import UV.AdvanceStableSquareResidual
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Cartesian integration by parts for the branch singularity multiplied
by the literal longitudinal quadratic numerator. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology RealInnerProductSpace

abbrev ConeUnitDirection := UnitVector (WithLp 2 (ℝ × Spatial))

/-- The axial unit in the intrinsic Euclidean norm used for polar coordinates. -/
def coneAxialUnit : ConeUnitDirection :=
  ⟨WithLp.toLp 2 ((1 : ℝ), (0 : Spatial)), by
    rw [WithLp.prod_norm_eq_of_L2]
    norm_num⟩

/-- The Euclidean lift of a norm-one spatial axis into the fixed real chart. -/
def coneSpatialUnit (e : UnitVector Spatial) : ConeUnitDirection :=
  ⟨WithLp.toLp 2 ((0 : ℝ), e.val), by
    rw [WithLp.prod_norm_eq_of_L2]
    simp [e.property]⟩

/-- Covariant momentum component on the intrinsic Lorentzian chart. -/
def coneCovector (v : ℝ × Spatial) : (ℝ × Spatial) →L[ℝ] ℝ :=
  v.1 • ContinuousLinearMap.fst ℝ ℝ Spatial -
    (innerSL ℝ v.2).comp (ContinuousLinearMap.snd ℝ ℝ Spatial)

theorem coneCovector_apply (v q : ℝ × Spatial) :
    coneCovector v q = v.1 * q.1 - ⟪v.2, q.2⟫ := by
  simp [coneCovector]

theorem coneCovector_axial (q : ℝ × Spatial) :
    coneCovector (WithLp.ofLp coneAxialUnit.val) q = q.1 := by
  simp [coneCovector_apply, coneAxialUnit]

theorem coneCovector_spatial (e : UnitVector Spatial) (q : ℝ × Spatial) :
    coneCovector (WithLp.ofLp (coneSpatialUnit e).val) q = -⟪e.val, q.2⟫ := by
  simp [coneCovector_apply, coneSpatialUnit]

theorem shell_square_hasFDerivAt (q : ℝ × Spatial) :
    HasFDerivAt (fun q : ℝ × Spatial => shellSquare q.1 q.2) (2 • coneCovector q) q := by
  have ht := ((ContinuousLinearMap.fst ℝ ℝ Spatial).hasFDerivAt (x := q)).pow 2
  have hp := (hasStrictFDerivAt_norm_sq q.2).hasFDerivAt.comp q
    ((ContinuousLinearMap.snd ℝ ℝ Spatial).hasFDerivAt (x := q))
  have hd := ht.sub hp
  convert hd using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [coneCovector_apply, two_mul]
  ring

variable {E : Type*} [NormedAddCommGroup E]

/-- Directional derivative with the exact signed Lorentzian covector.
This identity is valid at the cone tip for every positive height. -/
theorem Plane.stable_inverse_root_directional_derivative (diamond : Plane E) (ε : Evolution)
    (h : Height) (q v : ℝ × Spatial) :
    fderiv ℝ (fun q : ℝ × Spatial =>
      (diamond.stableShellRoot ε h (shellSquare q.1 q.2))⁻¹) q v =
        (coneCovector v q : ℂ) *
          ((diamond.stableShellRoot ε h (shellSquare q.1 q.2)) ^ 3)⁻¹ := by
  have hRoot := diamond.stable_shell_inverse_root_hasDerivAt ε h (shellSquare q.1 q.2)
  have hd := hRoot.hasFDerivAt.comp q (shell_square_hasFDerivAt q)
  change fderiv ℝ ((fun u => (diamond.stableShellRoot ε h u)⁻¹) ∘
    (fun q : ℝ × Spatial => shellSquare q.1 q.2)) q v = _
  rw [hd.fderiv]
  simp [coneCovector_apply, real_inner_comm q.2 v.2, two_nsmul, Complex.real_smul]
  ring

theorem Plane.stable_inverse_root_full_momentum (diamond : Plane E) (ε : Evolution)
    {g : ℝ × Spatial → ℂ} (hg : Continuous g) (hs : HasCompactSupport g) :
    Integrable (fun q : ℝ × Spatial => g q *
      (stableShellBoundaryRoot (diamond.eta ε) (shellSquare q.1 q.2))⁻¹) ∧
    Tendsto (fun h : Height => ∫ q : ℝ × Spatial, g q *
      (diamond.stableShellRoot ε h (shellSquare q.1 q.2))⁻¹)
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 (∫ q : ℝ × Spatial, g q *
        (stableShellBoundaryRoot (diamond.eta ε) (shellSquare q.1 q.2))⁻¹)) := by
  refine cone_test_limit_of_inverse_root_bound
    (K := fun h w => (diamond.stableShellRoot ε h w)⁻¹)
    (L := fun w => (stableShellBoundaryRoot (diamond.eta ε) w)⁻¹)
    (C := 1) ?_ ?_ ?_ ?_ ?_ hg hs
  · intro h
    exact (continuous_iff_continuousAt.mpr fun w =>
      (diamond.stable_shell_inverse_root_hasDerivAt ε h w).continuousAt).measurable
  · unfold stableShellBoundaryRoot
    fun_prop
  · intro h w hw
    rw [one_mul]
    exact diamond.stable_shell_inverse_root_norm_le ε h hw
  · intro w _
    rw [norm_inv, stable_shell_boundary_root_norm _ (diamond.eta_sq ε), one_mul, inverseRootAbs]
  · intro w hw
    exact diamond.stable_shell_inverse_root_tendsto ε hw

/-- The smooth test after its second covariant momentum component has
been included. -/
def coneLinearTest (v : ConeUnitDirection) (g : ℝ × Spatial → ℂ) (q : ℝ × Spatial) : ℂ :=
  g q * (coneCovector (WithLp.ofLp v.val) q : ℂ)

theorem cone_linear_test_contDiff (v : ConeUnitDirection) {g : ℝ × Spatial → ℂ}
    (hg : ContDiff ℝ 1 g) : ContDiff ℝ 1 (coneLinearTest v g) :=
  hg.mul (Complex.ofRealCLM.contDiff.comp (coneCovector (WithLp.ofLp v.val)).contDiff)

theorem cone_linear_test_compact (v : ConeUnitDirection) {g : ℝ × Spatial → ℂ}
    (hs : HasCompactSupport g) : HasCompactSupport (coneLinearTest v g) :=
  hs.mul_right

/-- The actual longitudinal fractional term tested on all four momenta.
The two axes carry norm-one witnesses in the intrinsic polar norm. -/
def Plane.stableTensorFractionalPair (diamond : Plane E) (ε : Evolution) (h : Height)
    (a : ℝ) (u v : ConeUnitDirection) (g : ℝ × Spatial → ℂ) : ℂ :=
  ∫ q : ℝ × Spatial, coneLinearTest v g q * (coneCovector (WithLp.ofLp u.val) q : ℂ) *
    (-(a : ℂ) / (diamond.stableShellRoot ε h (shellSquare q.1 q.2)) ^ 3)

theorem Plane.stable_tensor_fractional_pair_parts (diamond : Plane E) (ε : Evolution)
    (h : Height) (a : ℝ) (u v : ConeUnitDirection)
    {g : ℝ × Spatial → ℂ} (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g) :
    diamond.stableTensorFractionalPair ε h a u v g =
      (a : ℂ) * ∫ q : ℝ × Spatial, fderiv ℝ (coneLinearTest v g) q (WithLp.ofLp u.val) *
        (diamond.stableShellRoot ε h (shellSquare q.1 q.2))⁻¹ := by
  let d := WithLp.ofLp u.val
  let T := coneLinearTest v g
  let P (q : ℝ × Spatial) := (diamond.stableShellRoot ε h (shellSquare q.1 q.2))⁻¹
  have hT := cone_linear_test_contDiff v hg
  have hTs := cone_linear_test_compact v hs
  have hT' : Continuous (fun q => fderiv ℝ T q d) :=
    (hT.continuous_fderiv_apply le_rfl).comp (continuous_id.prodMk continuous_const)
  have hPs (q : ℝ × Spatial) : DifferentiableAt ℝ P q := by
    have hRoot := diamond.stable_shell_inverse_root_hasDerivAt ε h (shellSquare q.1 q.2)
    exact (hRoot.hasFDerivAt.comp q (shell_square_hasFDerivAt q)).differentiableAt
  have hPc : Continuous P := continuous_iff_continuousAt.mpr fun q => (hPs q).continuousAt
  have hP' (q : ℝ × Spatial) : fderiv ℝ P q d = (coneCovector d q : ℂ) * P q ^ 3 := by
    rw [show fderiv ℝ P q d =
      (coneCovector d q : ℂ) * ((diamond.stableShellRoot ε h (shellSquare q.1 q.2)) ^ 3)⁻¹
      from diamond.stable_inverse_root_directional_derivative ε h q d]
    simp only [P, inv_pow]
  have hP'c : Continuous (fun q => fderiv ℝ P q d) := by
    simp_rw [hP']
    exact (Complex.continuous_ofReal.comp (coneCovector d).continuous).mul (hPc.pow 3)
  letI : (volume : Measure (ℝ × Spatial)).IsAddHaarMeasure := by
    change ((volume : Measure ℝ).prod (volume : Measure Spatial)).IsAddHaarMeasure
    infer_instance
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    ((hT'.mul hPc).integrable_of_hasCompactSupport ((hTs.fderiv_apply ℝ d).mul_right))
    ((hT.continuous.mul hP'c).integrable_of_hasCompactSupport hTs.mul_right)
    ((hT.continuous.mul hPc).integrable_of_hasCompactSupport hTs.mul_right)
    (hT.differentiable (by norm_num)) hPs
  calc
    _ = (-(a : ℂ)) * ∫ q : ℝ × Spatial, T q * fderiv ℝ P q d := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      refine Eventually.of_forall fun q => ?_
      dsimp only
      rw [hP']
      simp only [T, d, P, inv_pow, div_eq_mul_inv]
      ring
    _ = _ := by rw [hIBP]; ring

/-- The longitudinal fractional contribution has a boundary limit on
arbitrary compact C¹ tests in the actual Cartesian four-momentum measure. -/
theorem Plane.stable_tensor_fractional_pair_limit (diamond : Plane E) (ε : Evolution)
    (a : ℝ) (u v : ConeUnitDirection) {g : ℝ × Spatial → ℂ}
    (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g) :
    Tendsto (fun h : Height => diamond.stableTensorFractionalPair ε h a u v g)
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 ((a : ℂ) * ∫ q : ℝ × Spatial, fderiv ℝ (coneLinearTest v g) q (WithLp.ofLp u.val) *
        (stableShellBoundaryRoot (diamond.eta ε) (shellSquare q.1 q.2))⁻¹)) := by
  have hT := cone_linear_test_contDiff v hg
  have hTs := cone_linear_test_compact v hs
  apply ((diamond.stable_inverse_root_full_momentum ε
    ((hT.continuous_fderiv_apply le_rfl).comp (continuous_id.prodMk continuous_const))
    (hTs.fderiv_apply ℝ _)).2.const_mul (a : ℂ)).congr
  intro h
  exact (diamond.stable_tensor_fractional_pair_parts ε h a u v hg hs).symm

end UV.SectorPlane
