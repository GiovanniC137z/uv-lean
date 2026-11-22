import UV.VerifyRunningPrimitive

/-! The running-unit fractional tensor term on the fixed real
four-momentum chart, with its genuine axial contact. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E]

def Plane.stableInverseRootMomentum (diamond : Plane E) (ε : Evolution)
    (h : Height) (q : ℝ × Spatial) : ℂ :=
  (diamond.stableShellRoot ε h (shellSquare q.1 q.2))⁻¹

theorem Plane.stable_inverse_root_momentum_contDiff (diamond : Plane E)
    (ε : Evolution) (h : Height) :
    ContDiff ℝ 1 (diamond.stableInverseRootMomentum ε h) := by
  let P (w : ℝ) := (diamond.stableShellRoot ε h w)⁻¹
  have hd (w : ℝ) : HasDerivAt P ((2 : ℂ)⁻¹ *
      ((diamond.stableShellRoot ε h w) ^ 3)⁻¹) w :=
    diamond.stable_shell_inverse_root_hasDerivAt ε h w
  have hP : ContDiff ℝ 1 P := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun w => (hd w).differentiableAt, ?_⟩
    have hEq : deriv P = fun w => (2 : ℂ)⁻¹ * P w ^ 3 := by
      funext w
      simpa only [P, inv_pow] using (hd w).deriv
    rw [hEq]
    exact continuous_const.mul
      ((continuous_iff_continuousAt.mpr fun w => (hd w).continuousAt).pow 3)
  have hShell : ContDiff ℝ 1 (fun q : ℝ × Spatial => shellSquare q.1 q.2) := by
    unfold shellSquare
    have hx : ContDiff ℝ 1 (Prod.fst : ℝ × Spatial → ℝ) := contDiff_fst
    have hp : ContDiff ℝ 1 (Prod.snd : ℝ × Spatial → Spatial) := contDiff_snd
    exact (hx.pow 2).sub ((contDiff_norm_sq ℝ).comp hp)
  exact hP.comp hShell

def Plane.runningTensorFractionalPair (diamond : Plane E) (ε : Evolution) (h : Height)
    (a : ℝ) (u v : ConeUnitDirection) (g : ℝ × Spatial → ℂ) : ℂ :=
  ∫ q : ℝ × Spatial, runningAxialTest (coneLinearTest v g) q *
    (coneCovector (WithLp.ofLp u.val) q : ℂ) *
      (-(a : ℂ) / (diamond.stableShellRoot ε h (shellSquare q.1 q.2)) ^ 3)

/-- The jump of the running sign contributes the axial trace at each
positive height, before any boundary limit is taken. -/
theorem Plane.running_tensor_fractional_pair_parts (diamond : Plane E) (ε : Evolution)
    (h : Height) (a : ℝ) (u v : ConeUnitDirection) {g : ℝ × Spatial → ℂ}
    (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g) :
    let d := WithLp.ofLp u.val
    let T := coneLinearTest v g
    let P := diamond.stableInverseRootMomentum ε h
    diamond.runningTensorFractionalPair ε h a u v g =
      (a : ℂ) * ((∫ q : ℝ × Spatial, runningAxialTest (fun q => fderiv ℝ T q d) q * P q) +
        (2 : ℂ) * (d.1 : ℂ) * ∫ p : Spatial, T (0, p) * P (0, p)) := by
  dsimp only
  let d := WithLp.ofLp u.val
  let T := coneLinearTest v g
  let P := diamond.stableInverseRootMomentum ε h
  have ht : ContDiff ℝ 1 T := cone_linear_test_contDiff v hg
  have hts : HasCompactSupport T := cone_linear_test_compact v hs
  have hp : ContDiff ℝ 1 P := diamond.stable_inverse_root_momentum_contDiff ε h
  let A (q : ℝ × Spatial) := runningAxialTest (fun q => fderiv ℝ T q d) q * P q
  let B (q : ℝ × Spatial) := runningAxialTest T q * fderiv ℝ P q d
  have htc : Continuous (fun q => fderiv ℝ T q d) :=
    (ht.continuous_fderiv_apply le_rfl).comp (continuous_id.prodMk continuous_const)
  have hpc : Continuous (fun q => fderiv ℝ P q d) :=
    (hp.continuous_fderiv_apply le_rfl).comp (continuous_id.prodMk continuous_const)
  have hAi : Integrable A := by
    have hi : Integrable (fun q => fderiv ℝ T q d * P q) :=
      (htc.mul hp.continuous).integrable_of_hasCompactSupport (hts.fderiv_apply ℝ d).mul_right
    simpa only [A, runningAxialTest, mul_assoc] using
      integrable_runningAxialSign_mul measurable_fst hi
  have hBi : Integrable B := by
    have hi : Integrable (fun q => T q * fderiv ℝ P q d) :=
      (ht.continuous.mul hpc).integrable_of_hasCompactSupport hts.mul_right
    simpa only [B, runningAxialTest, mul_assoc] using
      integrable_runningAxialSign_mul measurable_fst hi
  have hIBP := integral_axialSign_directional_derivative
    (f := T * P) (ht.mul hp) hts.mul_right d
  have hDer (q : ℝ × Spatial) :
      (axialSign q.1 : ℂ) * fderiv ℝ (T * P) q d = A q + B q := by
    rw [fderiv_mul (ht.differentiable (by norm_num) q) (hp.differentiable (by norm_num) q)]
    simp only [A, B, runningAxialTest, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  simp_rw [hDer] at hIBP
  rw [integral_add hAi hBi] at hIBP
  change diamond.runningTensorFractionalPair ε h a u v g =
    (a : ℂ) * ((∫ q, A q) + (2 : ℂ) * (d.1 : ℂ) * ∫ p : Spatial, T (0, p) * P (0, p))
  calc
    _ = -(a : ℂ) * ∫ q, B q := by
      unfold Plane.runningTensorFractionalPair
      rw [← integral_const_mul]
      apply integral_congr_ae
      refine Eventually.of_forall fun q => ?_
      dsimp only [B]
      rw [show fderiv ℝ P q d = (coneCovector d q : ℂ) *
          ((diamond.stableShellRoot ε h (shellSquare q.1 q.2)) ^ 3)⁻¹ from
        diamond.stable_inverse_root_directional_derivative ε h q d]
      simp only [T, d, div_eq_mul_inv]
      ring
    _ = _ := by
      linear_combination -(a : ℂ) * hIBP

theorem Plane.running_tensor_fractional_pair_limit (diamond : Plane E) (ε : Evolution)
    (a : ℝ) (u v : ConeUnitDirection) {g : ℝ × Spatial → ℂ}
    (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g) :
    let d := WithLp.ofLp u.val
    let T := coneLinearTest v g
    Tendsto (fun h : Height => diamond.runningTensorFractionalPair ε h a u v g)
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 ((a : ℂ) * ((∫ q : ℝ × Spatial,
        runningAxialTest (fun q => fderiv ℝ T q d) q *
          (stableShellBoundaryRoot (diamond.eta ε) (shellSquare q.1 q.2))⁻¹) +
        (2 : ℂ) * (d.1 : ℂ) * ∫ p : Spatial, T (0, p) * (‖p‖ : ℂ)⁻¹))) := by
  dsimp only
  let d := WithLp.ofLp u.val
  let T := coneLinearTest v g
  have ht : ContDiff ℝ 1 T := cone_linear_test_contDiff v hg
  have hts : HasCompactSupport T := cone_linear_test_compact v hs
  have htc : Continuous (fun q => fderiv ℝ T q d) :=
    (ht.continuous_fderiv_apply le_rfl).comp (continuous_id.prodMk continuous_const)
  have hV := diamond.running_inverse_root_full_momentum ε htc (hts.fderiv_apply ℝ d)
  have hCut : Continuous (fun p : Spatial => T (0, p)) :=
    ht.continuous.comp (continuous_const.prodMk continuous_id)
  have hTrace := diamond.stable_inverse_root_axial_trace_limit ε hCut (running_spatial_slice_compact hts 0)
  refine (((hV.add (hTrace.const_mul ((2 : ℂ) * (d.1 : ℂ)))).const_mul (a : ℂ))).congr fun h => ?_
  exact (diamond.running_tensor_fractional_pair_parts ε h a u v hg hs).symm

end UV.SectorPlane
