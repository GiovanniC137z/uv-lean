import UV.AdvanceStableCartesian
import UV.AdvanceConeAngularBoundary

/-! The complete stable-half longitudinal coefficient, assembled at
one positive height from the checked normal limits on a fixed plane. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology

/-- The longitudinal numerator is the product of the two actual
covariant momentum components in the supplied unit directions. -/
def coneTensorTest (u v : ConeUnitDirection) (g : ℝ × Spatial → ℂ) (q : ℝ × Spatial) : ℂ :=
  coneLinearTest v g q * (coneCovector (WithLp.ofLp u.val) q : ℂ)

theorem cone_tensor_test_continuous (u v : ConeUnitDirection) {g : ℝ × Spatial → ℂ}
    (hg : Continuous g) : Continuous (coneTensorTest u v g) := by
  unfold coneTensorTest coneLinearTest
  exact (hg.mul (Complex.continuous_ofReal.comp (coneCovector (WithLp.ofLp v.val)).continuous)).mul
    (Complex.continuous_ofReal.comp (coneCovector (WithLp.ofLp u.val)).continuous)

theorem cone_tensor_test_compact (u v : ConeUnitDirection) {g : ℝ × Spatial → ℂ}
    (hs : HasCompactSupport g) : HasCompactSupport (coneTensorTest u v g) := by
  unfold coneTensorTest coneLinearTest
  exact hs.mul_right.mul_right

variable {E : Type*} [NormedAddCommGroup E]

def Plane.masslessStableLongitudinalPair (diamond : Plane E) (ε : Evolution) (h : Height)
    (a : ℝ) (u v : ConeUnitDirection) (g : ℝ × Spatial → ℂ) : ℂ :=
  ∫ q : ℝ × Spatial, coneTensorTest u v g q *
    (diamond.stableHalfCoefficient ε a (shellSquare q.1 q.2) h *
      (diamond.poleCoefficient ε h (shellSquare q.1 q.2)) ^ 2)


theorem Plane.massless_longitudinal_integrand_directed (diamond : Plane E) (ε : Evolution)
    (h : Height) (a : ℝ) (u v : ConeUnitDirection) (g : ℝ × Spatial → ℂ) (q : ℝ × Spatial) :
    let w := shellSquare q.1 q.2
    directed (coneTensorTest u v g q * (diamond.stableHalfCoefficient ε a w h *
      (diamond.poleCoefficient ε h w) ^ 2)) =
      directed (coneTensorTest u v g q) *
        (diamond.stableHalfNumerator ε h a w * (diamond.poleInverse ε h w) ^ 2) := by
  dsimp only
  rw [directed_mul, diamond.stable_square_coefficient_directed]

theorem Plane.massless_stable_longitudinal_pair_split (diamond : Plane E) (ε : Evolution)
    (h : Height) (a : ℝ) (u v : ConeUnitDirection) {g : ℝ × Spatial → ℂ}
    (hg : Continuous g) (hs : HasCompactSupport g) :
    diamond.masslessStableLongitudinalPair ε h a u v g =
      (∫ q : ℝ × Spatial, coneTensorTest u v g q *
        (diamond.poleCoefficient ε h (shellSquare q.1 q.2)) ^ 2) +
      diamond.stableTensorFractionalPair ε h a u v g -
      ((a : ℂ) ^ 2 / 2) * (∫ q : ℝ × Spatial, coneTensorTest u v g q *
        diamond.poleCoefficient ε h (shellSquare q.1 q.2)) +
      ∫ q : ℝ × Spatial, coneTensorTest u v g q *
        stableSquareResidual a (diamond.shiftedShellCoefficient ε h (shellSquare q.1 q.2)) := by
  let f := coneTensorTest u v g
  let w (q : ℝ × Spatial) := shellSquare q.1 q.2
  let Z (q : ℝ × Spatial) := diamond.shiftedShellCoefficient ε h (w q)
  let P (q : ℝ × Spatial) := diamond.poleCoefficient ε h (w q)
  let S (q : ℝ × Spatial) := diamond.stableShellRoot ε h (w q)
  let C := (a : ℂ) ^ 2 / 2
  let B (q : ℝ × Spatial) := -(a : ℂ) / (S q) ^ 3
  let D (q : ℝ × Spatial) := stableSquareResidual a (Z q)
  have hPc : Continuous P := (diamond.pole_coefficient_continuous ε h).comp shellSquare_continuous
  have hZc : Continuous Z := (Complex.continuous_ofReal.add continuous_const).comp shellSquare_continuous
  have hS₀ (q : ℝ × Spatial) : S q ≠ 0 := diamond.stable_shell_root_ne_zero ε h (w q)
  have hSc : Continuous S := by
    have hInv (x : ℝ) : HasDerivAt (fun y => (diamond.stableShellRoot ε h y)⁻¹)
        ((2 : ℂ)⁻¹ * ((diamond.stableShellRoot ε h x) ^ 3)⁻¹) x :=
      diamond.stable_shell_inverse_root_hasDerivAt ε h x
    have hC := ((continuous_iff_continuousAt.mpr fun x => (hInv x).continuousAt).comp
      shellSquare_continuous).inv₀ (fun q => inv_ne_zero (hS₀ q))
    simpa only [Function.comp_def, inv_inv] using hC
  have hB : Continuous B := continuous_const.div (hSc.pow 3) (fun q => pow_ne_zero _ (hS₀ q))
  have hD : Continuous D := by
    let X (q : ℝ × Spatial) := -(a : ℂ) * S q
    have hX : Continuous X := continuous_const.mul hSc
    change Continuous (fun q => (Complex.exp (X q) - 1 - X q - X q ^ 2 / 2) / Z q ^ 2)
    exact (((Complex.continuous_exp.comp hX).sub continuous_const).sub hX |>.sub
      ((hX.pow 2).div_const 2)).div (hZc.pow 2)
      (fun q => pow_ne_zero _ (diamond.massless_shifted_coefficient_nonzero ε h (w q)))
  have hf : Continuous f := cone_tensor_test_continuous u v hg
  have hfs : HasCompactSupport f := cone_tensor_test_compact u v hs
  have hi {K : ℝ × Spatial → ℂ} (hK : Continuous K) :
      Integrable (fun q => f q * K q) volume := (hf.mul hK).integrable_of_hasCompactSupport hfs.mul_right
  have h₂ := hi (hPc.pow 2)
  have hB' := hi hB
  have h₁ := (hi hPc).const_mul C
  have hD' := hi hD
  have hSum : Integrable (fun q => f q * (P q) ^ 2 + f q * B q) volume := h₂.add hB'
  have hSub : Integrable (fun q => f q * (P q) ^ 2 + f q * B q - C * (f q * P q)) volume :=
    hSum.sub h₁
  change diamond.masslessStableLongitudinalPair ε h a u v g =
    (∫ q, f q * (P q) ^ 2) + (∫ q, f q * B q) -
      C * (∫ q, f q * P q) + ∫ q, f q * D q
  rw [← integral_const_mul, ← integral_add h₂ hB', ← integral_sub hSum h₁,
    ← integral_add hSub hD']
  unfold Plane.masslessStableLongitudinalPair
  apply integral_congr_ae
  refine Eventually.of_forall fun q => ?_
  change f q * (diamond.stableHalfCoefficient ε a (w q) h * (P q) ^ 2) =
    f q * (P q) ^ 2 + f q * B q - C * (f q * P q) + f q * D q
  rw [diamond.stable_square_coefficient_split ε h a (w q)]
  dsimp only [P, B, C, D, Z, S]
  ring

/-- Boundary value of the complete longitudinal coefficient on compact
nonradial tests with the stated uniform normal Taylor bounds. -/
theorem Plane.massless_stable_longitudinal_limit (diamond : Plane E) (ε : Evolution)
    {a R M : ℝ} (ha : 0 ≤ a) (hR : 0 < R) (hM : 0 ≤ M)
    (u v : ConeUnitDirection) {g : ℝ × Spatial → ℂ}
    (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g)
    (hoff : ∀ q, R < coneEuclideanRadius q → coneTensorTest u v g q = 0)
    (d : ℝ → ℂ)
    (hSingle : ∀ r ∈ Ioc (0 : ℝ) R, ‖coneAngularAmplitude (coneTensorTest u v g) r 0‖ ≤ M ∧
      ∀ y ∈ Icc (-1 : ℝ) 1,
        ‖coneAngularAmplitude (coneTensorTest u v g) r y -
          coneAngularAmplitude (coneTensorTest u v g) r 0‖ ≤ M * |y|)
    (hDouble : ∀ r ∈ Ioc (0 : ℝ) R,
      ‖coneQuadraticAngularAmplitude (coneTensorTest u v g) r 0‖ ≤ M ∧ ‖d r‖ ≤ M ∧
      ∀ y ∈ Icc (-1 : ℝ) 1, ‖coneQuadraticAngularAmplitude (coneTensorTest u v g) r y -
        coneQuadraticAngularAmplitude (coneTensorTest u v g) r 0 - (y : ℂ) * d r‖ ≤ M * |y| ^ 2) :
    Tendsto (fun h : Height => diamond.masslessStableLongitudinalPair ε h a u v g)
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 (
        ((2 * Real.pi ^ 2 : ℝ) • ∫ r in Ioc (0 : ℝ) R, r •
          coneAngularSquareBoundary (diamond.eta ε)
            (coneQuadraticAngularAmplitude (coneTensorTest u v g) r) (d r)) +
        (a : ℂ) * (∫ q : ℝ × Spatial,
          fderiv ℝ (coneLinearTest v g) q (WithLp.ofLp u.val) *
            (stableShellBoundaryRoot (diamond.eta ε) (shellSquare q.1 q.2))⁻¹) -
        ((a : ℂ) ^ 2 / 2) * ((2 * Real.pi ^ 2 : ℝ) • ∫ r in Ioc (0 : ℝ) R, r •
          coneAngularSingleBoundary (diamond.eta ε) (coneAngularAmplitude (coneTensorTest u v g) r)) +
        ∫ q : ℝ × Spatial,
          coneTensorTest u v g q * stableSquareBoundaryResidual (diamond.eta ε) a
            (shellSquare q.1 q.2))) := by
  have hf := cone_tensor_test_continuous u v hg.continuous
  have hfs := cone_tensor_test_compact u v hs
  have h₁ := diamond.cone_nonradial_single_limit ε hf hfs hR hoff hM hSingle
  have h₂ := diamond.cone_nonradial_quadratic_limit ε hf hfs hR hoff d hM hDouble
  have hB := diamond.stable_tensor_fractional_pair_limit ε a u v hg hs
  have hD := (diamond.stable_square_residual_full_momentum ε ha hf hfs).2
  refine (((h₂.add hB).sub (h₁.const_mul ((a : ℂ) ^ 2 / 2))).add hD).congr fun h => ?_
  exact (diamond.massless_stable_longitudinal_pair_split ε h a u v hg.continuous hs).symm

end UV.SectorPlane
