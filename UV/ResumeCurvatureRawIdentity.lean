import UV.ResumeCurvatureDistributions
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! The regularization cancels exactly on each actual real lattice mode.
The order-six derivative is carried on the Schwartz test without changing
the Gaussian mode coordinate or the fixed geometric convention. -/

noncomputable section

open MeasureTheory Real Filter
open scoped BigOperators Topology SchwartzMap

namespace UV.ResumeCurvatureRawIdentity

open UV.ResumeCurvatureSmooth UV.ResumeCurvatureRawBounds UV.ResumeCurvatureDistributions
open UV.ExtendCurvaturePotential UV.NextCurvatureLaw UV.FurtherCurvatureShell
open UV.RevisionCurvatureDeterminant (latticeFrequency)

private theorem bounded_mul_test_integrable (f : Cover → ℝ) (hf : Continuous f)
    (A : ℝ) (hb : ∀ x, ‖f x‖ ≤ A) (φ : SchwartzTest) :
    Integrable (fun x => f x * φ x) volume := by
  refine (φ.integrable.norm.const_mul A).mono'
    (hf.aestronglyMeasurable.mul φ.continuous.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)

private theorem integrate_oscillator_second (L : Cover →L[ℝ] ℝ) (v : Cover)
    (u du : ℝ → ℝ) (hu : ∀ t, HasDerivAt u (du t) t)
    (hdu : ∀ t, HasDerivAt du (-u t) t)
    (huB : ∀ t, ‖u t‖ ≤ 1) (hduB : ∀ t, ‖du t‖ ≤ 1) (φ : SchwartzTest) :
    (∫ x, u (L x) * (SchwartzMap.pderivCLM ℝ v (SchwartzMap.pderivCLM ℝ v φ)) x) =
      -(L v)^2 * ∫ x, u (L x) * φ x := by
  let F (x : Cover) := u (L x)
  let d := L v
  let G (x : Cover) := d * du (L x)
  let D : SchwartzTest →L[ℝ] SchwartzTest := SchwartzMap.pderivCLM ℝ v
  have hF (x : Cover) : HasFDerivAt F ((du (L x)) • L) x :=
    (hu (L x)).comp_hasFDerivAt x L.hasFDerivAt
  have hG (x : Cover) : HasFDerivAt G ((d * (-u (L x))) • L) x := by
    have hh : HasFDerivAt (fun y : Cover => du (L y)) ((-u (L x)) • L) x :=
      (hdu (L x)).comp_hasFDerivAt x L.hasFDerivAt
    simpa only [smul_smul] using hh.const_smul d
  have hmF (x : Cover) : (fderiv ℝ F x) v = G x := by
    rw [(hF x).fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_comm _ _
  have hmG (x : Cover) : (fderiv ℝ G x) v = -d^2 * F x := by
    rw [(hG x).fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]
    change d * (-F x) * d = -d^2 * F x
    ring
  have hdF : Differentiable ℝ F := fun x => (hF x).differentiableAt
  have hdG : Differentiable ℝ G := fun x => (hG x).differentiableAt
  have hFi (ψ : SchwartzTest) : Integrable (fun x => F x * ψ x) volume :=
    bounded_mul_test_integrable F hdF.continuous 1 (fun x => huB _) ψ
  have hGi (ψ : SchwartzTest) : Integrable (fun x => G x * ψ x) volume :=
    bounded_mul_test_integrable G hdG.continuous ‖d‖ (fun x => by
      dsimp [G]; rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hduB _)) ψ
  have ibp₁ : (∫ x, F x * D (D φ) x) = -∫ x, G x * D φ x := by
    have hx : Integrable (fun x => fderiv ℝ F x v * D φ x) volume := by
      simpa only [hmF] using hGi (D φ)
    have hy : Integrable (fun x => F x * fderiv ℝ (D φ) x v) volume := hFi (D (D φ))
    simpa only [hmF] using
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hx hy (hFi (D φ))
        hdF (D φ).differentiable
  have ibp₂ : (∫ x, G x * D φ x) = d^2 * ∫ x, F x * φ x := by
    have hx : Integrable (fun x => fderiv ℝ G x v * φ x) volume := by
      simp_rw [hmG, mul_assoc]
      exact (hFi φ).const_mul _
    have hy : Integrable (fun x => G x * fderiv ℝ φ x v) volume := hGi (D φ)
    have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hx hy (hGi φ) hdG φ.differentiable
    simpa only [hmG, mul_assoc, neg_mul, integral_neg, neg_neg, integral_const_mul] using he
  change (∫ x, F x * D (D φ) x) = -d^2 * ∫ x, F x * φ x
  rw [ibp₁, ibp₂, neg_mul]

private theorem phaseLinear_unit (k : TorusMode) (j : Fin 4) :
    phaseLinear k (unitCoordinate j) = (k j : ℝ) := by
  rw [phaseLinear_apply]
  simp only [unitCoordinate, EuclideanSpace.single_apply]
  classical
  simp [mul_ite]

def modeTestPair (k : MeanZeroMode) (φ : SchwartzTest) : ℝ :=
  testPeriodicPair φ (realTorusMode k)

private theorem modeTestPair_integral (k : MeanZeroMode) (φ : SchwartzTest) :
    modeTestPair k φ = ∫ x, modeOnCover k x * φ x := by
  change (∫ x, realTorusMode k (coverPoint x) * φ x) = _
  simp_rw [realTorusMode_cover_eq]

theorem mode_secondCoordinate_pair (k : MeanZeroMode) (j : Fin 4) (φ : SchwartzTest) :
    modeTestPair k (secondCoordinate j φ) = -((k.1 j : ℝ)^2) * modeTestPair k φ := by
  simp only [modeTestPair_integral]
  unfold modeOnCover
  split
  · have hd (t : ℝ) : HasDerivAt (fun x => -sin x) (-cos t) t := (hasDerivAt_sin t).neg
    have he := integrate_oscillator_second (phaseLinear k) (unitCoordinate j)
      Real.cos (fun t => -sin t) hasDerivAt_cos hd
      (fun t => Real.abs_cos_le_one t) (fun t => by simpa using Real.abs_sin_le_one t) φ
    rw [phaseLinear_unit] at he
    simp only [smul_eq_mul, mul_assoc, integral_const_mul] at *
    exact congrArg (fun z : ℝ => sqrt 2 * z) he |>.trans (by ring)
  · have he := integrate_oscillator_second (phaseLinear (-k.1)) (unitCoordinate j)
      Real.sin Real.cos hasDerivAt_sin hasDerivAt_cos
      (fun t => Real.abs_sin_le_one t) (fun t => Real.abs_cos_le_one t) φ
    rw [phaseLinear_unit] at he
    simp only [Pi.neg_apply, Int.cast_neg, neg_sq] at he
    simp only [smul_eq_mul, mul_assoc, integral_const_mul] at *
    exact congrArg (fun z : ℝ => sqrt 2 * z) he |>.trans (by ring)

/-- Exact cancellation of the regularization multiplier on each mode. -/
theorem mode_elliptic_pair (k : MeanZeroMode) (φ : SchwartzTest) :
    modeTestPair k (ellipticTestCube φ) =
      (1 + latticeFrequency k ^ 2)^3 * modeTestPair k φ := by
  have h1 (ψ : SchwartzTest) :
      modeTestPair k (oneMinusLaplacian ψ) =
        (1 + latticeFrequency k ^ 2) * modeTestPair k ψ := by
    change coverDistribution (realTorusMode k) (oneMinusLaplacian ψ) = _
    unfold oneMinusLaplacian
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.sum_apply, map_sub, map_sum]
    change modeTestPair k ψ - ∑ j : Fin 4, modeTestPair k (secondCoordinate j ψ) = _
    simp_rw [mode_secondCoordinate_pair, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add,
      ← Finset.sum_mul]
    rw [latticeFrequency, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    ring
  rw [ellipticTestCube]
  simp only [ContinuousLinearMap.comp_apply, h1]
  ring

/-- The finite spherical distribution represents precisely the original
raw Gaussian Fourier coefficients after testing. -/
theorem cutoffRawDistribution_eq_mode_pair_sum {n : ℕ} (Λ ℓ : ℝ) (X : ModeSlot n → ℝ)
    (a : Fin 2) (c : Fin n) (φ : SchwartzTest) :
    cutoffRawDistribution Λ ℓ X a c φ =
      ∑ k ∈ retainedModes Λ, depthRescale ℓ X (k,(a,c)) * modeTestPair k φ := by
  change testPeriodicPair (ellipticTestCube φ) (cutoffRawPotential Λ ℓ X a c) = _
  unfold cutoffRawPotential rawPotentialTerm
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  change rawRegularization k * depthRescale ℓ X (k,(a,c)) *
    modeTestPair k (ellipticTestCube φ) = _
  rw [mode_elliptic_pair, rawRegularization]
  have h : (1 + latticeFrequency k ^ 2)^3 ≠ 0 := by positivity
  field_simp

private theorem mode_multiplier_cancel (k : MeanZeroMode) (r : ℝ) (φ : SchwartzTest) :
    rawRegularization k * r * modeTestPair k (ellipticTestCube φ) = r * modeTestPair k φ := by
  rw [mode_elliptic_pair, rawRegularization]
  have h : (1 + latticeFrequency k ^ 2)^3 ≠ 0 := by positivity
  field_simp

/-- The unrestricted distribution pairs with precisely the unregularized
Gaussian Fourier coefficients on the same probability-one set at all
depths. The test series converges absolutely. -/
theorem ae_fullRawDistribution_eq_mode_pair_tsum (n : ℕ) :
    ∀ᵐ X ∂commonGaussian n, ∀ (ℓ : ℝ) (a : Fin 2) (c : Fin n) (φ : SchwartzTest),
      Summable (fun k : MeanZeroMode => |depthRescale ℓ X (k,(a,c)) * modeTestPair k φ|) ∧
      fullRawDistribution ℓ X a c φ =
        ∑' k, depthRescale ℓ X (k,(a,c)) * modeTestPair k φ := by
  filter_upwards [ae_regularized_coordinates_summable n] with X hX
  intro ℓ a c φ
  let i : MeanZeroMode → ModeSlot n := fun k => (k,(a,c))
  have hi : Function.Injective i := fun _ _ hh => congrArg (fun j : ModeSlot n => j.1) hh
  have hs : Summable (fun k : MeanZeroMode => rawRegularization k * |depthRescale ℓ X (k,(a,c))|) := by
    simpa only [Function.comp_def, i] using (hX ℓ).comp_injective hi
  let v := testPeriodicPair (ellipticTestCube φ)
  have hnorm (k : MeanZeroMode) : ‖rawPotentialTerm ℓ X a c k‖ ≤
      sqrt 2 * (rawRegularization k * |depthRescale ℓ X (k,(a,c))|) := by
    unfold rawPotentialTerm
    rw [norm_smul, norm_mul, Real.norm_of_nonneg (rawRegularization_nonneg k), Real.norm_eq_abs,
      mul_comm (sqrt 2)]
    exact mul_le_mul_of_nonneg_left (realTorusMode_norm_bound k)
      (mul_nonneg (rawRegularization_nonneg k) (abs_nonneg _))
  have hs' : Summable (fun k : MeanZeroMode => ‖rawPotentialTerm ℓ X a c k‖) :=
    (hs.mul_left (sqrt 2)).of_nonneg_of_le (fun _ => norm_nonneg _) hnorm
  have hv (k : MeanZeroMode) :
      v (rawPotentialTerm ℓ X a c k) = depthRescale ℓ X (k,(a,c)) * modeTestPair k φ := by
    unfold v rawPotentialTerm
    rw [map_smul, smul_eq_mul]
    exact mode_multiplier_cancel k _ _
  refine ⟨?_, ?_⟩
  · apply (hs'.mul_left ‖v‖).of_nonneg_of_le (fun _ => abs_nonneg _)
    intro k
    rw [← hv, ← Real.norm_eq_abs]
    exact v.le_opNorm _
  · change v (∑' k, rawPotentialTerm ℓ X a c k) = _
    rw [v.map_tsum hs'.of_norm]
    simp_rw [hv]

end UV.ResumeCurvatureRawIdentity
