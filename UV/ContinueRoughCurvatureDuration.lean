import UV.ContinueRoughCurvatureCoordinate

/-! Exact Tonelli transfer from independent positive durations to the
absolute angular Green word, including infinite sums of mode paths. -/

noncomputable section
open MeasureTheory Real Filter Set
open scoped ENNReal BigOperators
namespace UV.RoughCurvature

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def roughCurvatureProperCost {n : ℕ} (b : Fin (n+1) → ℝ → AngularProfile)
    (K : ℤ → ℝ → ℝ → ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ z : Fin (n+1) → ℝ,
    ∑' k : Fin (n+1) → ℤ,
      ∫⁻ u : Fin (n+1) → ℝ, ∏ i,
        ENNReal.ofReal (collarVertexWeight (z i) * ‖fourierCoeff (b i (z i)) (k i - k (i+1))‖) *
          K (k (i+1)) (z i) (z (i+1)) (u i)
        ∂Measure.pi (fun _ : Fin (n+1) => collarPositiveMeasure)
    ∂Measure.pi (fun _ : Fin (n+1) => collarPositiveMeasure)

/-- The endpoint kernel can be replaced by its Green integral independently
on every edge, without imposing a common duration or bounding the angles. -/
theorem rough_curvature_proper_eq_green {n : ℕ} (b : Fin (n+1) → ℝ → AngularProfile)
    (K : ℤ → ℝ → ℝ → ℝ → ℝ≥0∞)
    (hK : ∀ j z w, Measurable (K j z w))
    (hG : ∀ j z w, 0 < z → 0 < w →
      (∫⁻ u, K j z w u ∂collarPositiveMeasure) = ENNReal.ofReal (collarModeGreen j z w)) :
    roughCurvatureProperCost b K = roughCurvatureCost b := by
  unfold roughCurvatureProperCost roughCurvatureCost
  apply lintegral_congr_ae
  have hp : ∀ᵐ z : Fin (n+1) → ℝ ∂Measure.pi (fun _ => collarPositiveMeasure), ∀ i, 0 < z i := by
    apply ae_all_iff.mpr
    intro i
    exact Measure.tendsto_eval_ae_ae (μ := fun _ : Fin (n+1) => collarPositiveMeasure) (i := i)
      (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [hp] with z hz
  apply tsum_congr
  intro k
  let u (i : Fin (n+1)) := collarVertexWeight (z i) * ‖fourierCoeff (b i (z i)) (k i - k (i+1))‖
  let L (i : Fin (n+1)) := K (k (i+1)) (z i) (z (i+1))
  have hL (i : Fin (n+1)) : Measurable (fun t => ENNReal.ofReal (u i) * L i t) :=
    measurable_const.mul (hK _ _ _)
  rw [network_lintegral_fintype_prod (fun _ : Fin (n+1) => collarPositiveMeasure)
    (fun i t => ENNReal.ofReal (u i) * L i t) hL]
  have h (i : Fin (n+1)) :
      (∫⁻ t, ENNReal.ofReal (u i) * L i t ∂collarPositiveMeasure) =
        ENNReal.ofReal (u i * collarModeGreen (k (i+1)) (z i) (z (i+1))) := by
    rw [lintegral_const_mul _ (show Measurable (L i) from hK _ _ _)]
    change ENNReal.ofReal (u i) * (∫⁻ t, K _ _ _ t ∂collarPositiveMeasure) = _
    rw [hG _ _ _ (hz _) (hz _)]
    have hU : 0 ≤ u i := by
      unfold u collarVertexWeight
      exact mul_nonneg (rpow_nonneg (by linarith [hz i]) _) (norm_nonneg _)
    exact (ENNReal.ofReal_mul hU).symm
  simp_rw [h]
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · rfl
  · intro i _
    refine mul_nonneg ?_ (collarModeGreen_nonnegative (k (i+1)) (hz i).le (hz (i+1)).le)
    unfold u collarVertexWeight
    exact mul_nonneg (rpow_nonneg (by linarith [hz i]) _) (norm_nonneg _)

theorem rough_curvature_proper_bound {n : ℕ} (b : Fin (n+2) → ℝ → AngularProfile)
    (K : ℤ → ℝ → ℝ → ℝ → ℝ≥0∞)
    (hK : ∀ j z w, Measurable (K j z w))
    (hG : ∀ j z w, 0 < z → 0 < w →
      (∫⁻ u, K j z w u ∂collarPositiveMeasure) = ENNReal.ofReal (collarModeGreen j z w))
    (M : Fin (n+2) → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hb : ∀ i, ∀ᵐ z ∂collarPositiveMeasure, fourierCoeff (b i z) 0 = 0 ∧ ‖b i z‖ ≤ M i) :
    roughCurvatureProperCost b K ≤
      ENNReal.ofReal (((2/3)*sqrt (1+Real.pi^2/12))^(n+2) * ∏ i, M i) := by
  rw [rough_curvature_proper_eq_green b K hK hG]
  exact rough_curvature_green_bound b M hM hb

end UV.RoughCurvature
