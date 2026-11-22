import UV.RevisionSourceGaussian
import UV.RevisionSourceMixture

/-! Actual Gaussian laws on the common product probability space for the
shared-depth fourth cumulant and the correlation of squares. -/

open MeasureTheory Filter
open scoped Topology

namespace UV

variable {Ω D : Type*} [MeasurableSpace Ω] [MeasurableSpace D]

/-- A measurable nonnegative variance is integrable under a probability law
when its square is integrable. The square's measurability is sufficient. -/
theorem depth_variance_integrable (w : Measure D) [IsProbabilityMeasure w]
    {v : D → ℝ} (hv : ∀ᵐ r ∂w, 0 ≤ v r) (hv₂ : Integrable (fun r => v r ^ 2) w) :
    Integrable v w := by
  have hm : AEStronglyMeasurable v w := by
    apply ((Real.continuous_sqrt.comp_aestronglyMeasurable hv₂.aestronglyMeasurable)).congr
    filter_upwards [hv] with r hr
    exact Real.sqrt_sq hr
  have hmajorant := (integrable_const (1 : ℝ)).add hv₂
  apply hmajorant.mono' hm
  filter_upwards [hv] with r hr
  simp only [Pi.add_apply, Real.norm_of_nonneg hr]
  nlinarith [sq_nonneg (v r - 1)]

/-- Conditional Gaussian laws and a square-integrable conditional variance
supply both joint integrability and the conditional moment identities. -/
theorem gaussian_depth_moments (w : Measure D) [IsProbabilityMeasure w]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : D × Ω → ℝ) (v : D → ℝ)
    (hX : Measurable X) (hv₂ : Integrable (fun r => v r ^ 2) w)
    (hLaw : ∀ᵐ r ∂w, 0 ≤ v r ∧ μ.map (fun ω => X (r, ω)) = sourceGaussian (v r)) :
    Integrable (fun z => X z ^ 2) (w.prod μ) ∧
    Integrable (fun z => X z ^ 4) (w.prod μ) ∧
    (∀ᵐ r ∂w, (∫ ω, X (r, ω) ^ 2 ∂μ) = v r) ∧
    (∀ᵐ r ∂w, (∫ ω, X (r, ω) ^ 4 ∂μ) = 3 * v r ^ 2) := by
  have hm : ∀ᵐ r ∂w, Integrable (fun ω => X (r, ω) ^ 2) μ ∧
      Integrable (fun ω => X (r, ω) ^ 4) μ ∧
      ((∫ ω, X (r, ω) ^ 2 ∂μ) = v r) ∧ ((∫ ω, X (r, ω) ^ 4 ∂μ) = 3 * v r ^ 2) := by
    filter_upwards [hLaw] with r hr
    exact source_gaussian_observable_moments μ _ (hX.comp measurable_prodMk_left).aemeasurable
      hr.1 hr.2
  have hv := depth_variance_integrable w (hLaw.mono fun _ hr => hr.1) hv₂
  exact ⟨integrable_depth_of_nonnegative_slices w μ (hX.pow_const 2).aestronglyMeasurable
      (fun z => sq_nonneg (X z)) (hm.mono fun _ h => h.1) hv (hm.mono fun _ h => h.2.2.1),
    integrable_depth_of_nonnegative_slices w μ (hX.pow_const 4).aestronglyMeasurable
      (fun z => by positivity) (hm.mono fun _ h => h.2.1) (hv₂.const_mul 3)
      (hm.mono fun _ h => h.2.2.2), hm.mono (fun _ h => h.2.2.1), hm.mono (fun _ h => h.2.2.2)⟩

/-- Fourth cumulant identity with actual conditional centered Gaussian laws. -/
theorem gaussian_shared_depth_fourth_cumulant (w : Measure D) [IsProbabilityMeasure w]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : D × Ω → ℝ) (v : D → ℝ)
    (hX : Measurable X) (hv₂ : Integrable (fun r => v r ^ 2) w)
    (hLaw : ∀ᵐ r ∂w, 0 ≤ v r ∧ μ.map (fun ω => X (r, ω)) = sourceGaussian (v r)) :
    (∫ z, X z ^ 4 ∂(w.prod μ)) - 3 * (∫ z, X z ^ 2 ∂(w.prod μ)) ^ 2 =
      3 * ((∫ r, v r ^ 2 ∂w) - (∫ r, v r ∂w) ^ 2) := by
  obtain ⟨h₂, h₄, hv₂', hv₄'⟩ := gaussian_depth_moments w μ X v hX hv₂ hLaw
  exact shared_depth_fourth_cumulant w μ X v h₂ h₄ hv₂' hv₄'

/-- The four scalar projections of a centered Gaussian pair with equal
variance. A common Gaussian field satisfies these laws on any two tests. -/
def sourceGaussianPairLaw (μ : Measure Ω) (X Y : Ω → ℝ) (v c : ℝ) : Prop :=
  0 ≤ v ∧ 0 ≤ 2 * v + 2 * c ∧ 0 ≤ 2 * v - 2 * c ∧
  μ.map X = sourceGaussian v ∧ μ.map Y = sourceGaussian v ∧
  μ.map (fun ω => X ω + Y ω) = sourceGaussian (2 * v + 2 * c) ∧
  μ.map (fun ω => X ω - Y ω) = sourceGaussian (2 * v - 2 * c)

theorem sourceGaussianPairLaw_abs_le (μ : Measure Ω) (X Y : Ω → ℝ) {v c : ℝ}
    (h : sourceGaussianPairLaw μ X Y v c) : |c| ≤ v := by
  apply abs_le.mpr
  exact ⟨by linarith [h.2.1], by linarith [h.2.2.1]⟩

/-- The correlation parameter in the four conditional scalar laws is the
actual mixed second moment. -/
theorem sourceGaussianPairLaw_mixed_moment (μ : Measure Ω) (X Y : Ω → ℝ)
    (hx : AEMeasurable X μ) (hy : AEMeasurable Y μ) {v c : ℝ}
    (h : sourceGaussianPairLaw μ X Y v c) : (∫ ω, X ω * Y ω ∂μ) = c := by
  rcases h with ⟨hv, hp, _, hxl, hyl, hpl, _⟩
  obtain ⟨hx₂, _, hxm, _⟩ := source_gaussian_observable_moments μ X hx hv hxl
  obtain ⟨hy₂, _, hym, _⟩ := source_gaussian_observable_moments μ Y hy hv hyl
  obtain ⟨_, _, hpm, _⟩ := source_gaussian_observable_moments μ _ (hx.add hy) hp hpl
  have hi : Integrable (fun ω => X ω * Y ω) μ := by
    apply ((hx₂.add hy₂).const_mul (1 / 2 : ℝ)).mono' (hx.mul hy).aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_le]
    simp only [Pi.add_apply]
    constructor <;> nlinarith [sq_nonneg (X ω + Y ω), sq_nonneg (X ω - Y ω)]
  have he : (fun ω => (X ω + Y ω) ^ 2) =
      fun ω => (X ω ^ 2 + Y ω ^ 2) + 2 * (X ω * Y ω) := by
    funext ω
    ring
  have hadd := integral_add (hx₂.add hy₂) (hi.const_mul 2)
  simp only [Pi.add_apply] at hadd
  rw [he, hadd, integral_add hx₂ hy₂, integral_const_mul, hxm, hym] at hpm
  linarith

/-- Covariance of the two squared readouts with actual conditional centered
Gaussian laws. The joint moment estimates follow from integrability of the
square of the common conditional variance. -/
theorem gaussian_shared_depth_square_covariance (w : Measure D) [IsProbabilityMeasure w]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : D × Ω → ℝ) (v c : D → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hc : AEMeasurable c w)
    (hv₂ : Integrable (fun r => v r ^ 2) w)
    (hLaw : ∀ᵐ r ∂w, sourceGaussianPairLaw μ (fun ω => X (r, ω)) (fun ω => Y (r, ω)) (v r) (c r)) :
    (∫ z, X z ^ 2 * Y z ^ 2 ∂(w.prod μ)) -
      (∫ z, X z ^ 2 ∂(w.prod μ)) * (∫ z, Y z ^ 2 ∂(w.prod μ)) =
      2 * (∫ r, c r ^ 2 ∂w) + ((∫ r, v r ^ 2 ∂w) - (∫ r, v r ∂w) ^ 2) := by
  obtain ⟨hx₂, hx₄, hx₂', _⟩ := gaussian_depth_moments w μ X v hX hv₂
    (hLaw.mono fun _ h => ⟨h.1, h.2.2.2.1⟩)
  obtain ⟨hy₂, hy₄, hy₂', _⟩ := gaussian_depth_moments w μ Y v hY hv₂
    (hLaw.mono fun _ h => ⟨h.1, h.2.2.2.2.1⟩)
  have hxy : Integrable (fun z => X z ^ 2 * Y z ^ 2) (w.prod μ) := by
    apply ((hx₄.add hy₄).const_mul (1 / 2 : ℝ)).mono'
      ((hX.pow_const 2).mul (hY.pow_const 2)).aestronglyMeasurable
    filter_upwards with z
    simp only [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)), Pi.add_apply]
    nlinarith [sq_nonneg (X z ^ 2 - Y z ^ 2)]
  have hc₂ : Integrable (fun r => c r ^ 2) w := by
    apply hv₂.mono' (hc.pow_const 2).aestronglyMeasurable
    filter_upwards [hLaw] with r hr
    rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (sourceGaussianPairLaw_abs_le μ _ _ hr) 2
  apply shared_depth_square_covariance w μ X Y v c hx₂ hy₂ hxy hv₂ hc₂ hx₂' hy₂'
  filter_upwards [hLaw] with r hr
  rcases hr with ⟨hv, hp, hm, hxl, hyl, hpl, hml⟩
  have hx' : AEMeasurable (fun ω => X (r, ω)) μ :=
    (hX.comp measurable_prodMk_left).aemeasurable
  have hy' : AEMeasurable (fun ω => Y (r, ω)) μ :=
    (hY.comp measurable_prodMk_left).aemeasurable
  obtain ⟨_, hx₄', _, hxM⟩ := source_gaussian_observable_moments μ _ hx' hv hxl
  obtain ⟨_, hy₄', _, hyM⟩ := source_gaussian_observable_moments μ _ hy' hv hyl
  obtain ⟨_, hp₄', _, hpM⟩ := source_gaussian_observable_moments μ _ (hx'.add hy') hp hpl
  obtain ⟨_, hm₄', _, hmM⟩ := source_gaussian_observable_moments μ _ (hx'.sub hy') hm hml
  exact square_wick_of_scalar_fourth_moments μ _ _ _ _ hx₄' hy₄' hp₄' hm₄' hxM hyM hpM hmM

/-- In the common-depth Gaussian model, conditional clustering leaves
exactly the variance of the conditional variance. -/
theorem gaussian_shared_depth_square_covariance_limit {R : Type*} (l : Filter R)
    [l.IsCountablyGenerated] (w : Measure D) [IsProbabilityMeasure w]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : D × Ω → ℝ) (Y : R → D × Ω → ℝ)
    (v : D → ℝ) (c : R → D → ℝ) (hX : Measurable X)
    (hv₂ : Integrable (fun r => v r ^ 2) w)
    (hY : ∀ᶠ R' in l, Measurable (Y R'))
    (hc : ∀ᶠ R' in l, AEMeasurable (c R') w)
    (hLaw : ∀ᶠ R' in l, ∀ᵐ r ∂w,
      sourceGaussianPairLaw μ (fun ω => X (r, ω)) (fun ω => Y R' (r, ω)) (v r) (c R' r))
    (hlim : ∀ᵐ r ∂w, Tendsto (fun R' => c R' r) l (𝓝 0)) :
    Tendsto (fun R' => (∫ z, X z ^ 2 * Y R' z ^ 2 ∂(w.prod μ)) -
      (∫ z, X z ^ 2 ∂(w.prod μ)) * (∫ z, Y R' z ^ 2 ∂(w.prod μ))) l
      (𝓝 ((∫ r, v r ^ 2 ∂w) - (∫ r, v r ∂w) ^ 2)) := by
  apply shared_depth_square_covariance_limit l w v c _ _
    (hc.mono fun _ hc' => hc'.aestronglyMeasurable) _ hv₂ hlim
  · filter_upwards [hY, hc, hLaw] with R' hY' hc' hLaw'
    exact gaussian_shared_depth_square_covariance w μ X (Y R') v (c R') hX hY' hc' hv₂ hLaw'
  · filter_upwards [hLaw] with R' hLaw'
    exact hLaw'.mono fun _ h => sourceGaussianPairLaw_abs_le μ _ _ h

end UV
