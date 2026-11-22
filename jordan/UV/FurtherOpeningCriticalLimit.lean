import UV.FurtherOpeningMoment

noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal Nat ProbabilityTheory

namespace UV

private def criticalShape (a M x : ℝ) : ℝ :=
  openingHalfMoment (x + a / Real.sqrt M) *
    (1 + min (max (1 + x / Real.sqrt M + a / M) 0) 1 / 2)

def openingCriticalPairSum (a M : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (- (M.toNNReal : ℝ)) * (M.toNNReal : ℝ) ^ n / n ! *
    (Real.sqrt (1 - ((n : ℝ) + a) / M) * (1 + (((n : ℝ) + a) / M) / 2))

lemma openingHalfMoment_shift_le {x d : ℝ} (hd : 0 ≤ d) :
    openingHalfMoment (x + d) ≤ openingHalfMoment x :=
  Real.sqrt_le_sqrt (max_le_max (by linarith) le_rfl)

lemma openingHalfMoment_shift_loss {x d : ℝ} (hd : 0 ≤ d) :
    openingHalfMoment x - openingHalfMoment (x + d) ≤ Real.sqrt d := by
  have hmax : max (-x) 0 ≤ max (-(x+d)) 0 + d :=
    max_le (by linarith [le_max_left (-(x+d)) 0]) (by positivity)
  have h1 := Real.sq_sqrt (le_max_right (-x) 0)
  have h2 := Real.sq_sqrt (le_max_right (-(x+d)) 0)
  have h0 := openingHalfMoment_shift_le (x := x) hd
  apply (Real.le_sqrt (sub_nonneg.mpr h0) hd).mpr
  unfold openingHalfMoment at *
  nlinarith [mul_nonneg (Real.sqrt_nonneg (max (-(x+d)) 0)) (sub_nonneg.mpr h0)]

lemma openingHalfMoment_mul_abs_le (x : ℝ) : openingHalfMoment x * |x| ≤ 1 + x ^ 2 := by
  have hmax : max (-x) 0 ≤ |x| := max_le (neg_le_abs _) (abs_nonneg _)
  by_cases hx : |x| ≤ 1
  · have h1 : openingHalfMoment x ≤ 1 := by
      exact (Real.sqrt_le_left zero_le_one).mpr (by simpa using hmax.trans hx)
    exact (mul_le_mul h1 hx (abs_nonneg _) zero_le_one).trans (by linarith [sq_nonneg x])
  · have h1 : openingHalfMoment x ≤ |x| := by
      apply (Real.sqrt_le_left (abs_nonneg _)).mpr
      exact hmax.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_not_ge hx)) (abs_nonneg x)])
    calc
      _ ≤ |x| * |x| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = x ^ 2 := by rw [← pow_two, sq_abs]
      _ ≤ _ := by linarith

private theorem criticalShape_le {a M : ℝ} (ha : 0 ≤ a) (_hM : 0 < M) (x : ℝ) :
    0 ≤ criticalShape a M x ∧ criticalShape a M x ≤ (3 / 2) * openingHalfMoment x := by
  let u := min (max (1 + x / Real.sqrt M + a / M) 0) 1
  have hu0 : 0 ≤ u := le_min (le_max_right _ _) zero_le_one
  have hu1 : u ≤ 1 := min_le_right _ _
  have h := openingHalfMoment_shift_le (x := x) (div_nonneg ha (Real.sqrt_nonneg M))
  change 0 ≤ openingHalfMoment (x + a / Real.sqrt M) * (1 + u / 2) ∧ _
  constructor
  · exact mul_nonneg (openingHalfMoment_nonneg _) (by linarith)
  · change openingHalfMoment (x + a / Real.sqrt M) * (1 + u / 2) ≤ _
    calc
      _ ≤ openingHalfMoment x * (3 / 2) :=
        mul_le_mul h (by linarith) (by linarith) (openingHalfMoment_nonneg _)
      _ = _ := mul_comm _ _

private theorem criticalShape_gap {a M : ℝ} (ha : 0 ≤ a) (hM : 0 < M) (x : ℝ) :
    (3 / 2) * openingHalfMoment x - criticalShape a M x ≤
      (3 / 2) * Real.sqrt (a / Real.sqrt M) + (1 + x ^ 2) / (2 * Real.sqrt M) := by
  let s := Real.sqrt M
  let u := min (max (1 + x / s + a / M) 0) 1
  have hs : 0 < s := Real.sqrt_pos.mpr hM
  have h1u : 0 ≤ 1 - u := sub_nonneg.mpr (min_le_right _ _)
  have h2u : 1 - u ≤ |x| / s := by
    dsimp [u]
    by_cases h : max (1 + x / s + a / M) 0 ≤ 1
    · rw [min_eq_left h]
      have hx := div_le_div_of_nonneg_right (neg_le_abs x) hs.le
      rw [neg_div] at hx
      linarith [le_max_left (1 + x / s + a / M) 0, div_nonneg ha hM.le]
    · rw [min_eq_right (le_of_not_ge h), sub_self]
      positivity
  have hd : 0 ≤ a / s := div_nonneg ha hs.le
  have hg := openingHalfMoment_shift_le (x := x) hd
  have hdrop := openingHalfMoment_shift_loss (x := x) hd
  have hp : openingHalfMoment (x + a / s) * ((1 - u) / 2) ≤ (1 + x ^ 2) / (2 * s) := by
    calc
      _ ≤ openingHalfMoment x * ((|x| / s) / 2) := mul_le_mul hg
        (div_le_div_of_nonneg_right h2u (by norm_num)) (by positivity) (openingHalfMoment_nonneg _)
      _ = (openingHalfMoment x * |x|) / (2 * s) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (openingHalfMoment_mul_abs_le x) (by positivity)
  change (3 / 2) * openingHalfMoment x -
    openingHalfMoment (x + a / s) * (1 + u / 2) ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hdrop (by norm_num : (0 : ℝ) ≤ 3 / 2)]

private theorem criticalShape_continuous (a M : ℝ) : Continuous (criticalShape a M) := by
  unfold criticalShape openingHalfMoment
  fun_prop

private theorem criticalShape_integrable {a M : ℝ} (ha : 0 ≤ a) (hM : 0 < M) :
    Integrable (criticalShape a M) (openingCriticalMeasure M : Measure ℝ) := by
  have h := (openingHalfMoment_integrable (openingCriticalMeasure_second_moment hM).1).const_mul (3 / 2)
  apply h.mono' (criticalShape_continuous a M).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_of_nonneg (criticalShape_le ha hM x).1]
  exact (criticalShape_le ha hM x).2

private theorem criticalShape_expectation_gap {a M : ℝ} (ha : 0 ≤ a) (hM : 0 < M) :
    (3 / 2) * (∫ x, openingHalfMoment x ∂(openingCriticalMeasure M : Measure ℝ)) -
      (∫ x, criticalShape a M x ∂(openingCriticalMeasure M : Measure ℝ)) ≤
      (3 / 2) * Real.sqrt (a / Real.sqrt M) + (Real.sqrt M)⁻¹ := by
  let μ : Measure ℝ := openingCriticalMeasure M
  have h2 := openingCriticalMeasure_second_moment hM
  have hI : Integrable (fun x ↦ ((3 / 2) : ℝ) * openingHalfMoment x) μ :=
    (openingHalfMoment_integrable h2.1).const_mul _
  have hJ : Integrable (criticalShape a M) μ := criticalShape_integrable ha hM
  let B := (3 / 2) * Real.sqrt (a / Real.sqrt M)
  have hN : Integrable (fun x : ℝ ↦ 1 + x ^ 2) μ := (integrable_const _).add h2.1
  have hG : Integrable (fun x : ℝ ↦ (1 + x ^ 2) / (2 * Real.sqrt M)) μ := hN.div_const _
  have hB : Integrable (fun x : ℝ ↦ B + (1 + x ^ 2) / (2 * Real.sqrt M)) μ :=
    (integrable_const _).add hG
  have h := integral_mono (hI.sub hJ) hB (criticalShape_gap ha hM)
  change (∫ x, (3 / 2) * openingHalfMoment x - criticalShape a M x ∂μ) ≤
    (∫ x : ℝ, B + (1 + x ^ 2) / (2 * Real.sqrt M) ∂μ) at h
  rw [integral_sub hI hJ, integral_const_mul,
    integral_add (integrable_const B) hG,
    integral_div, integral_add (integrable_const (1 : ℝ)) h2.1, h2.2] at h
  have hr : (1 + 1 : ℝ) / (2 * Real.sqrt M) = (Real.sqrt M)⁻¹ := by ring
  simpa [μ, B, Measure.real, hr] using h

private theorem criticalShape_expectation_le {a M : ℝ} (ha : 0 ≤ a) (hM : 0 < M) :
    (∫ x, criticalShape a M x ∂(openingCriticalMeasure M : Measure ℝ)) ≤
      (3 / 2) * (∫ x, openingHalfMoment x ∂(openingCriticalMeasure M : Measure ℝ)) := by
  rw [← integral_const_mul]
  exact integral_mono (criticalShape_integrable ha hM)
    ((openingHalfMoment_integrable (openingCriticalMeasure_second_moment hM).1).const_mul _)
    (fun x ↦ (criticalShape_le ha hM x).2)

theorem criticalShape_expectation_tendsto {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun M ↦ ∫ x, criticalShape a M x ∂(openingCriticalMeasure M : Measure ℝ)) atTop
      (𝓝 ((3 / 2) * ∫ x, openingHalfMoment x ∂(openingGaussianMeasure : Measure ℝ))) := by
  let B (M : ℝ) := (3 / 2) * Real.sqrt (a / Real.sqrt M) + (Real.sqrt M)⁻¹
  have hT : Tendsto B atTop (𝓝 0) := by
    have hD : Tendsto (fun M ↦ a / Real.sqrt M) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
    have hInv : Tendsto (fun M ↦ (Real.sqrt M)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
    simpa [B] using ((Real.continuous_sqrt.continuousAt.tendsto.comp hD).const_mul (3 / 2)).add hInv
  have hH := openingCriticalHalfMoment_tendsto.const_mul (3 / 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hH.sub hT) hH ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
    have hg := criticalShape_expectation_gap ha hM
    dsimp [B]
    linarith
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
    exact criticalShape_expectation_le ha hM

private theorem criticalShape_count {a M : ℝ} (ha : 0 ≤ a) (hM : 0 < M) (n : ℕ) :
    criticalShape a M (((n : ℝ) - M) / Real.sqrt M) = Real.sqrt (Real.sqrt M) *
      (Real.sqrt (1 - ((n : ℝ) + a) / M) * (1 + (((n : ℝ) + a) / M) / 2)) := by
  let x := ((n : ℝ) + a) / M
  let s := Real.sqrt M
  have hs : 0 < s := Real.sqrt_pos.mpr hM
  have hss : s ^ 2 = M := Real.sq_sqrt hM.le
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 1 + (((n : ℝ) - M) / s) / s + a / M = x := by
    rw [div_div, ← pow_two, hss]
    dsimp [x]
    field_simp
    ring
  have hz : -((((n : ℝ) - M) / s) + a / s) = s * (1 - x) := by
    calc
      _ = (M - ((n : ℝ) + a)) / s := by ring
      _ = s * ((M - ((n : ℝ) + a)) / M) := by rw [← hss]; field_simp
      _ = _ := by rw [sub_div, div_self hM.ne']
  have hmax (t : ℝ) : Real.sqrt (max t 0) = Real.sqrt t := by
    by_cases ht : 0 ≤ t
    · rw [max_eq_left ht]
    · rw [max_eq_right (le_of_not_ge ht), Real.sqrt_eq_zero_of_nonpos (le_of_not_ge ht), Real.sqrt_zero]
  change Real.sqrt (max (-((((n : ℝ) - M) / s) + a / s)) 0) *
    (1 + min (max (1 + (((n : ℝ) - M) / s) / s + a / M) 0) 1 / 2) =
    Real.sqrt s * (Real.sqrt (1 - x) * (1 + x / 2))
  rw [hy, hz, hmax, Real.sqrt_mul hs.le, max_eq_left hx]
  by_cases hx1 : x ≤ 1
  · rw [min_eq_left hx1, mul_assoc]
  · have h0 : Real.sqrt (1 - x) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
    simp [h0]

private theorem criticalShape_expectation_eq {a M : ℝ} (ha : 0 ≤ a) (hM : 0 < M) :
    (∫ x, criticalShape a M x ∂(openingCriticalMeasure M : Measure ℝ)) =
      Real.sqrt (Real.sqrt M) * openingCriticalPairSum a M := by
  rw [openingCriticalMeasure_eq_map, integral_map AEMeasurable.of_discrete (criticalShape_continuous a M).aestronglyMeasurable,
    integral_poissonMeasure]
  simp_rw [criticalShape_count ha hM, smul_eq_mul]
  rw [openingCriticalPairSum, ← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

/-- Critical coefficient for the actual inclusive Poisson sum of open
channels. Its scaling factor is `√√M = M^(1/4)`. -/
theorem openingCriticalPairSum_rescaled_limit {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun M ↦ Real.sqrt (Real.sqrt M) * openingCriticalPairSum a M) atTop
      (𝓝 ((3 / 2) * ∫ x, openingHalfMoment x ∂(openingGaussianMeasure : Measure ℝ))) := by
  apply (criticalShape_expectation_tendsto ha).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
  exact criticalShape_expectation_eq ha hM

/-- This coefficient is positive since the normal law has a positive
probability of a negative fluctuation. -/
theorem openingCriticalCoefficient_pos :
    0 < (3 / 2) * ∫ x, openingHalfMoment x ∂(openingGaussianMeasure : Measure ℝ) := by
  apply mul_pos (by norm_num)
  rw [integral_pos_iff_support_of_nonneg openingHalfMoment_nonneg
    (openingHalfMoment_integrable openingGaussianMeasure_second_moment.1)]
  have hs : Function.support openingHalfMoment = Set.Iio 0 := by
    ext x
    simp [openingHalfMoment]
  rw [hs]
  change 0 < gaussianReal 0 1 (Set.Iio 0)
  rw [gaussianReal_apply_eq_integral _ (by norm_num : (1 : ℝ≥0) ≠ 0), ENNReal.ofReal_pos,
    setIntegral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall (gaussianPDFReal_nonneg 0 1)) (integrable_gaussianPDFReal 0 1).restrict]
  have hPDF : Function.support (gaussianPDFReal 0 1) = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    exact (gaussianPDFReal_pos _ _ _ (by norm_num)).ne'
  rw [hPDF, Set.univ_inter, Real.volume_Iio]
  simp

/-- Critical pair density at the original timelike invariant on the selected
Lorentzian plane. At the critical slope the mean `bS` is `S/(4Δ)`. -/
def openingCriticalLorentzianDensity (e m Δ S : ℝ) : ℝ :=
  (e ^ 2 / (12 * Real.pi ^ 2)) * openingCriticalPairSum (m ^ 2 / Δ) (S / (4 * Δ))

theorem openingCriticalLorentzianDensity_channel_sum {e m Δ b S : ℝ}
    (hΔ : 0 < Δ) (hcrit : 4 * Δ * b = 1) (hS : 0 < S) :
    openingCriticalLorentzianDensity e m Δ S = (e ^ 2 / (12 * Real.pi ^ 2)) * ∑' n : ℕ,
      Real.exp (-(b * S)) * (b * S) ^ n / n ! *
        (Real.sqrt (1 - 4 * (m ^ 2 + n * Δ) / S) * (1 + 2 * (m ^ 2 + n * Δ) / S)) := by
  unfold openingCriticalLorentzianDensity openingCriticalPairSum
  congr 1
  apply tsum_congr
  intro n
  have hm : S / (4 * Δ) = b * S := by
    apply (div_eq_iff (by positivity : (4 * Δ : ℝ) ≠ 0)).mpr
    nlinarith [congrArg (fun x : ℝ ↦ S * x) hcrit]
  have hx : ((n : ℝ) + m ^ 2 / Δ) / (S / (4 * Δ)) = 4 * (m ^ 2 + n * Δ) / S := by
    field_simp
    ring
  rw [Real.coe_toNNReal _ (by positivity), hx, hm]
  congr 3
  ring

/-- The critical equivalent in the physical cut variable `S`. The normal
coefficient is strictly positive for nonzero electric charge. -/
theorem openingCriticalLorentzianDensity_equivalent {e m Δ : ℝ} (hΔ : 0 < Δ) (he : e ≠ 0) :
    let C : ℝ := (e ^ 2 / (12 * Real.pi ^ 2)) * ((3 / 2) *
      ∫ x, openingHalfMoment x ∂(openingGaussianMeasure : Measure ℝ))
    0 < C ∧ Tendsto (fun S ↦ (S / (4 * Δ)) ^ (1 / 4 : ℝ) *
      openingCriticalLorentzianDensity e m Δ S) atTop (𝓝 C) := by
  dsimp only
  refine ⟨mul_pos (by positivity) openingCriticalCoefficient_pos, ?_⟩
  have hS : Tendsto (fun S : ℝ ↦ S / (4 * Δ)) atTop atTop := by
    simp only [div_eq_mul_inv]
    exact tendsto_id.atTop_mul_const (by positivity)
  have ht : Tendsto (fun S ↦ Real.sqrt (Real.sqrt (S / (4 * Δ))) *
      openingCriticalLorentzianDensity e m Δ S) atTop
      (𝓝 ((e ^ 2 / (12 * Real.pi ^ 2)) * ((3 / 2) *
        ∫ x, openingHalfMoment x ∂(openingGaussianMeasure : Measure ℝ)))) := by
    simpa only [openingCriticalLorentzianDensity, Function.comp_apply, mul_left_comm] using
      ((openingCriticalPairSum_rescaled_limit (show 0 ≤ m ^ 2 / Δ by positivity)).comp hS).const_mul
        (e ^ 2 / (12 * Real.pi ^ 2))
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with S hS0
  have hM : 0 ≤ S / (4 * Δ) := by positivity
  rw [Real.sqrt_eq_rpow (Real.sqrt (S / (4 * Δ))), ← Real.rpow_div_two_eq_sqrt (1 / 2) hM]
  norm_num

end UV
