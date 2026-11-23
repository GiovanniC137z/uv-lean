import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Field.Periodic

/-! Periodic averaging for the absolute cross-spectral oscillation. -/

noncomputable section

open MeasureTheory Set Real Filter
open scoped Topology Interval

namespace UV.ContinueCrossTailPeriodic

private def centeredSine (a x : ℝ) : ℝ := |sin (a*x)| - 2/π

private def sinePrimitive (a x : ℝ) : ℝ := ∫ t in 0..x, centeredSine a t

private theorem continuous_centeredSine (a : ℝ) : Continuous (centeredSine a) := by
  unfold centeredSine
  fun_prop

private theorem centeredSine_periodic (a : ℝ) (ha : 0 < a) :
    Function.Periodic (centeredSine a) (π / a) := by
  intro x
  unfold centeredSine
  have h : a * (π/a) = π := by field_simp
  rw [mul_add, h, sin_add_pi, abs_neg]

/-- The mean over each absolute-sine period is exactly `2 / π`. -/
theorem abs_sine_period_integral (a : ℝ) (ha : 0 < a) :
    (∫ x in 0..(π/a), |sin (a*x)|) = (2/π) * (π/a) := by
  have hp : 0 < π/a := div_pos pi_pos ha
  have h : a * (π/a) = π := by field_simp
  calc
    _ = ∫ x in 0..(π/a), sin (a*x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hp.le] at hx
      apply abs_of_nonneg
      exact sin_nonneg_of_nonneg_of_le_pi (mul_nonneg ha.le hx.1)
        ((mul_le_mul_of_nonneg_left hx.2 ha.le).trans_eq h)
    _ = _ := by
      rw [intervalIntegral.integral_comp_mul_left sin ha.ne', mul_zero, h,
        integral_sin, cos_zero, cos_pi, smul_eq_mul]
      field_simp [ha.ne', pi_ne_zero]
      norm_num

private theorem centeredSine_period_integral (a : ℝ) (ha : 0 < a) :
    (∫ x in 0..(π/a), centeredSine a x) = 0 := by
  unfold centeredSine
  have hf : Continuous fun x : ℝ => |sin (a*x)| := by fun_prop
  have hi : IntervalIntegrable (fun _ : ℝ => (2/π : ℝ)) volume 0 (π/a) :=
    continuous_const.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) hi,
    abs_sine_period_integral a ha, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm, sub_self]

private theorem sinePrimitive_periodic (a : ℝ) (ha : 0 < a) :
    Function.Periodic (sinePrimitive a) (π/a) := by
  intro x
  unfold sinePrimitive
  rw [(centeredSine_periodic a ha).intervalIntegral_add_eq_add 0 x
    (fun u v => (continuous_centeredSine a).intervalIntegrable u v), zero_add,
    centeredSine_period_integral a ha, add_zero]

private theorem sinePrimitive_derivative (a x : ℝ) :
    HasDerivAt (sinePrimitive a) (centeredSine a x) x :=
  ((continuous_centeredSine a).integral_hasStrictDerivAt 0 x).hasDerivAt

private theorem sinePrimitive_continuous (a : ℝ) : Continuous (sinePrimitive a) :=
  continuous_iff_continuousAt.mpr fun x => (sinePrimitive_derivative a x).continuousAt

private theorem sinePrimitive_norm_bound (a : ℝ) (ha : 0 < a) (x : ℝ) :
    ‖sinePrimitive a x‖ ≤ (1 + 2/π) * (π/a) := by
  obtain ⟨y,hy,hEq⟩ := (sinePrimitive_periodic a ha).exists_mem_Ico₀ (div_pos pi_pos ha) x
  rw [hEq]
  have hn (t : ℝ) : ‖centeredSine a t‖ ≤ 1+2/π := by
    unfold centeredSine
    calc
      _ ≤ ‖|sin (a*t)|‖ + ‖(2/π : ℝ)‖ := norm_sub_le _ _
      _ ≤ _ := by
        rw [Real.norm_of_nonneg (abs_nonneg _), Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 2/π)]
        exact add_le_add_right (abs_sin_le_one _) _
  calc
    _ ≤ (1 + 2/π) * |y-0| := intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => hn t)
    _ ≤ _ := by rw [sub_zero, abs_of_nonneg hy.1]; gcongr; exact hy.2.le

private theorem interval_pos {K R : ℝ} (hK : 0 < K) (hKR : K ≤ R)
    {x : ℝ} (hx : x ∈ [[K,R]]) : 0 < x :=
  hK.trans_le ((uIcc_of_le hKR ▸ hx) : x ∈ Icc K R).1

/-- Centered absolute sine has a uniformly bounded weighted integral.
The explicit estimate also controls its Cauchy tails as `K → ∞`. -/
theorem centered_abs_sine_integral_budget (a K R : ℝ) (ha : 0 < a) (hK : 0 < K)
    (hKR : K ≤ R) :
    ‖∫ x in K..R, x⁻¹ * (|sin (a*x)| - 2/π)‖ ≤ 2 * ((1+2/π) * (π/a)) / K := by
  let C : ℝ := (1+2/π) * (π/a)
  let F := sinePrimitive a
  let q (x : ℝ) := (x^2)⁻¹
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hR : 0 < R := hK.trans_le hKR
  have hinv : ContinuousOn (fun x : ℝ => x⁻¹) [[K,R]] :=
    continuous_id.continuousOn.inv₀ (fun x hx => (interval_pos hK hKR hx).ne')
  have hq : ContinuousOn q [[K,R]] :=
    (continuous_id.pow 2).continuousOn.inv₀ (fun x hx => pow_ne_zero _ (interval_pos hK hKR hx).ne')
  have hqi : IntervalIntegrable q volume K R := hq.intervalIntegrable
  have hneg (x : ℝ) (hx : x ∈ Ioo (min K R) (max K R)) : 0 < x := by
    rw [min_eq_left hKR] at hx
    exact hK.trans hx.1
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := K) (b := R) (u := fun x : ℝ => x⁻¹) (v := F) (u' := fun x => -q x)
    (v' := centeredSine a) hinv (sinePrimitive_continuous a).continuousOn
    (fun x hx => hasDerivAt_inv (hneg x hx).ne') (fun x _ => sinePrimitive_derivative a x)
    (hqi.neg) ((continuous_centeredSine a).intervalIntegrable K R)
  have hqValue : (∫ x in K..R, q x) = K⁻¹ - R⁻¹ := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ => -x⁻¹) (f' := q)
      (fun x hx => by simpa only [neg_neg, q] using (hasDerivAt_inv (interval_pos hK hKR hx).ne').neg)
      hqi
    exact h.trans (by ring)
  have hI : ‖∫ x in K..R, (-q x) * F x‖ ≤ C * (K⁻¹ - R⁻¹) := by
    refine (intervalIntegral.norm_integral_le_integral_norm hKR).trans ?_
    have hFi : IntervalIntegrable (fun x => (-q x)*F x) volume K R :=
      (hq.neg.mul (sinePrimitive_continuous a).continuousOn).intervalIntegrable
    have hb := intervalIntegral.integral_mono_on hKR hFi.norm (hqi.const_mul C)
      (fun x _ => ?_)
    · exact hb.trans_eq (by rw [intervalIntegral.integral_const_mul, hqValue])
    · have hv : 0 ≤ q x := by dsimp [q]; positivity
      rw [norm_mul, norm_neg, Real.norm_of_nonneg hv, mul_comm C]
      exact mul_le_mul_of_nonneg_left (sinePrimitive_norm_bound a ha x) hv
  have hL (x : ℝ) (hx : 0 < x) : ‖x⁻¹ * F x‖ ≤ x⁻¹ * C := by
    rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hx.le)]
    exact mul_le_mul_of_nonneg_left (sinePrimitive_norm_bound a ha x) (inv_nonneg.mpr hx.le)
  change ‖∫ x in K..R, x⁻¹ * centeredSine a x‖ ≤ 2*C/K
  rw [hIBP]
  calc
    _ ≤ ‖R⁻¹ * F R‖ + ‖K⁻¹ * F K‖ + ‖∫ x in K..R, (-q x) * F x‖ :=
      (norm_sub_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
    _ ≤ R⁻¹*C + K⁻¹*C + C*(K⁻¹-R⁻¹) := add_le_add (add_le_add (hL _ hR) (hL _ hK)) hI
    _ = _ := by rw [div_eq_mul_inv]; ring

private theorem abs_sine_log_sub_eq_centered (a K R : ℝ) (hK : 0 < K) (hKR : K ≤ R) :
    (∫ x in K..R, |sin (a*x)|/x) - (2/π)*log R =
      (∫ x in K..R, x⁻¹ * centeredSine a x) - (2/π)*log K := by
  have hR : 0 < R := hK.trans_le hKR
  have hinv : ContinuousOn (fun x : ℝ => x⁻¹) [[K,R]] :=
    continuous_id.continuousOn.inv₀ (fun x hx => (interval_pos hK hKR hx).ne')
  have hi₁ : IntervalIntegrable (fun x => x⁻¹ * centeredSine a x) volume K R :=
    (hinv.mul (continuous_centeredSine a).continuousOn).intervalIntegrable
  have hi₂ : IntervalIntegrable (fun x : ℝ => (2/π)*x⁻¹) volume K R :=
    (show IntervalIntegrable (fun x : ℝ => x⁻¹) volume K R from hinv.intervalIntegrable).const_mul _
  have heq : (∫ x in K..R, |sin (a*x)|/x) =
      (∫ x in K..R, x⁻¹ * centeredSine a x) + (2/π)*(log R - log K) := by
    rw [← log_div hR.ne' hK.ne', ← integral_inv_of_pos hK hR, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hi₁ hi₂]
    · apply intervalIntegral.integral_congr
      intro x _
      unfold centeredSine
      rw [div_eq_mul_inv]
      ring
  rw [heq]
  ring

/-- The logarithmic coefficient of the literal absolute oscillation is
`2 / π` with a uniform bounded remainder above every positive threshold. -/
theorem abs_sine_div_log_remainder_bound (a K : ℝ) (ha : 0 < a) (hK : 0 < K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, K ≤ R →
      |(∫ x in K..R, |sin (a*x)| / x) - (2/π)*log R| ≤ C := by
  refine ⟨2*((1+2/π)*(π/a))/K + |(2/π)*log K|, by positivity, ?_⟩
  intro R hKR
  rw [abs_sine_log_sub_eq_centered a K R hK hKR]
  simp only [← Real.norm_eq_abs]
  exact (norm_sub_le _ _).trans (add_le_add_right (centered_abs_sine_integral_budget a K R ha hK hKR) _)

/-- The centered logarithmic discrepancy has a finite limit, with an
explicit inverse-radius remainder on the unrestricted radial half-line. -/
theorem abs_sine_div_log_remainder_limit (a K : ℝ) (ha : 0 < a) (hK : 0 < K) :
    ∃ L : ℝ, Tendsto (fun R => (∫ x in K..R, |sin (a*x)|/x) - (2/π)*log R) atTop (𝓝 L) ∧
      ∀ R : ℝ, K ≤ R →
        ‖(∫ x in K..R, |sin (a*x)|/x) - (2/π)*log R - L‖ ≤ 2*((1+2/π)*(π/a))/R := by
  let C : ℝ := 2*((1+2/π)*(π/a))
  let g (R : ℝ) := ∫ x in K..R, x⁻¹ * centeredSine a x
  have hi {U V : ℝ} (hU : 0 < U) (hUV : U ≤ V) :
      IntervalIntegrable (fun x => x⁻¹ * centeredSine a x) volume U V :=
    ((continuous_id.continuousOn.inv₀ (fun x hx => (interval_pos hU hUV hx).ne')).mul
      (continuous_centeredSine a).continuousOn).intervalIntegrable
  have hstep (R S : ℝ) (hKR : K ≤ R) (hRS : R ≤ S) : ‖g S - g R‖ ≤ C/R := by
    have h := intervalIntegral.integral_add_adjacent_intervals (hi hK hKR) (hi (hK.trans_le hKR) hRS)
    have he : g S - g R = ∫ x in R..S, x⁻¹ * centeredSine a x := by dsimp [g]; linarith
    rw [he]
    exact centered_abs_sine_integral_budget a R S ha (hK.trans_le hKR) hRS
  have hsmall : Tendsto (fun R : ℝ => C/R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0)).const_mul C
  have hC : CauchySeq g := by
    apply Metric.cauchySeq_iff'.mpr
    intro ε hε
    obtain ⟨N,hNK,hNe⟩ := ((eventually_ge_atTop K).and (hsmall.eventually (gt_mem_nhds hε))).exists
    refine ⟨N,fun R hNR => ?_⟩
    rw [Real.dist_eq, ← Real.norm_eq_abs]
    exact (hstep N R hNK hNR).trans_lt hNe
  obtain ⟨L,hL⟩ := cauchySeq_tendsto_of_complete hC
  refine ⟨L - (2/π)*log K, ?_, ?_⟩
  · apply (hL.sub_const ((2/π)*log K)).congr'
    filter_upwards [eventually_ge_atTop K] with R hR
    exact (abs_sine_log_sub_eq_centered a K R hK hR).symm
  · intro R hKR
    rw [abs_sine_log_sub_eq_centered a K R hK hKR]
    change ‖g R - (2/π)*log K - (L-(2/π)*log K)‖ ≤ C/R
    rw [show g R - (2/π)*log K - (L-(2/π)*log K) = g R - L by ring, norm_sub_rev]
    exact le_of_tendsto (hL.sub_const (g R)).norm ((eventually_ge_atTop R).mono fun S hRS =>
      hstep R S hKR hRS)

/-- Dividing the absolute-sine integral by `log R` gives the sharp
coefficient `2 / π` at every strictly positive oscillation rate. -/
theorem abs_sine_div_log_ratio_tendsto (a K : ℝ) (ha : 0 < a) (hK : 0 < K) :
    Tendsto (fun R => (∫ x in K..R, |sin (a*x)|/x) / log R) atTop (𝓝 (2/π)) := by
  obtain ⟨L,hL,_⟩ := abs_sine_div_log_remainder_limit a K ha hK
  have hi : Tendsto (fun R : ℝ => (log R)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_log_atTop
  have ht := (hL.mul hi).add (tendsto_const_nhds (x := (2/π : ℝ)))
  rw [mul_zero, zero_add] at ht
  apply ht.congr'
  filter_upwards [tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with R hR
  field_simp [hR.ne']
  ring

end UV.ContinueCrossTailPeriodic
