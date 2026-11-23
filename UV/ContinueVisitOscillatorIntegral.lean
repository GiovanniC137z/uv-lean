import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-! The literal Gaussian integral in the odd normal oscillator's
cutoff variance calculation. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace UV.ContinueVisitOscillatorIntegral

def gaussianDifferenceProfile (b u : ℝ) : ℝ :=
  (1 - Real.exp (-b * u ^ (2 : ℕ))) / u ^ (2 : ℕ)

private theorem gaussian_difference_profile_nonneg {b : ℝ} (hb : 0 ≤ b) (u : ℝ) :
    0 ≤ gaussianDifferenceProfile b u := by
  unfold gaussianDifferenceProfile
  exact div_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (sq_nonneg _)))) (sq_nonneg _)

private theorem gaussian_difference_profile_time {b u : ℝ} (hb : 0 < b) (hu : u ≠ 0) :
    (∫ t in Ioc (0 : ℝ) b, Real.exp (-t * u ^ (2 : ℕ))) = gaussianDifferenceProfile b u := by
  let F : ℝ → ℝ := fun t => Real.exp (-(u ^ (2 : ℕ)) * t) / -(u ^ (2 : ℕ))
  have hF (t : ℝ) : HasDerivAt F (Real.exp (-t * u ^ (2 : ℕ))) t := by
    convert (((hasDerivAt_id t).const_mul (-(u ^ (2 : ℕ)))).exp.div_const
      (-(u ^ (2 : ℕ)))) using 1
    simp only [id_eq, mul_one]
    rw [mul_div_cancel_right₀ _ (neg_ne_zero.mpr (pow_ne_zero _ hu))]
    congr 1
    ring
  have hI : IntervalIntegrable (fun t : ℝ => Real.exp (-t * u ^ (2 : ℕ))) volume 0 b := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [← intervalIntegral.integral_of_le hb.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t) hI]
  unfold F gaussianDifferenceProfile
  simp only [mul_zero, Real.exp_zero, div_neg]
  rw [show -(u ^ (2 : ℕ)) * b = -b * u ^ (2 : ℕ) by ring]
  ring

private theorem gaussian_difference_profile_time_enn {b u : ℝ} (hb : 0 < b) (hu : u ≠ 0) :
    ENNReal.ofReal (gaussianDifferenceProfile b u) =
      ∫⁻ t in Ioc (0 : ℝ) b, ENNReal.ofReal (Real.exp (-t * u ^ (2 : ℕ))) := by
  let f : ℝ → ℝ := fun t => Real.exp (-t * u ^ (2 : ℕ))
  have hf : Continuous f := by unfold f; fun_prop
  have hI : IntegrableOn f (Ioc 0 b) := hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hp : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioc 0 b), 0 ≤ f t :=
    Eventually.of_forall fun _ => Real.exp_nonneg _
  rw [← gaussian_difference_profile_time hb hu]
  exact ofReal_integral_eq_lintegral_ofReal hI hp

private theorem real_volume_ae_ne_zero : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 0 := by
  have he : {u : ℝ | ¬ u ≠ 0} = ({0} : Set ℝ) := by ext u; simp
  exact ae_iff.mpr (he ▸ measure_singleton (0 : ℝ))

private theorem gaussian_time_radial_integral {b : ℝ} (hb : 0 < b) :
    (∫⁻ t in Ioc (0 : ℝ) b,
      ENNReal.ofReal (Real.sqrt (Real.pi / t))) =
      ENNReal.ofReal (2 * Real.sqrt Real.pi * Real.sqrt b) := by
  have he (t : ℝ) (ht : 0 < t) :
      Real.sqrt (Real.pi / t) = Real.sqrt Real.pi * t ^ (-(1 / 2) : ℝ) := by
    rw [Real.sqrt_div Real.pi_pos.le, div_eq_mul_inv, Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
  let f : ℝ → ℝ := fun t => Real.sqrt Real.pi * t ^ (-(1 / 2) : ℝ)
  have hi : IntegrableOn f (Ioc 0 b) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num : -(1 : ℝ) < -(1 / 2)))).const_mul _
  calc
    _ = ∫⁻ t in Ioc (0 : ℝ) b, ENNReal.ofReal (f t) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [he t ht.1]
    _ = ENNReal.ofReal (∫ t in Ioc (0 : ℝ) b, f t) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal hi
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg ht.1.le _)
    _ = _ := by
      unfold f
      rw [integral_const_mul, ← intervalIntegral.integral_of_le hb.le,
        integral_rpow (Or.inl (by norm_num))]
      congr 1
      rw [show (-(1 / 2) : ℝ) + 1 = 1 / 2 by norm_num,
        Real.zero_rpow (by norm_num), sub_zero, ← Real.sqrt_eq_rpow]
      ring

/-- A positive proper-time representation and Gaussian integration
evaluate the difference quotient exactly on the full normal line. -/
theorem gaussian_difference_profile_integral {b : ℝ} (hb : 0 < b) :
    Integrable (gaussianDifferenceProfile b) ∧
      (∫ u : ℝ, gaussianDifferenceProfile b u) = 2 * Real.sqrt Real.pi * Real.sqrt b := by
  let g : ℝ → ℝ → ℝ≥0∞ := fun u t => ENNReal.ofReal (Real.exp (-t * u ^ (2 : ℕ)))
  have hmeas : Measurable (Function.uncurry g) := by unfold g Function.uncurry; fun_prop
  have hG (t : ℝ) (ht : 0 < t) :
      (∫⁻ u, g u t) = ENNReal.ofReal (Real.sqrt (Real.pi / t)) := by
    unfold g
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_sq ht)
      (Eventually.of_forall fun _ => Real.exp_nonneg _), integral_gaussian]
  have hEq : (∫⁻ u, ENNReal.ofReal (gaussianDifferenceProfile b u)) =
      ENNReal.ofReal (2 * Real.sqrt Real.pi * Real.sqrt b) := by
    calc
      _ = ∫⁻ u : ℝ, ∫⁻ t in Ioc (0 : ℝ) b, g u t :=
        lintegral_congr_ae (real_volume_ae_ne_zero.mono (fun _ hu =>
          gaussian_difference_profile_time_enn hb hu))
      _ = ∫⁻ t in Ioc (0 : ℝ) b, ∫⁻ u, g u t := lintegral_lintegral_swap hmeas.aemeasurable
      _ = _ := by
        rw [← gaussian_time_radial_integral hb]
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hG t ht.1
  have hm : Measurable (gaussianDifferenceProfile b) := by unfold gaussianDifferenceProfile; fun_prop
  have hpos : ∀ᵐ u ∂(volume : Measure ℝ), 0 ≤ gaussianDifferenceProfile b u :=
    Eventually.of_forall (gaussian_difference_profile_nonneg hb.le)
  have hi : Integrable (gaussianDifferenceProfile b) :=
    (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable hpos).mp
      (hEq.trans_ne ENNReal.ofReal_ne_top)
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi hpos] at hEq
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (gaussian_difference_profile_nonneg hb.le))
    (by positivity)).mp hEq

def oddOscillatorScalingProfile (u : ℝ) : ℝ :=
  (1 - Real.exp (-(u ^ (2 : ℕ)))) ^ (2 : ℕ) / u ^ (2 : ℕ)

theorem odd_oscillator_scaling_profile_integral :
    Integrable oddOscillatorScalingProfile ∧
      (∫ u : ℝ, oddOscillatorScalingProfile u) =
        4 * Real.sqrt Real.pi * (1 - (Real.sqrt 2)⁻¹) := by
  have h1 := gaussian_difference_profile_integral (b := 1) one_pos
  have h2 := gaussian_difference_profile_integral (b := 2) two_pos
  have he : oddOscillatorScalingProfile = fun u =>
      2 * gaussianDifferenceProfile 1 u - gaussianDifferenceProfile 2 u := by
    funext u
    unfold oddOscillatorScalingProfile gaussianDifferenceProfile
    rw [neg_one_mul, show (-2 : ℝ) * u ^ (2 : ℕ) = -(u ^ (2 : ℕ)) + -(u ^ (2 : ℕ)) by ring,
      Real.exp_add]
    ring
  have hi := h1.1.const_mul (2 : ℝ)
  rw [he]
  refine ⟨hi.sub h2.1, ?_⟩
  rw [integral_sub hi h2.1, integral_const_mul, h1.2, h2.2, Real.sqrt_one, mul_one]
  have hs : Real.sqrt 2 = 2 * (Real.sqrt 2)⁻¹ := by
    rw [← div_eq_mul_inv, eq_div_iff (Real.sqrt_pos.mpr two_pos).ne', ← pow_two,
      Real.sq_sqrt two_pos.le]
  nth_rw 1 [hs]
  ring

end UV.ContinueVisitOscillatorIntegral
