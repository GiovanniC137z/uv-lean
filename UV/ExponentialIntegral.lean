import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! The actual positive exponential integral and its logarithmic finite part. -/

noncomputable section
open MeasureTheory Filter Set Real Asymptotics
open scoped Topology

namespace UV

def exponentialIntegral (s : ℝ) : ℝ := ∫ t in Ioi s, Real.exp (-t) / t

def exponentialIntegralRemainder (t : ℝ) : ℝ := (1 - Real.exp (-t)) / t

theorem exponentialIntegral_integrable {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Ioi s) := by
  apply ((integrableOn_exp_neg_Ioi s).const_mul (1 / s)).mono'
  · exact (by fun_prop : Measurable (fun t : ℝ => Real.exp (-t) / t)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_of_nonneg (div_nonneg (Real.exp_nonneg _) (hs.trans ht).le)]
    calc
      _ ≤ Real.exp (-t) / s := div_le_div_of_nonneg_left (Real.exp_nonneg _) hs ht.le
      _ = _ := by ring

theorem exponentialIntegral_remainder_bounds {t : ℝ} (ht : 0 < t) :
    0 ≤ exponentialIntegralRemainder t ∧ exponentialIntegralRemainder t ≤ 1 := by
  unfold exponentialIntegralRemainder
  constructor
  · exact div_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))) ht.le
  · apply (div_le_one ht).mpr
    have hh := Real.add_one_le_exp (-t)
    linarith

theorem exponentialIntegral_remainder_intervalIntegrable {s : ℝ} (hs : 0 ≤ s) :
    IntervalIntegrable exponentialIntegralRemainder volume 0 s := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs]
  apply (integrable_const (1 : ℝ)).mono'
  · exact (by unfold exponentialIntegralRemainder; fun_prop : Measurable exponentialIntegralRemainder).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    obtain ⟨hn, hu⟩ := exponentialIntegral_remainder_bounds ht.1
    rwa [Real.norm_of_nonneg hn]

theorem exp_log_integrable : IntegrableOn (fun t : ℝ => Real.log t * Real.exp (-t)) (Ioi 0) := by
  have hnear : IntegrableOn (fun t : ℝ => Real.log t * Real.exp (-t)) (Ioc 0 1) := by
    have hi : IntervalIntegrable (fun t : ℝ => Real.log t * Real.exp (-t)) volume 0 1 :=
      intervalIntegral.intervalIntegrable_log'.mul_continuousOn (Real.continuous_exp.comp continuous_neg).continuousOn
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hi
  have hbase : IntegrableOn (fun t : ℝ => t * Real.exp (-t)) (Ioi 1) := by
    have hi := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (1 : ℝ))
      (b := (1 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    simp only [Real.rpow_one, neg_one_mul] at hi
    exact hi.mono_set (Ioi_subset_Ioi zero_le_one)
  have htail : IntegrableOn (fun t : ℝ => Real.log t * Real.exp (-t)) (Ioi 1) := by
    apply hbase.mono'
    · exact ((Real.measurable_log.mul (Real.continuous_exp.comp continuous_neg).measurable)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_of_nonneg (mul_nonneg (Real.log_nonneg ht.le) (Real.exp_nonneg _))]
      exact mul_le_mul_of_nonneg_right (Real.log_le_self (zero_le_one.trans ht.le)) (Real.exp_nonneg _)
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact hnear.union htail

theorem euler_constant_eq_exp_log_integral :
    Real.eulerMascheroniConstant = -(∫ t in Ioi 0, Real.log t * Real.exp (-t)) := by
  have hd := Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num)
  have heq : Complex.GammaIntegral =ᶠ[𝓝 (1 : ℂ)] Complex.Gamma := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (0 : ℝ) < (1 : ℂ).re by norm_num)] with z hz
    exact (Complex.Gamma_eq_integral hz).symm
  have hh := (hd.congr_of_eventuallyEq heq.symm).unique Complex.hasDerivAt_Gamma_one
  simp only [sub_self, Complex.cpow_zero, one_mul] at hh
  have hcast : (∫ t in Ioi (0 : ℝ), (Real.log t : ℂ) * (Real.exp (-t) : ℂ)) =
      ((∫ t in Ioi (0 : ℝ), Real.log t * Real.exp (-t) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext t
    exact (Complex.ofReal_mul _ _).symm
  rw [hcast] at hh
  have hr := congrArg Complex.re hh
  simp only [Complex.ofReal_re, Complex.neg_re] at hr
  linarith

theorem exp_neg_log_tendsto_atTop :
    Tendsto (fun t : ℝ => Real.exp (-t) * Real.log t) atTop (𝓝 0) := by
  apply squeeze_zero' (g := fun t : ℝ => t * Real.exp (-t))
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    exact mul_nonneg (Real.exp_nonneg _) (Real.log_nonneg (by linarith))
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    calc
      _ ≤ Real.exp (-t) * t := mul_le_mul_of_nonneg_left (Real.log_le_self (by linarith))
        (Real.exp_nonneg _)
      _ = _ := mul_comm _ _
  · simpa only [pow_one] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1

theorem exponentialIntegral_tail_integration_by_parts {s : ℝ} (hs : 0 < s) :
    exponentialIntegral s = -Real.exp (-s) * Real.log s +
      ∫ t in Ioi s, Real.log t * Real.exp (-t) := by
  have hJ := exp_log_integrable.mono_set (Ioi_subset_Ioi hs.le)
  have hder : ∀ t ∈ Ici s, HasDerivAt (fun t : ℝ => Real.exp (-t) * Real.log t)
      (Real.exp (-t) / t - Real.log t * Real.exp (-t)) t := by
    intro t ht
    have hh := ((hasDerivAt_neg t).exp).mul (Real.hasDerivAt_log (ne_of_gt (hs.trans_le ht)))
    convert hh using 1
    simp only [div_eq_mul_inv]
    ring
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto' hder
    ((exponentialIntegral_integrable hs).sub hJ) exp_neg_log_tendsto_atTop
  rw [integral_sub (exponentialIntegral_integrable hs) hJ] at hFTC
  unfold exponentialIntegral
  linarith

theorem regularized_exp_log_tendsto_zero :
    Tendsto (fun t : ℝ => (1 - Real.exp (-t)) * Real.log t) (𝓝[>] 0) (𝓝 0) := by
  have hd : HasDerivAt (fun t : ℝ => 1 - Real.exp (-t)) 1 0 := by
    convert ((hasDerivAt_neg (0 : ℝ)).exp).const_sub 1 using 1
    norm_num
  have hsl := (hasDerivAt_iff_tendsto_slope_left_right.mp hd).2
  have hlog : Tendsto (fun t : ℝ => t * Real.log t) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_mul] using Real.continuous_mul_log.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hh := hsl.mul hlog
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [slope_def_field, neg_zero, Real.exp_zero, sub_self, sub_zero]
  field_simp [ne_of_gt (show 0 < t from ht)]

theorem exponentialIntegral_small_integration_by_parts {s : ℝ} (hs : 0 < s) :
    (∫ t in (0 : ℝ)..s, Real.log t * Real.exp (-t)) +
      (∫ t in (0 : ℝ)..s, exponentialIntegralRemainder t) =
        (1 - Real.exp (-s)) * Real.log s := by
  have hJ : IntervalIntegrable (fun t : ℝ => Real.log t * Real.exp (-t)) volume 0 s := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs.le]
    exact exp_log_integrable.mono_set Ioc_subset_Ioi_self
  have hRem := exponentialIntegral_remainder_intervalIntegrable hs.le
  rw [← intervalIntegral.integral_add hJ hRem]
  have hd : ∀ t ∈ Ioo (0 : ℝ) s, HasDerivAt
      (fun t : ℝ => (1 - Real.exp (-t)) * Real.log t)
      (Real.log t * Real.exp (-t) + exponentialIntegralRemainder t) t := by
    intro t ht
    have hh := (((hasDerivAt_neg t).exp).const_sub 1).mul (Real.hasDerivAt_log ht.1.ne')
    convert hh using 1
    unfold exponentialIntegralRemainder
    ring
  have hscont : ContinuousAt (fun t : ℝ => (1 - Real.exp (-t)) * Real.log t) s := by
    exact (continuous_const.sub (Real.continuous_exp.comp continuous_neg)).continuousAt.mul
      (Real.continuousAt_log hs.ne')
  simpa only [sub_zero] using intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hs hd
    (hJ.add hRem) regularized_exp_log_tendsto_zero (hscont.tendsto.mono_left nhdsWithin_le_nhds)

theorem exponentialIntegral_exact_remainder {s : ℝ} (hs : 0 < s) :
    exponentialIntegral s + Real.eulerMascheroniConstant + Real.log s =
      ∫ t in (0 : ℝ)..s, exponentialIntegralRemainder t := by
  have hsplit : (∫ t in Ioi (0 : ℝ), Real.log t * Real.exp (-t)) =
      (∫ t in (0 : ℝ)..s, Real.log t * Real.exp (-t)) +
        ∫ t in Ioi s, Real.log t * Real.exp (-t) := by
    rw [intervalIntegral.integral_of_le hs.le]
    have hh := setIntegral_union (μ := (volume : Measure ℝ))
      (f := fun t : ℝ => Real.log t * Real.exp (-t))
      (disjoint_left.mpr (fun _ (h1 : _ ∈ Ioc 0 s) (h2 : _ ∈ Ioi s) => not_lt_of_ge h1.2 h2))
      measurableSet_Ioi (exp_log_integrable.mono_set Ioc_subset_Ioi_self)
      (exp_log_integrable.mono_set (Ioi_subset_Ioi hs.le))
    rw [Ioc_union_Ioi_eq_Ioi hs.le] at hh
    exact hh
  rw [exponentialIntegral_tail_integration_by_parts hs, euler_constant_eq_exp_log_integral, hsplit]
  have hsmall := exponentialIntegral_small_integration_by_parts hs
  linarith

theorem exponentialIntegral_error_bound {s : ℝ} (hs : 0 < s) :
    |exponentialIntegral s + Real.eulerMascheroniConstant + Real.log s| ≤ s := by
  rw [exponentialIntegral_exact_remainder hs]
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..s, exponentialIntegralRemainder t := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hs.le
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rcases ht.1.eq_or_lt with rfl | ht
    · norm_num [exponentialIntegralRemainder]
    · exact (exponentialIntegral_remainder_bounds ht).1
  rw [abs_of_nonneg hnonneg]
  calc
    _ ≤ ∫ _t in (0 : ℝ)..s, (1 : ℝ) := by
      apply intervalIntegral.integral_mono_ae_restrict hs.le
        (exponentialIntegral_remainder_intervalIntegrable hs.le) intervalIntegrable_const
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rcases ht.1.eq_or_lt with rfl | ht
      · norm_num [exponentialIntegralRemainder]
      · exact (exponentialIntegral_remainder_bounds ht).2
    _ = s := by simp

end UV
