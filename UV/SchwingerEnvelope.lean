import UV.GlobalConvergence
import UV.PolynomialRouting
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The source's actual infrared Schwinger envelopes. The estimates are
derived from integrability and a bound near zero, rather than an assumed
momentum-space decay bound. They combine with the full Laplace multiplier
and its endpoint inverse moment on four-dimensional loop momentum. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal BigOperators

namespace UV

/-- The covariance defined by the nonnegative proper-time envelope. -/
def schwingerCovariance (E : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ α : ℝ in Ioi 0, E α * exp (-α * z)

theorem schwinger_covariance_parameter_integrable {E : ℝ → ℝ}
    (hE : IntegrableOn E (Ioi 0)) (hpos : ∀ α, 0 < α → 0 ≤ E α)
    {z : ℝ} (hz : 0 ≤ z) :
    IntegrableOn (fun α => E α * exp (-α * z)) (Ioi 0) := by
  apply hE.mono' (hE.aestronglyMeasurable.mul (by fun_prop))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
  change ‖E α * exp (-α * z)‖ ≤ E α
  rw [Real.norm_of_nonneg (mul_nonneg (hpos α hα) (exp_nonneg _))]
  exact mul_le_of_le_one_right (hpos α hα)
    (exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_of_lt hα)) hz))

theorem schwinger_covariance_nonneg {E : ℝ → ℝ}
    (hpos : ∀ α, 0 < α → 0 ≤ E α) (z : ℝ) :
    0 ≤ schwingerCovariance E z := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
  exact mul_nonneg (hpos α hα) (exp_nonneg _)

theorem schwinger_covariance_measurable {E : ℝ → ℝ} (hE : Measurable E) :
    Measurable (schwingerCovariance E) := by
  have hm : StronglyMeasurable
      (fun x : ℝ × ℝ => E x.2 * exp (-x.2 * x.1)) := by
    exact (hE.comp measurable_snd |>.mul (by fun_prop)).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

/-- General infrared covariances are bounded at all nonnegative momenta by
their original proper-time mass. This controls discarded nonselected lines. -/
theorem schwinger_covariance_le_integral {E : ℝ → ℝ}
    (hE : IntegrableOn E (Ioi 0)) (hpos : ∀ α, 0 < α → 0 ≤ E α)
    {z : ℝ} (hz : 0 ≤ z) :
    schwingerCovariance E z ≤ ∫ α : ℝ in Ioi 0, E α := by
  apply integral_mono_ae (schwinger_covariance_parameter_integrable hE hpos hz) hE
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
  exact mul_le_of_le_one_right (hpos α hα)
    (exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_of_lt hα)) hz))

/-- The general infrared envelope has a massless power bound plus an
exponentially decaying tail. The constants are exactly the near-zero bound
and the original proper-time integral. -/
theorem schwinger_covariance_split_bound {E : ℝ → ℝ} {α0 K z : ℝ}
    (hE : IntegrableOn E (Ioi 0)) (hpos : ∀ α, 0 < α → 0 ≤ E α)
    (hα0 : 0 < α0) (hK : ∀ α ∈ Ioc 0 α0, E α ≤ K) (hz : 0 < z) :
    schwingerCovariance E z ≤
      K / z + (∫ α : ℝ in Ioi 0, E α) * exp (-α0 * z) := by
  have hK0 : 0 ≤ K := (hpos α0 hα0).trans (hK α0 ⟨hα0, le_rfl⟩)
  have hexp : IntegrableOn (fun α : ℝ => exp (-α * z)) (Ioi 0) := by
    simpa only [neg_mul, mul_comm z] using
      integrableOn_exp_mul_Ioi (a := -z) (by linarith) 0
  have hdom : ∀ᵐ α ∂volume.restrict (Ioi (0 : ℝ)),
      E α * exp (-α * z) ≤ K * exp (-α * z) + E α * exp (-α0 * z) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
    by_cases hle : α ≤ α0
    · have h := mul_le_mul_of_nonneg_right (hK α ⟨hα, hle⟩) (exp_nonneg (-α * z))
      have ht := mul_nonneg (hpos α hα) (exp_nonneg (-α0 * z))
      linarith
    · have hdec : exp (-α * z) ≤ exp (-α0 * z) := by
        apply exp_le_exp.mpr
        nlinarith [lt_of_not_ge hle]
      have h := mul_le_mul_of_nonneg_left hdec (hpos α hα)
      have ht := mul_nonneg hK0 (exp_nonneg (-α * z))
      linarith
  have hi := integral_mono_ae (schwinger_covariance_parameter_integrable hE hpos hz.le)
    ((hexp.const_mul K).add (hE.mul_const (exp (-α0 * z)))) hdom
  change schwingerCovariance E z ≤
    ∫ α : ℝ in Ioi 0, K * exp (-α * z) + E α * exp (-α0 * z) at hi
  rw [integral_add (hexp.const_mul K) (hE.mul_const (exp (-α0 * z))),
    integral_const_mul, integral_mul_const] at hi
  have he : (∫ α : ℝ in Ioi 0, exp (-α * z)) = 1 / z := by
    have h := integral_exp_mul_Ioi (a := -z) (by linarith) 0
    simpa only [mul_zero, exp_zero, neg_div_neg_eq, neg_mul, mul_comm z] using h
  rw [he] at hi
  simpa only [mul_one_div] using hi

/-- A four-dimensional Gaussian absorbs every nonnegative real numerator
degree. This is the regular tail term of the general Schwinger envelope. -/
theorem schwinger_gaussian_weight_integrable {d α0 : ℝ} (hd : 0 ≤ d) (hα0 : 0 < α0) :
    Integrable (fun q : LoopMomentum => ‖q‖ ^ d * exp (-α0 * ‖q‖ ^ 2)) := by
  have h := massless_gaussian_integrable (d := d + 2) (by linarith) hα0
  simpa only [add_sub_cancel_right] using h

/-- The Gaussian tail also has an explicit four-dimensional moment. -/
theorem schwinger_gaussian_weight_integral {d α0 : ℝ} (hd : 0 ≤ d) (hα0 : 0 < α0) :
    (∫ q : LoopMomentum, ‖q‖ ^ d * exp (-α0 * ‖q‖ ^ 2)) =
      π ^ 2 * α0 ^ (-(2 + d / 2)) * Gamma (2 + d / 2) := by
  have h := massless_gaussian_integral (d := d + 2) (by linarith) hα0
  have he : 1 + (d + 2) / 2 = 2 + d / 2 := by ring
  simpa only [add_sub_cancel_right, he] using h

theorem schwinger_full_laplace_nonneg (ρ : Measure ℝ) (z : ℝ) :
    0 ≤ laplace ρ z := integral_nonneg fun _ => exp_nonneg _

/-- The full multiplier's mass bound includes its support and no-atom
hypotheses, rather than silently discarding a contribution at zero. -/
theorem schwinger_full_laplace_le_mass (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0) {z : ℝ} (hz : 0 ≤ z) :
    laplace ρ z ≤ (ρ (Ioi 0)).toReal := by
  rw [← positiveLaplace_toReal_eq_laplace ρ hneg hzero hz]
  exact ENNReal.toReal_mono (measure_ne_top ρ _) (positiveLaplace_le_mass ρ hz)

theorem schwinger_full_laplace_measurable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0) (a : ℝ) :
    Measurable (fun q : LoopMomentum => laplace ρ (a ^ 2 * ‖q‖ ^ 2)) := by
  have he : (fun q : LoopMomentum => laplace ρ (a ^ 2 * ‖q‖ ^ 2)) =
      fun q => (positiveLaplace ρ (a ^ 2 * ‖q‖ ^ 2)).toReal := by
    ext q
    exact (positiveLaplace_toReal_eq_laplace ρ hneg hzero (by positivity)).symm
  rw [he]
  unfold positiveLaplace
  fun_prop

/-- Damping the general Schwinger covariance gives a selected massless line
and a regular Gaussian tail as an explicit derived momentum envelope. -/
theorem schwinger_damped_line_bound (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0)
    {E : ℝ → ℝ} {α0 K a d : ℝ}
    (hE : IntegrableOn E (Ioi 0)) (hpos : ∀ α, 0 < α → 0 ≤ E α)
    (hα0 : 0 < α0) (hK : ∀ α ∈ Ioc 0 α0, E α ≤ K)
    {q : LoopMomentum} (hq : q ≠ 0) :
    ‖q‖ ^ d * laplace ρ (a ^ 2 * ‖q‖ ^ 2) * schwingerCovariance E (‖q‖ ^ 2) ≤
      K * (‖q‖ ^ d * selectedLine ρ a 0 q) +
        ((ρ (Ioi 0)).toReal * (∫ α : ℝ in Ioi 0, E α)) *
          (‖q‖ ^ d * exp (-α0 * ‖q‖ ^ 2)) := by
  have hI : 0 ≤ ∫ α : ℝ in Ioi 0, E α := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
    exact hpos α hα
  have hq2 : 0 < ‖q‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hq)
  have hΦ0 := schwinger_full_laplace_nonneg ρ (a ^ 2 * ‖q‖ ^ 2)
  have hΦ := schwinger_full_laplace_le_mass ρ hneg hzero
    (show 0 ≤ a ^ 2 * ‖q‖ ^ 2 by positivity)
  have hbound := schwinger_covariance_split_bound hE hpos hα0 hK hq2
  have hfirst : K * (‖q‖ ^ d * selectedLine ρ a 0 q) =
      ‖q‖ ^ d * laplace ρ (a ^ 2 * ‖q‖ ^ 2) * (K / ‖q‖ ^ 2) := by
    unfold selectedLine
    rw [positiveLaplace_toReal_eq_laplace ρ hneg hzero (by positivity)]
    simp only [zero_pow two_ne_zero, add_zero]
    ring
  rw [hfirst]
  calc
    _ ≤ ‖q‖ ^ d * laplace ρ (a ^ 2 * ‖q‖ ^ 2) *
        (K / ‖q‖ ^ 2 + (∫ α : ℝ in Ioi 0, E α) * exp (-α0 * ‖q‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hbound (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hΦ0)
    _ = ‖q‖ ^ d * laplace ρ (a ^ 2 * ‖q‖ ^ 2) * (K / ‖q‖ ^ 2) +
        (laplace ρ (a ^ 2 * ‖q‖ ^ 2) * (∫ α : ℝ in Ioi 0, E α)) *
          (‖q‖ ^ d * exp (-α0 * ‖q‖ ^ 2)) := by ring
    _ ≤ _ := by gcongr

/-- Endpoint inverse moments suffice for one actual damped line with the
source's general infrared prescription, at every nonnegative real degree. -/
theorem schwinger_damped_line_integrable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0)
    {E : ℝ → ℝ} {α0 K a d : ℝ}
    (hmE : Measurable E) (hE : IntegrableOn E (Ioi 0))
    (hpos : ∀ α, 0 < α → 0 ≤ E α)
    (hα0 : 0 < α0) (hK : ∀ α ∈ Ioc 0 α0, E α ≤ K)
    (ha : 0 < a) (hd : 0 ≤ d) (hM : inverseMoment ρ (1 + d / 2) < ⊤) :
    Integrable (fun q : LoopMomentum =>
      ‖q‖ ^ d * laplace ρ (a ^ 2 * ‖q‖ ^ 2) * schwingerCovariance E (‖q‖ ^ 2)) := by
  have hline := (selectedLine_weight_integrable ρ ha hd hM 0).const_mul K
  have htail := (schwinger_gaussian_weight_integrable hd hα0).const_mul
    ((ρ (Ioi 0)).toReal * (∫ α : ℝ in Ioi 0, E α))
  apply (hline.add htail).mono' ?_ ?_
  · exact (((continuous_norm.rpow_const (fun _ => Or.inr hd)).measurable.mul
      (schwinger_full_laplace_measurable ρ hneg hzero a)).mul
      ((schwinger_covariance_measurable hmE).comp (by fun_prop))).aestronglyMeasurable
  · have hq : ∀ᵐ q : LoopMomentum, q ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hq] with q hq
    change ‖‖q‖ ^ d * laplace ρ (a ^ 2 * ‖q‖ ^ 2) * schwingerCovariance E (‖q‖ ^ 2)‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (schwinger_full_laplace_nonneg _ _))
      (schwinger_covariance_nonneg hpos _))]
    exact schwinger_damped_line_bound ρ hneg hzero hE hpos hα0 hK hq

/-- Explicit endpoint-moment bound for a line with a general Schwinger
envelope; it retains the proper-time tail instead of discarding it. -/
def schwingerMomentBound (ρ : Measure ℝ) (E : ℝ → ℝ) (a d α0 K : ℝ) : ℝ :=
  K * lineMomentBound ρ a d +
    ((ρ (Ioi 0)).toReal * (∫ α : ℝ in Ioi 0, E α)) *
      (π ^ 2 * α0 ^ (-(2 + d / 2)) * Gamma (2 + d / 2))

theorem schwinger_damped_line_integral_le (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0)
    {E : ℝ → ℝ} {α0 K a d : ℝ}
    (hmE : Measurable E) (hE : IntegrableOn E (Ioi 0))
    (hpos : ∀ α, 0 < α → 0 ≤ E α)
    (hα0 : 0 < α0) (hK : ∀ α ∈ Ioc 0 α0, E α ≤ K)
    (ha : 0 < a) (hd : 0 ≤ d) (hM : inverseMoment ρ (1 + d / 2) < ⊤) :
    (∫ q : LoopMomentum,
      ‖q‖ ^ d * laplace ρ (a ^ 2 * ‖q‖ ^ 2) * schwingerCovariance E (‖q‖ ^ 2)) ≤
      schwingerMomentBound ρ E a d α0 K := by
  have hK0 : 0 ≤ K := (hpos α0 hα0).trans (hK α0 ⟨hα0, le_rfl⟩)
  have hline := (selectedLine_weight_integrable ρ ha hd hM 0).const_mul K
  have htail := (schwinger_gaussian_weight_integrable hd hα0).const_mul
    ((ρ (Ioi 0)).toReal * (∫ α : ℝ in Ioi 0, E α))
  have hq : ∀ᵐ q : LoopMomentum, q ≠ 0 := by rw [ae_iff]; simp
  calc
    _ ≤ ∫ q : LoopMomentum, K * (‖q‖ ^ d * selectedLine ρ a 0 q) +
        ((ρ (Ioi 0)).toReal * (∫ α : ℝ in Ioi 0, E α)) *
          (‖q‖ ^ d * exp (-α0 * ‖q‖ ^ 2)) := by
      apply integral_mono_ae
        (schwinger_damped_line_integrable ρ hneg hzero hmE hE hpos hα0 hK ha hd hM)
        (hline.add htail)
      filter_upwards [hq] with q hq
      exact schwinger_damped_line_bound ρ hneg hzero hE hpos hα0 hK hq
    _ = K * (∫ q : LoopMomentum, ‖q‖ ^ d * selectedLine ρ a 0 q) +
        ((ρ (Ioi 0)).toReal * (∫ α : ℝ in Ioi 0, E α)) *
          (π ^ 2 * α0 ^ (-(2 + d / 2)) * Gamma (2 + d / 2)) := by
      rw [integral_add hline htail, integral_const_mul, integral_const_mul,
        schwinger_gaussian_weight_integral hd hα0]
    _ ≤ _ := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left (selectedLine_integral_le ρ ha hd hM 0) hK0) _

/-- The constant and degree-d numerator terms of a general infrared line. -/
def schwingerWeight (ρ : Measure ℝ) (E : ℝ → ℝ) (a d : ℝ) (q : LoopMomentum) : ℝ :=
  (1 + ‖q‖ ^ d) * laplace ρ (a ^ 2 * ‖q‖ ^ 2) * schwingerCovariance E (‖q‖ ^ 2)

theorem schwingerWeight_nonneg (ρ : Measure ℝ) {E : ℝ → ℝ}
    (hpos : ∀ α, 0 < α → 0 ≤ E α) (a d : ℝ) (q : LoopMomentum) :
    0 ≤ schwingerWeight ρ E a d q := by
  exact mul_nonneg (mul_nonneg (by positivity) (schwinger_full_laplace_nonneg _ _))
    (schwinger_covariance_nonneg hpos _)

/-- One highest inverse moment controls the constant and every lower degree
of the actual Schwinger line, just as for the mass denominator. -/
theorem schwingerWeight_integrable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0)
    {E : ℝ → ℝ} {α0 K a d D : ℝ}
    (hmE : Measurable E) (hE : IntegrableOn E (Ioi 0))
    (hpos : ∀ α, 0 < α → 0 ≤ E α)
    (hα0 : 0 < α0) (hK : ∀ α ∈ Ioc 0 α0, E α ≤ K)
    (ha : 0 < a) (hd : 0 ≤ d) (hdD : d ≤ D)
    (hM : inverseMoment ρ (1 + D / 2) < ⊤) :
    Integrable (schwingerWeight ρ E a d) := by
  have hM0 : inverseMoment ρ (1 + 0 / 2) < ⊤ :=
    inverseMoment_lower_order_finite ρ (by norm_num) (by linarith) hM
  have hMd : inverseMoment ρ (1 + d / 2) < ⊤ :=
    inverseMoment_lower_order_finite ρ (by linarith) (by linarith) hM
  have h0 := schwinger_damped_line_integrable ρ hneg hzero hmE hE hpos hα0 hK
    ha (show (0 : ℝ) ≤ 0 by rfl) hM0
  have hdegree := schwinger_damped_line_integrable ρ hneg hzero hmE hE hpos hα0 hK ha hd hMd
  convert h0.add hdegree using 1
  ext q
  simp only [schwingerWeight, Real.rpow_zero, one_mul, Pi.add_apply]
  ring

theorem schwingerWeight_integral_le (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0)
    {E : ℝ → ℝ} {α0 K a d D : ℝ}
    (hmE : Measurable E) (hE : IntegrableOn E (Ioi 0))
    (hpos : ∀ α, 0 < α → 0 ≤ E α)
    (hα0 : 0 < α0) (hK : ∀ α ∈ Ioc 0 α0, E α ≤ K)
    (ha : 0 < a) (hd : 0 ≤ d) (hdD : d ≤ D)
    (hM : inverseMoment ρ (1 + D / 2) < ⊤) :
    (∫ q, schwingerWeight ρ E a d q) ≤
      schwingerMomentBound ρ E a 0 α0 K + schwingerMomentBound ρ E a d α0 K := by
  have hM0 : inverseMoment ρ (1 + 0 / 2) < ⊤ :=
    inverseMoment_lower_order_finite ρ (by norm_num) (by linarith) hM
  have hMd : inverseMoment ρ (1 + d / 2) < ⊤ :=
    inverseMoment_lower_order_finite ρ (by linarith) (by linarith) hM
  have h0 := schwinger_damped_line_integrable ρ hneg hzero hmE hE hpos hα0 hK
    ha (show (0 : ℝ) ≤ 0 by rfl) hM0
  have hdegree := schwinger_damped_line_integrable ρ hneg hzero hmE hE hpos hα0 hK ha hd hMd
  have he : schwingerWeight ρ E a d = fun q =>
      ‖q‖ ^ (0 : ℝ) * laplace ρ (a ^ 2 * ‖q‖ ^ 2) * schwingerCovariance E (‖q‖ ^ 2) +
      ‖q‖ ^ d * laplace ρ (a ^ 2 * ‖q‖ ^ 2) * schwingerCovariance E (‖q‖ ^ 2) := by
    ext q
    simp only [schwingerWeight, Real.rpow_zero, one_mul]
    ring
  rw [he, integral_add h0 hdegree]
  exact add_le_add
    (schwinger_damped_line_integral_le ρ hneg hzero hmE hE hpos hα0 hK
      ha (show (0 : ℝ) ≤ 0 by rfl) hM0)
    (schwinger_damped_line_integral_le ρ hneg hzero hmE hE hpos hα0 hK ha hd hMd)

/-- The actual damped covariance factor of one uncut virtual line. -/
def schwingerLine (ρ : Measure ℝ) (E : ℝ → ℝ) (a : ℝ) (q : LoopMomentum) : ℝ :=
  laplace ρ (a ^ 2 * ‖q‖ ^ 2) * schwingerCovariance E (‖q‖ ^ 2)

theorem schwingerLine_nonneg (ρ : Measure ℝ) {E : ℝ → ℝ}
    (hpos : ∀ α, 0 < α → 0 ≤ E α) (a : ℝ) (q : LoopMomentum) :
    0 ≤ schwingerLine ρ E a q :=
  mul_nonneg (schwinger_full_laplace_nonneg _ _) (schwinger_covariance_nonneg hpos _)

theorem schwingerLine_measurable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0)
    {E : ℝ → ℝ} (hmE : Measurable E) (a : ℝ) :
    Measurable (schwingerLine ρ E a) :=
  (schwinger_full_laplace_measurable ρ hneg hzero a).mul
    ((schwinger_covariance_measurable hmE).comp (by fun_prop))

/-- The nonselected factors have a uniform bound derived from the actual
proper-time mass and the actual multiplier measure. -/
theorem schwingerLine_le_mass (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0)
    {E : ℝ → ℝ} (hE : IntegrableOn E (Ioi 0))
    (hpos : ∀ α, 0 < α → 0 ≤ E α) (a : ℝ) (q : LoopMomentum) :
    schwingerLine ρ E a q ≤ (ρ (Ioi 0)).toReal * (∫ α : ℝ in Ioi 0, E α) := by
  apply mul_le_mul
    (schwinger_full_laplace_le_mass ρ hneg hzero (by positivity))
    (schwinger_covariance_le_integral hE hpos (sq_nonneg _))
    (schwinger_covariance_nonneg hpos _) ENNReal.toReal_nonneg

/-- Independent general-infrared line factors control a complete numerator
having a factorized degree bound, with an explicit uniform integral estimate. -/
theorem schwinger_product_integrable
    {ι P F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ι → Measure ℝ) [∀ j, IsFiniteMeasure (ρ j)]
    (hneg : ∀ j, ρ j (Iio 0) = 0) (hzero : ∀ j, ρ j {0} = 0)
    (E : ι → ℝ → ℝ) (a d D α0 K : ι → ℝ)
    (hmE : ∀ j, Measurable (E j)) (hE : ∀ j, IntegrableOn (E j) (Ioi 0))
    (hpos : ∀ j α, 0 < α → 0 ≤ E j α)
    (hα0 : ∀ j, 0 < α0 j) (hK : ∀ j, ∀ α ∈ Ioc 0 (α0 j), E j α ≤ K j)
    (ha : ∀ j, 0 < a j) (hd : ∀ j, 0 ≤ d j) (hdD : ∀ j, d j ≤ D j)
    (hM : ∀ j, inverseMoment (ρ j) (1 + D j / 2) < ⊤)
    {C : ℝ} (hC : 0 ≤ C) (f : P → (ι → LoopMomentum) → F)
    (hf : ∀ p, AEStronglyMeasurable (f p) (Measure.pi fun _ : ι => volume))
    (hb : ∀ p ℓ, ‖f p ℓ‖ ≤ C * ∏ j, schwingerWeight (ρ j) (E j) (a j) (d j) (ℓ j)) :
    ∀ p, Integrable (f p) (Measure.pi fun _ : ι => volume) ∧
      (∫ ℓ, ‖f p ℓ‖ ∂(Measure.pi fun _ : ι => volume)) ≤
        C * ∏ j, (schwingerMomentBound (ρ j) (E j) (a j) 0 (α0 j) (K j) +
          schwingerMomentBound (ρ j) (E j) (a j) (d j) (α0 j) (K j)) := by
  have hi (j : ι) : Integrable (schwingerWeight (ρ j) (E j) (a j) (d j)) :=
    schwingerWeight_integrable (ρ j) (hneg j) (hzero j) (hmE j) (hE j) (hpos j)
      (hα0 j) (hK j) (ha j) (hd j) (hdD j) (hM j)
  have hp := Integrable.fintype_prod hi
  intro p
  have hfp := (hp.const_mul C).mono' (hf p) (Filter.Eventually.of_forall (hb p))
  refine ⟨hfp, ?_⟩
  calc
    _ ≤ ∫ ℓ : ι → LoopMomentum, C * ∏ j,
        schwingerWeight (ρ j) (E j) (a j) (d j) (ℓ j)
        ∂(Measure.pi fun _ : ι => volume) :=
      integral_mono_ae hfp.norm (hp.const_mul C) (Filter.Eventually.of_forall (hb p))
    _ = C * ∏ j, ∫ q, schwingerWeight (ρ j) (E j) (a j) (d j) q := by
      rw [integral_const_mul, integral_fintype_prod_eq_prod]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Finset.prod_le_prod
      · intro j _
        exact integral_nonneg (schwingerWeight_nonneg (ρ j) (hpos j) (a j) (d j))
      · intro j _
        exact schwingerWeight_integral_le (ρ j) (hneg j) (hzero j) (hmE j) (hE j) (hpos j)
          (hα0 j) (hK j) (ha j) (hd j) (hdD j) (hM j)

/-- The direct routed proof of the global moment criterion for general
infrared covariances. A uniform original-coordinate complete-numerator bound
is converted by the inverse routing; the actual line integrability and its
uniform quantitative bound are derived from the endpoint inverse moment. -/
theorem schwinger_routed_graph
    {ι P F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ι → Measure ℝ) [∀ j, IsFiniteMeasure (ρ j)]
    (hneg : ∀ j, ρ j (Iio 0) = 0) (hzero : ∀ j, ρ j {0} = 0)
    (E : ι → ℝ → ℝ) (a α0 K : ι → ℝ)
    (hmE : ∀ j, Measurable (E j)) (hE : ∀ j, IntegrableOn (E j) (Ioi 0))
    (hpos : ∀ j α, 0 < α → 0 ≤ E j α)
    (hα0 : ∀ j, 0 < α0 j) (hK : ∀ j, ∀ α ∈ Ioc 0 (α0 j), E j α ≤ K j)
    (ha : ∀ j, 0 < a j) {B C D : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hM : ∀ j, inverseMoment (ρ j) (1 + D / 2) < ⊤)
    (e : (ι → LoopMomentum) ≃L[ℝ] (ι → LoopMomentum))
    (b : P → (ι → LoopMomentum)) (hb : ∀ p, ‖b p‖ ≤ B)
    (N : P → (ι → LoopMomentum) → F) (hmN : ∀ p, StronglyMeasurable (N p))
    (hN : ∀ p k, ‖N p k‖ ≤ C * (1 + ‖k‖ ^ D)) :
    ∀ p, Integrable (fun k =>
      (∏ j, schwingerLine (ρ j) (E j) (a j) ((e k + b p) j)) • N p k)
        (Measure.pi fun _ : ι => volume) ∧
      (∫ k, ‖(∏ j, schwingerLine (ρ j) (E j) (a j) ((e k + b p) j)) • N p k‖
        ∂(Measure.pi fun _ : ι => volume)) ≤
        |(LinearMap.det e.toLinearMap)⁻¹| *
          (C * (1 + (‖e.symm.toContinuousLinearMap‖ * (1 + B)) ^ D)) *
          ∏ j, (schwingerMomentBound (ρ j) (E j) (a j) 0 (α0 j) (K j) +
            schwingerMomentBound (ρ j) (E j) (a j) D (α0 j) (K j)) := by
  let Cr := C * (1 + (‖e.symm.toContinuousLinearMap‖ * (1 + B)) ^ D)
  have hCr : 0 ≤ Cr := mul_nonneg hC (by positivity)
  let g : P → (ι → LoopMomentum) → F := fun p ℓ =>
    (∏ j, schwingerLine (ρ j) (E j) (a j) (ℓ j)) • N p (e.symm (ℓ - b p))
  have hmg : ∀ p, AEStronglyMeasurable (g p) (Measure.pi fun _ : ι => volume) := by
    intro p
    have hmline (j : ι) : Measurable (fun ℓ : ι → LoopMomentum =>
        schwingerLine (ρ j) (E j) (a j) (ℓ j)) :=
      (schwingerLine_measurable (ρ j) (hneg j) (hzero j) (hmE j) (a j)).comp
        (measurable_pi_apply j)
    exact ((Finset.measurable_prod _ (fun j _ => hmline j)).stronglyMeasurable.smul
      ((hmN p).comp_measurable (by fun_prop))).aestronglyMeasurable
  have hbg : ∀ p ℓ, ‖g p ℓ‖ ≤ Cr * ∏ j, schwingerWeight (ρ j) (E j) (a j) D (ℓ j) := by
    intro p ℓ
    have hn : 0 ≤ ∏ j, schwingerLine (ρ j) (E j) (a j) (ℓ j) :=
      Finset.prod_nonneg fun j _ => schwingerLine_nonneg (ρ j) (hpos j) (a j) (ℓ j)
    change ‖(∏ j, schwingerLine (ρ j) (E j) (a j) (ℓ j)) •
      N p (e.symm (ℓ - b p))‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg hn]
    calc
      _ ≤ (∏ j, schwingerLine (ρ j) (E j) (a j) (ℓ j)) *
          (Cr * ∏ j, (1 + ‖ℓ j‖ ^ D)) :=
        mul_le_mul_of_nonneg_left
          (numerator_bound_after_affine_routing e b hB hC hD hb N hN p ℓ) hn
      _ = _ := by
        simp only [schwingerWeight, schwingerLine, Finset.prod_mul_distrib]
        ring
  have hg := schwinger_product_integrable ρ hneg hzero E a (fun _ => D) (fun _ => D) α0 K
    hmE hE hpos hα0 hK ha (fun _ => hD) (fun _ => le_rfl) hM hCr g hmg hbg
  intro p
  have heq : (fun k => g p (e k + b p)) = fun k =>
      (∏ j, schwingerLine (ρ j) (E j) (a j) ((e k + b p) j)) • N p k := by
    ext k
    simp only [g, add_sub_cancel_right, ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨heq ▸ routing_integrable (Measure.pi fun _ : ι => volume) e (b p) (hg p).1, ?_⟩
  simp_rw [← congrFun heq]
  rw [routing_integral (Measure.pi fun _ : ι => volume) e (b p) (fun ℓ => ‖g p ℓ‖)]
  exact (mul_le_mul_of_nonneg_left (hg p).2 (abs_nonneg _)).trans_eq (by dsimp [Cr]; ring)

/-- All virtual lines of the finite graph are included. The selected lines
span loop space through the actual affine equivalence; the remaining lines
have arbitrary measurable routings and their original covariance masses
give the uniform bound. Only the source's endpoint moment is required. -/
theorem global_schwinger_graph
    {ι κ P F : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ι → Measure ℝ) [∀ j, IsFiniteMeasure (ρ j)]
    (hneg : ∀ j, ρ j (Iio 0) = 0) (hzero : ∀ j, ρ j {0} = 0)
    (E : ι → ℝ → ℝ) (a α0 K : ι → ℝ)
    (hmE : ∀ j, Measurable (E j)) (hE : ∀ j, IntegrableOn (E j) (Ioi 0))
    (hpos : ∀ j α, 0 < α → 0 ≤ E j α)
    (hα0 : ∀ j, 0 < α0 j) (hK : ∀ j, ∀ α ∈ Ioc 0 (α0 j), E j α ≤ K j)
    (ha : ∀ j, 0 < a j) {B C D : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hM : ∀ j, inverseMoment (ρ j) (1 + D / 2) < ⊤)
    (ρu : κ → Measure ℝ) [∀ u, IsFiniteMeasure (ρu u)]
    (hnegu : ∀ u, ρu u (Iio 0) = 0) (hzerou : ∀ u, ρu u {0} = 0)
    (Eu : κ → ℝ → ℝ) (au : κ → ℝ)
    (hmEu : ∀ u, Measurable (Eu u)) (hEu : ∀ u, IntegrableOn (Eu u) (Ioi 0))
    (hposu : ∀ u α, 0 < α → 0 ≤ Eu u α)
    (qu : κ → P → (ι → LoopMomentum) → LoopMomentum)
    (hmqu : ∀ u p, Measurable (qu u p))
    (e : (ι → LoopMomentum) ≃L[ℝ] (ι → LoopMomentum))
    (b : P → (ι → LoopMomentum)) (hb : ∀ p, ‖b p‖ ≤ B)
    (N : P → (ι → LoopMomentum) → F) (hmN : ∀ p, StronglyMeasurable (N p))
    (hN : ∀ p k, ‖N p k‖ ≤ C * (1 + ‖k‖ ^ D)) :
    ∀ p, Integrable (fun k =>
      ((∏ j, schwingerLine (ρ j) (E j) (a j) ((e k + b p) j)) *
        (∏ u, schwingerLine (ρu u) (Eu u) (au u) (qu u p k))) • N p k)
        (Measure.pi fun _ : ι => volume) ∧
      (∫ k, ‖((∏ j, schwingerLine (ρ j) (E j) (a j) ((e k + b p) j)) *
        (∏ u, schwingerLine (ρu u) (Eu u) (au u) (qu u p k))) • N p k‖
        ∂(Measure.pi fun _ : ι => volume)) ≤
        |(LinearMap.det e.toLinearMap)⁻¹| *
          (((∏ u, (ρu u (Ioi 0)).toReal * (∫ α : ℝ in Ioi 0, Eu u α)) * C) *
            (1 + (‖e.symm.toContinuousLinearMap‖ * (1 + B)) ^ D)) *
          ∏ j, (schwingerMomentBound (ρ j) (E j) (a j) 0 (α0 j) (K j) +
            schwingerMomentBound (ρ j) (E j) (a j) D (α0 j) (K j)) := by
  let U := ∏ u, (ρu u (Ioi 0)).toReal * (∫ α : ℝ in Ioi 0, Eu u α)
  have hU : 0 ≤ U := by
    apply Finset.prod_nonneg
    intro u _
    apply mul_nonneg ENNReal.toReal_nonneg
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
    exact hposu u α hα
  let Nu : P → (ι → LoopMomentum) → F := fun p k =>
    (∏ u, schwingerLine (ρu u) (Eu u) (au u) (qu u p k)) • N p k
  have hmNu : ∀ p, StronglyMeasurable (Nu p) := by
    intro p
    apply StronglyMeasurable.smul _ (hmN p)
    apply Measurable.stronglyMeasurable
    exact Finset.measurable_prod _ fun u _ =>
      (schwingerLine_measurable (ρu u) (hnegu u) (hzerou u) (hmEu u) (au u)).comp (hmqu u p)
  have hNu : ∀ p k, ‖Nu p k‖ ≤ (U * C) * (1 + ‖k‖ ^ D) := by
    intro p k
    have hp0 : 0 ≤ ∏ u, schwingerLine (ρu u) (Eu u) (au u) (qu u p k) :=
      Finset.prod_nonneg fun u _ => schwingerLine_nonneg (ρu u) (hposu u) (au u) (qu u p k)
    have hp : (∏ u, schwingerLine (ρu u) (Eu u) (au u) (qu u p k)) ≤ U := by
      apply Finset.prod_le_prod
      · intro u _
        exact schwingerLine_nonneg (ρu u) (hposu u) (au u) (qu u p k)
      · intro u _
        exact schwingerLine_le_mass (ρu u) (hnegu u) (hzerou u) (hEu u) (hposu u) (au u) _
    change ‖(∏ u, schwingerLine (ρu u) (Eu u) (au u) (qu u p k)) • N p k‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg hp0]
    calc
      _ ≤ U * (C * (1 + ‖k‖ ^ D)) := mul_le_mul hp (hN p k) (norm_nonneg _) hU
      _ = _ := by ring
  have h := schwinger_routed_graph ρ hneg hzero E a α0 K hmE hE hpos hα0 hK ha
    hB (mul_nonneg hU hC) hD hM e b hb Nu hmNu hNu
  intro p
  simpa only [Nu, smul_smul, U] using h p

end UV
