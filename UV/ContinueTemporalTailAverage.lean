import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! The normalized exponential average over the future of a point on the
normal coordinate. Its differential equation makes it possible to construct
the impedance for continuous, uniformly elliptic coefficients. -/

noncomputable section

namespace UV.TemporalRay

open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

def normalTailAverage (b : ℝ) (f : ℝ →ᵇ ℝ) (r : ℝ) : ℝ :=
  b * Real.exp (b*r) * ∫ s in Ioi r, Real.exp (-b*s) * f s

private theorem exp_weighted_integrable {b : ℝ} (hb : 0 < b) (f : ℝ →ᵇ ℝ) (r : ℝ) :
    IntegrableOn (fun s => Real.exp (-b*s) * f s) (Ioi r) := by
  refine ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hb) r).mul_const ‖f‖).mono' ?_ ?_
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul f.continuous).aestronglyMeasurable
  · filter_upwards with s
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm s) (Real.exp_pos _).le

private theorem tail_integral_split {b : ℝ} (hb : 0 < b) (f : ℝ →ᵇ ℝ) (r : ℝ) :
    (∫ s in Ioi r, Real.exp (-b*s)*f s) =
      (∫ s in Ioi (0:ℝ), Real.exp (-b*s)*f s) - ∫ s in (0:ℝ)..r, Real.exp (-b*s)*f s := by
  let g := fun s : ℝ => Real.exp (-b*s)*f s
  have hc : Continuous g := (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul f.continuous
  have h₁ := intervalIntegral_tendsto_integral_Ioi r (exp_weighted_integrable hb f r) tendsto_id
  have h₂ := (intervalIntegral_tendsto_integral_Ioi 0 (exp_weighted_integrable hb f 0) tendsto_id).sub_const
    (∫ s in (0:ℝ)..r, g s)
  apply tendsto_nhds_unique h₁
  apply h₂.congr'
  filter_upwards with t
  change (∫ s in (0:ℝ)..t, g s) - (∫ s in (0:ℝ)..r, g s) = ∫ s in r..t, g s
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 r) (hc.intervalIntegrable r t)]
  ring

theorem normal_tail_average_derivative {b : ℝ} (hb : 0 < b) (f : ℝ →ᵇ ℝ) (r : ℝ) :
    HasDerivAt (normalTailAverage b f) (b*(normalTailAverage b f r - f r)) r := by
  let g := fun s : ℝ => Real.exp (-b*s)*f s
  have hc : Continuous g := (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul f.continuous
  have hprim := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 r)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have h := (((hasDerivAt_id r).const_mul b).exp.const_mul b).mul
    (hprim.const_sub (∫ s in Ioi (0:ℝ), g s))
  have he : Real.exp (b*r) * Real.exp (-b*r) = 1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hrewrite : normalTailAverage b f = fun t => b * Real.exp (b*t) *
      ((∫ s in Ioi (0:ℝ), g s) - ∫ s in (0:ℝ)..t, g s) := by
    funext t
    exact congrArg (fun z => b*Real.exp (b*t)*z) (tail_integral_split hb f t)
  rw [hrewrite]
  convert h using 1
  dsimp [g, id]
  linear_combination b*f r*he

private theorem tail_mass {b : ℝ} (hb : 0 < b) (r : ℝ) :
    b * Real.exp (b*r) * (∫ s in Ioi r, Real.exp (-b*s)) = 1 := by
  rw [integral_exp_mul_Ioi (neg_lt_zero.mpr hb)]
  have h : Real.exp (b*r) * Real.exp (-b*r) = 1 := by
    rw [← Real.exp_add, show b*r + -b*r = 0 by ring, Real.exp_zero]
  field_simp
  simpa only [neg_mul] using h

theorem normal_tail_average_const {b : ℝ} (hb : 0 < b) (z r : ℝ) :
    normalTailAverage b (BoundedContinuousFunction.const ℝ z) r = z := by
  unfold normalTailAverage
  simp only [BoundedContinuousFunction.const_apply, integral_mul_const]
  rw [← mul_assoc, tail_mass hb, one_mul]

theorem normal_tail_average_mono {b : ℝ} (hb : 0 < b) {f g : ℝ →ᵇ ℝ}
    (h : ∀ s, f s ≤ g s) (r : ℝ) : normalTailAverage b f r ≤ normalTailAverage b g r := by
  refine mul_le_mul_of_nonneg_left (integral_mono (exp_weighted_integrable hb f r)
    (exp_weighted_integrable hb g r) fun s => ?_) (by positivity)
  exact mul_le_mul_of_nonneg_left (h s) (Real.exp_pos _).le

theorem normal_tail_average_dist {b : ℝ} (hb : 0 < b) {f g : ℝ →ᵇ ℝ} {C : ℝ}
    (h : ∀ s, |f s-g s| ≤ C) (r : ℝ) :
    |normalTailAverage b f r - normalTailAverage b g r| ≤ C := by
  have hsub : normalTailAverage b (f-g) r = normalTailAverage b f r - normalTailAverage b g r := by
    unfold normalTailAverage
    simp only [BoundedContinuousFunction.sub_apply, mul_sub]
    rw [integral_sub (exp_weighted_integrable hb f r) (exp_weighted_integrable hb g r), mul_sub]
  rw [← hsub, abs_le]
  constructor
  · rw [← normal_tail_average_const hb (-C) r]
    exact normal_tail_average_mono hb (fun s => (abs_le.mp (h s)).1) r
  · rw [← normal_tail_average_const hb C r]
    exact normal_tail_average_mono hb (fun s => (abs_le.mp (h s)).2) r

end UV.TemporalRay
