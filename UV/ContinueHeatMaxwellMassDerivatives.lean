import UV.ContinueHeatMaxwellSignIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-! All squared-mass derivatives of the fixed-width two-branch Maxwell
coefficient, with strict complete monotonicity on the physical mass ray. -/

noncomputable section

namespace UV.HeatMaxwell

open MeasureTheory Set Filter
open scoped Topology

theorem heatMaxwellDensity_integrable : IntegrableOn heatMaxwellDensity (Ioo 0 heatPeak) := by
  let μ := (volume : Measure ℝ).restrict (Ioo 0 heatPeak)
  let g := fun y => heatMaxwellDensity y / (1+y)^2
  have hg : Integrable g μ := heatMaxwellDensity_kernel_integrable zero_lt_one
  have hmeas : Measurable (fun y : ℝ => (1+y)^2) := (measurable_const.add measurable_id).pow_const 2
  have h : Integrable (fun y => (1+y)^2*g y) μ := by
    refine hg.bdd_mul' (c := (1+heatPeak)^2) hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioo 0 heatPeak) measurableSet_Ioo] with y hy
    exact (Real.norm_of_nonneg (sq_nonneg _)).trans_le
      (pow_le_pow_left₀ (by linarith [hy.1]) (add_le_add_left hy.2.le 1) 2)
  refine h.congr ?_
  filter_upwards [ae_restrict_mem (μ := volume) (s := Ioo 0 heatPeak) measurableSet_Ioo] with y hy
  change (1+y)^2 * (heatMaxwellDensity y / (1+y)^2) = _
  field_simp [show 1+y ≠ 0 by linarith [hy.1]]

def heatMassMoment (n : ℕ) (x : ℝ) : ℝ :=
  ∫ y in Ioo 0 heatPeak, heatMaxwellDensity y / (x+y)^(n+2)

private theorem heat_mass_power_meas (k : ℕ) (x : ℝ) :
    AEStronglyMeasurable (fun y => heatMaxwellDensity y/(x+y)^k) (volume.restrict (Ioo 0 heatPeak)) :=
by
  let μ := (volume : Measure ℝ).restrict (Ioo 0 heatPeak)
  have hm : Measurable (fun y : ℝ => ((x+y)^k)⁻¹) :=
    ((measurable_const.add measurable_id).pow_const k).inv
  have hd : AEStronglyMeasurable heatMaxwellDensity μ := heatMaxwellDensity_integrable.1
  simpa only [div_eq_mul_inv] using hd.mul (hm.aestronglyMeasurable (μ := μ))

private theorem heat_mass_integrable (k : ℕ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun y => heatMaxwellDensity y/(x+y)^k) (Ioo 0 heatPeak) := by
  refine (heatMaxwellDensity_integrable.div_const (x^k)).mono' (heat_mass_power_meas k x) ?_
  filter_upwards [ae_restrict_mem (μ := volume) (s := Ioo 0 heatPeak) measurableSet_Ioo] with y hy
  rw [Real.norm_of_nonneg (div_nonneg (heatMaxwellDensity_pos hy).le (pow_pos (add_pos hx hy.1) _).le)]
  exact div_le_div_of_nonneg_left (heatMaxwellDensity_pos hy).le (pow_pos hx _)
    (pow_le_pow_left₀ hx.le (le_add_of_nonneg_right hy.1.le) k)

private theorem heat_mass_point_derivative (k : ℕ) {x y : ℝ} (hx : 0 < x+y) :
    HasDerivAt (fun w => heatMaxwellDensity y/(w+y)^(k+1))
      (-((k+1 : ℕ) : ℝ)*(heatMaxwellDensity y/(x+y)^(k+2))) x := by
  have h := (hasDerivAt_const x (heatMaxwellDensity y)).div
    (((hasDerivAt_id x).add_const y).pow (k+1)) (pow_ne_zero _ hx.ne')
  convert h using 1
  simp only [Pi.pow_apply,id_eq,Nat.add_sub_cancel,zero_mul,zero_sub,mul_one]
  rw [show k+2 = (k+1)+1 by omega, pow_succ (x+y) (k+1),pow_succ (x+y) k]
  field_simp

theorem heatMassMoment_hasDerivAt (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (heatMassMoment n) (-((n+2 : ℕ) : ℝ)*heatMassMoment (n+1) x) x := by
  let μ := (volume : Measure ℝ).restrict (Ioo 0 heatPeak)
  let c : ℝ := ((n+2 : ℕ) : ℝ)
  let F := fun w y => heatMaxwellDensity y/(w+y)^(n+2)
  let G := fun w y => -c*(heatMaxwellDensity y/(w+y)^(n+3))
  have hc : 0 ≤ c := Nat.cast_nonneg _
  have hx' : 0 < x/2 := by positivity
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := G) (μ := μ)
    (bound := fun y => c*(heatMaxwellDensity y/(x/2)^(n+3))) hx'
    (Eventually.of_forall (heat_mass_power_meas (n+2))) (heat_mass_integrable (n+2) hx)
    ((heat_mass_power_meas (n+3) x).const_mul (-c)) (by
      filter_upwards [ae_restrict_mem (μ := volume) (s := Ioo 0 heatPeak) measurableSet_Ioo] with y hy w hw
      have hw' : x/2 < w := by
        rw [Metric.mem_ball,Real.dist_eq,abs_lt] at hw
        linarith only [hw.1]
      have hpos := hx'.trans (hw'.trans (lt_add_of_pos_right w hy.1))
      change ‖-c*(heatMaxwellDensity y/(w+y)^(n+3))‖ ≤ _
      rw [norm_mul,norm_neg,Real.norm_of_nonneg hc, Real.norm_of_nonneg
        (div_nonneg (heatMaxwellDensity_pos hy).le (pow_pos hpos _).le)]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (heatMaxwellDensity_pos hy).le
        (pow_pos hx' _) (pow_le_pow_left₀ hx'.le (hw'.le.trans (le_add_of_nonneg_right hy.1.le)) _)) hc)
    ((heatMaxwellDensity_integrable.div_const _).const_mul c) (by
      filter_upwards [ae_restrict_mem (μ := volume) (s := Ioo 0 heatPeak) measurableSet_Ioo] with y hy w hw
      rw [Metric.mem_ball,Real.dist_eq,abs_lt] at hw
      exact heat_mass_point_derivative (n+1) (by linarith only [hw.1,hy.1,hx]))
  have he := hd.2
  change HasDerivAt (heatMassMoment n) (∫ y, -c*(heatMaxwellDensity y/(x+y)^(n+3)) ∂μ) x at he
  rw [integral_const_mul] at he
  exact he

/-- The exact factorial and kernel power in every squared-mass derivative. -/
theorem heatMaxwellCoefficient_iteratedDeriv (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n heatMaxwellCoefficient x =
      (-1 : ℝ)^n*((n+1).factorial : ℝ)*heatMassMoment n x := by
  induction n generalizing x with
  | zero => simpa [heatMassMoment] using heatMaxwellCoefficient_positive_density hx
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n heatMaxwellCoefficient =ᶠ[𝓝 x]
        fun w => ((-1 : ℝ)^n*((n+1).factorial : ℝ))*heatMassMoment n w := by
      filter_upwards [eventually_gt_nhds hx] with w hw
      exact ih hw
    rw [he.deriv_eq, ((heatMassMoment_hasDerivAt n hx).const_mul _).deriv, Nat.factorial_succ (n+1), pow_succ]
    push_cast
    ring

theorem heatMaxwellCoefficient_strict_complete_monotone (n : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < (-1 : ℝ)^n * iteratedDeriv n heatMaxwellCoefficient x := by
  have hm : 0 < heatMassMoment n x := heatPeak_integral_pos (heat_mass_integrable (n+2) hx)
    (fun y hy => div_pos (heatMaxwellDensity_pos hy) (pow_pos (add_pos hx hy.1) _))
  rw [heatMaxwellCoefficient_iteratedDeriv n hx,← mul_assoc,← mul_assoc,← mul_pow]
  norm_num
  positivity

end UV.HeatMaxwell
