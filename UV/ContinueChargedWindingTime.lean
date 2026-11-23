import UV.ExtendNativeHolonomyDeterminant
import UV.FurtherBoundaryCollar
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! Proper times and all fixed holonomy derivatives of the nonzero
windings on the actual normal circle. The bound keeps both UV faces
and the massive long-time tail. -/

noncomputable section
open Real MeasureTheory Set Filter
open scoped ENNReal Topology
namespace UV.ExtendNativeHolonomy

private theorem paired_time_integrable {b a : ℝ} (hb : 0 < b) (ha : 0 < a) (q : ℝ) :
    IntegrableOn (fun t : ℝ => t^q * exp (-(b*t)-a/t)) (Ioi 0) := by
  have hF : Measurable (fun t : ℝ => t^q * exp (-(b*t)-a/t)) := by fun_prop
  have hS : IntegrableOn (fun t : ℝ => t^q * exp (-(b*t)-a/t)) (Ioc 0 1) := by
    have hI := UV.FurtherBoundaryCollar.stretched_exponential_integrableOn (T := 1) (a := 1) (show (0:ℝ)<1 by norm_num) ha (-q)
    apply hI.mono' hF.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_of_nonneg (mul_nonneg (rpow_nonneg ht.1.le _) (exp_pos _).le), neg_neg, rpow_neg_one]
    apply mul_le_mul_of_nonneg_left (exp_le_exp.2 _) (rpow_nonneg ht.1.le _)
    have hbt := mul_nonneg hb.le ht.1.le
    rw [div_eq_mul_inv, neg_mul]
    linarith
  let p := max 0 q
  have hp : 0 ≤ p := le_max_left _ _
  have hG : IntegrableOn (fun t : ℝ => exp (-t) * t^p) (Ioi 0) := by
    have h := GammaIntegral_convergent (show 0 < p+1 by positivity)
    simpa only [add_sub_cancel_right] using h
  have hGb : IntegrableOn ((fun t : ℝ => exp (-(b*t)) * (b*t)^p)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff (fun t : ℝ => exp (-t) * t^p) 0 hb).2 (by simpa using hG)
  have hG' : IntegrableOn (fun t : ℝ => exp (-(b*t)) * t^p) (Ioi 0) := by
    refine IntegrableOn.congr_fun (hGb.const_mul ((b^p)⁻¹)) (fun t ht => ?_) measurableSet_Ioi
    rw [mul_rpow hb.le ht.le]
    field_simp [(rpow_pos_of_pos hb p).ne']
  have hL : IntegrableOn (fun t : ℝ => t^q * exp (-(b*t)-a/t)) (Ioi 1) := by
    apply (hG'.mono_set (Ioi_subset_Ioi zero_le_one)).mono' hF.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht₀ : 0 < t := zero_lt_one.trans ht
    rw [Real.norm_of_nonneg (mul_nonneg (rpow_nonneg ht₀.le _) (exp_pos _).le), mul_comm (t^q)]
    exact mul_le_mul (exp_le_exp.2 (sub_le_self _ (div_nonneg ha.le ht₀.le)))
      (rpow_le_rpow_of_exponent_le ht.le (le_max_right _ _)) (rpow_nonneg ht₀.le _) (exp_pos _).le
  have hsets : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext t
    simp only [mem_union, mem_Ioc,mem_Ioi]
    exact ⟨fun h => h.elim And.left (zero_lt_one.trans ·),fun h =>
      (le_or_gt t 1).elim (fun hh => Or.inl ⟨h,hh⟩) Or.inr⟩
  rw [← hsets]
  exact hS.union hL

private theorem integer_exp_weight_summable {c : ℝ} (hc : 0 < c) (d : ℕ) :
    Summable (fun w : ℤ => |(w:ℝ)|^d * exp (-(c * |(w:ℝ)|))) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor <;> simpa using Real.summable_pow_mul_exp_neg_nat_mul d hc

private theorem nonzero_winding_time_bound {b a q t : ℝ} (hb : 0 < b) (ha : 0 < a) (ht : 0 < t)
    {w : ℤ} (hw : w ≠ 0) (d : ℕ) :
    t^q * (|(w:ℝ)|^d * exp (-(b*t)-a*(w:ℝ)^2/t)) ≤
      (t^q * exp (-(b/2*t)-(a/2)/t)) *
        (|(w:ℝ)|^d * exp (-(sqrt (a*b) * |(w:ℝ)|))) := by
  have hW : (1:ℝ) ≤ |(w:ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast (Int.add_one_le_iff.mpr (abs_pos.mpr hw) : (0:ℤ) + 1 ≤ |w|)
  have h₁ : sqrt (a*b) * |(w:ℝ)| ≤ b/2*t + (a/2)*(w:ℝ)^2/t := by
    have hgap := sq_nonneg (sqrt b*t-sqrt a*|(w:ℝ)|)
    rw [sub_sq, mul_pow, mul_pow, sq_sqrt hb.le, sq_sqrt ha.le, sq_abs] at hgap
    have hAB : sqrt b * sqrt a = sqrt (a*b) := by rw [sqrt_mul ha.le,mul_comm]
    have ht' := (le_div_iff₀ ht).2 (show (sqrt (a*b) * |(w:ℝ)| - b/2*t)*t ≤ (a/2)*(w:ℝ)^2 by
      calc
        _ = (2*(sqrt b*t)*(sqrt a*|(w:ℝ)|)-b*t^2)/2 := by rw [← hAB]; ring
        _ ≤ _ := by linarith)
    linarith
  have h₂ : (a/2)/t ≤ (a/2)*(w:ℝ)^2/t := by
    apply div_le_div_of_nonneg_right _ ht.le
    have hw₂ : (1:ℝ) ≤ (w:ℝ)^2 := by rw [← sq_abs (w:ℝ)]; nlinarith
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hw₂ (show 0 ≤ a/2 by positivity)
  calc
    _ = (t^q * |(w:ℝ)|^d) * exp (-(b*t)-a*(w:ℝ)^2/t) := by ring
    _ ≤ (t^q * |(w:ℝ)|^d) * exp ((-(b/2*t)-(a/2)/t) - sqrt (a*b)*|(w:ℝ)|) := by
      apply mul_le_mul_of_nonneg_left (exp_le_exp.2 _) (by positivity)
      have ht'' : b*t = 2*(b/2*t) := by ring
      have hw'' : a*(w:ℝ)^2/t = 2*((a/2)*(w:ℝ)^2/t) := by ring
      linarith only [h₁,h₂,ht'',hw'']
    _ = _ := by rw [show (-(b/2*t)-(a/2)/t) - sqrt (a*b)*|(w:ℝ)| =
        (-(b/2*t)-(a/2)/t) + -(sqrt (a*b)*|(w:ℝ)|) by ring, exp_add]; ring

/-- Joint absolute integrability of the normal winding sum with an
arbitrary fixed real degree in proper time and any number of angular
derivatives. The zero mode is excluded before integration. -/
theorem nonzero_winding_proper_time {b a : ℝ} (hb : 0 < b) (ha : 0 < a) (q : ℝ) (d : ℕ) :
    (∑' w : ℤ, ∫⁻ t in Ioi (0:ℝ), if w = 0 then 0 else
      ENNReal.ofReal (t^q * (|(w:ℝ)|^d * exp (-(b*t)-a*(w:ℝ)^2/t)))) < ⊤ := by
  let F (t : ℝ) := t^q * exp (-(b/2*t)-(a/2)/t)
  let W (w : ℤ) := |(w:ℝ)|^d * exp (-(sqrt (a*b)*|(w:ℝ)|))
  have hfI : IntegrableOn F (Ioi 0) := paired_time_integrable (half_pos hb) (half_pos ha) q
  have hfM : Measurable F := by unfold F; fun_prop
  have hfN : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioi 0)), 0 ≤ F t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (rpow_nonneg ht.le _) (exp_pos _).le
  have hA : (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (F t)) < ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hfI hfN]
    exact ENNReal.ofReal_lt_top
  have hB : (∑' w, ENNReal.ofReal (W w)) < ⊤ :=
    (integer_exp_weight_summable (show 0 < sqrt (a*b) by positivity) d).tsum_ofReal_lt_top
  apply lt_of_le_of_lt (b := (∑' w, ENNReal.ofReal (W w)) * ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (F t))
  · rw [← ENNReal.tsum_mul_right]
    apply ENNReal.tsum_le_tsum
    intro w
    rw [← lintegral_const_mul _ (show Measurable (fun t => ENNReal.ofReal (F t)) from ENNReal.measurable_ofReal.comp hfM)]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    by_cases hw : w = 0
    · simp [hw]
    · rw [if_neg hw, ← ENNReal.ofReal_mul (by dsimp [W]; positivity), mul_comm (W w)]
      exact ENNReal.ofReal_le_ofReal (nonzero_winding_time_bound (q := q) hb ha ht hw d)
  · exact ENNReal.mul_lt_top hB hA

end UV.ExtendNativeHolonomy
