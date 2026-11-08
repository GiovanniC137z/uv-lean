import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

noncomputable section
open MeasureTheory Set

namespace UV

theorem translated_log_integrable (r : ℝ) :
    IntegrableOn (fun x : ℝ => Real.log (x - r)) (Icc (0 : ℝ) 1) := by
  have hi := (intervalIntegral.intervalIntegrable_log' (a := -r) (b := 1 - r)).comp_sub_right r
  have hh : IntervalIntegrable (fun x : ℝ => Real.log (x - r)) volume 0 1 := by
    simpa only [neg_add_cancel, sub_add_cancel] using hi
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hh

theorem translated_log_integral (r : ℝ) :
    (∫ x in Icc (0 : ℝ) 1, Real.log (x - r)) =
      (1 - r) * Real.log (1 - r) + r * Real.log r - 1 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_comp_sub_right, integral_log]
  simp only [zero_sub, Real.log_neg_eq_log]
  ring

theorem mul_log_ge_neg_one {x : ℝ} (hx : 0 ≤ x) : -1 ≤ x * Real.log x := by
  by_cases hzero : x = 0
  · simp [hzero]
  · have hh := mul_le_mul_of_nonneg_left (Real.neg_inv_le_log hx) hx
    have he : x * (-x⁻¹) = -1 := by field_simp
    linarith

theorem translated_log_abs_integrable (r : ℝ) :
    IntegrableOn (fun x : ℝ => |Real.log (x - r)|) (Icc (0 : ℝ) 1) :=
  (translated_log_integrable r).abs

/-- Uniform integrable logarithmic singularity bound for a root anywhere in
the closed Feynman parameter interval, including its endpoints. -/
theorem translated_log_abs_integral_le {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    (∫ x in Icc (0 : ℝ) 1, |Real.log (x - r)|) ≤ 3 := by
  have he : (∫ x in Icc (0 : ℝ) 1, |Real.log (x - r)|) =
      -(∫ x in Icc (0 : ℝ) 1, Real.log (x - r)) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    have hd : |x - r| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1, hr.2], by linarith [hx.2, hr.1]⟩
    have hn : Real.log (x - r) ≤ 0 := by
      rw [← Real.log_abs]
      exact Real.log_nonpos (abs_nonneg _) hd
    exact abs_of_nonpos hn
  rw [he, translated_log_integral]
  linarith [mul_log_ge_neg_one hr.1, mul_log_ge_neg_one (sub_nonneg.mpr hr.2)]

end UV
