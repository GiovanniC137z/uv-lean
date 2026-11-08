import UV.GlobalConvergence
import UV.AnalyticScalar

/-! Exact Gaussian integration for two actual translated scalar lines. -/

noncomputable section
open MeasureTheory Real
open scoped InnerProductSpace

namespace UV

theorem scalar_gaussian_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun q : ScalarMomentum => Real.exp (-b * ‖q‖ ^ 2)) := by
  simpa only [sub_self, Real.rpow_zero, one_mul] using
    (massless_gaussian_integrable (d := 2) (by norm_num) hb)

theorem scalar_gaussian_integral {b : ℝ} (hb : 0 < b) :
    (∫ q : ScalarMomentum, Real.exp (-b * ‖q‖ ^ 2)) = Real.pi ^ 2 / b ^ 2 := by
  have he := massless_gaussian_integral (d := 2) (by norm_num) hb
  norm_num [Real.Gamma_nat_eq_factorial] at he
  simpa only [neg_mul, div_eq_mul_inv] using he

theorem two_line_complete_square {w₁ w₂ : ℝ} (hw : w₁ + w₂ ≠ 0)
    (P q : ScalarMomentum) :
    w₁ * ‖q‖ ^ 2 + w₂ * ‖q + P‖ ^ 2 =
      (w₁ + w₂) * ‖q + (w₂ / (w₁ + w₂)) • P‖ ^ 2 +
        (w₁ * w₂ / (w₁ + w₂)) * ‖P‖ ^ 2 := by
  simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_smul_right]
  field_simp
  ring

theorem two_line_gaussian_factor {w₁ w₂ : ℝ} (hw : w₁ + w₂ ≠ 0)
    (P q : ScalarMomentum) :
    Real.exp (-w₁ * ‖q‖ ^ 2 - w₂ * ‖q + P‖ ^ 2) =
      Real.exp (-(w₁ * w₂ / (w₁ + w₂)) * ‖P‖ ^ 2) *
        Real.exp (-(w₁ + w₂) * ‖q + (w₂ / (w₁ + w₂)) • P‖ ^ 2) := by
  rw [← Real.exp_add]
  congr 1
  linarith [two_line_complete_square hw P q]

theorem two_line_gaussian_integrable {w₁ w₂ : ℝ} (hw : 0 < w₁ + w₂)
    (P : ScalarMomentum) :
    Integrable (fun q : ScalarMomentum => Real.exp (-w₁ * ‖q‖ ^ 2 - w₂ * ‖q + P‖ ^ 2)) := by
  simp_rw [two_line_gaussian_factor hw.ne' P]
  apply Integrable.const_mul
  exact (measurePreserving_add_right volume ((w₂ / (w₁ + w₂)) • P)).integrable_comp_of_integrable
    (scalar_gaussian_integrable hw)

theorem two_line_gaussian_integral {w₁ w₂ : ℝ} (hw : 0 < w₁ + w₂)
    (P : ScalarMomentum) :
    (∫ q : ScalarMomentum, Real.exp (-w₁ * ‖q‖ ^ 2 - w₂ * ‖q + P‖ ^ 2)) =
      Real.pi ^ 2 / (w₁ + w₂) ^ 2 *
        Real.exp (-(w₁ * w₂ / (w₁ + w₂)) * ‖P‖ ^ 2) := by
  simp_rw [two_line_gaussian_factor hw.ne' P]
  rw [integral_const_mul]
  have ht := integral_add_right_eq_self (μ := volume)
    (fun q : ScalarMomentum => Real.exp (-(w₁ + w₂) * ‖q‖ ^ 2)) ((w₂ / (w₁ + w₂)) • P)
  rw [ht, scalar_gaussian_integral hw]
  ring

theorem two_line_gaussian_lintegral {w₁ w₂ : ℝ} (hw : 0 < w₁ + w₂)
    (P : ScalarMomentum) :
    (∫⁻ q : ScalarMomentum, ENNReal.ofReal
      (Real.exp (-w₁ * ‖q‖ ^ 2 - w₂ * ‖q + P‖ ^ 2))) =
      ENNReal.ofReal (Real.pi ^ 2 / (w₁ + w₂) ^ 2 *
        Real.exp (-(w₁ * w₂ / (w₁ + w₂)) * ‖P‖ ^ 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (two_line_gaussian_integrable hw P)
    (Filter.Eventually.of_forall fun q => (Real.exp_pos _).le), two_line_gaussian_integral hw P]

end UV
