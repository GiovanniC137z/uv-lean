import UV.ContinueShellReturnMarks
import UV.ContinueRelativeSoftShape

/-! The Maxwell sewing integral and the unmarked constant Neumann mode
in the scalar polarization of the separable determinant. -/

noncomputable section
open MeasureTheory Set Filter
namespace UV

theorem shell_maxwell_radial_integral {t u : ℝ} (ht : 0 < t) (hu : u ∈ Ioo (0:ℝ) 1) :
    (∫ X in Ioi (0:ℝ), X*Real.exp (-(t*(u*(1-u))*X))) = 1/(t*(u*(1-u)))^2 := by
  have h : 0 < t*(u*(1-u)) := mul_pos ht (mul_pos hu.1 (sub_pos.mpr hu.2))
  simpa [RelativeSoft.expMonomial] using RelativeSoft.exp_monomial_integral h 1

def shellUnmarkedIntegrand (m X : ℝ) (M : ℝ → ℝ) (t u : ℝ) : ℝ :=
  t⁻¹*Real.exp (-(m^2*t))*((u*(1-u))*Real.exp (-(t*(u*(1-u))*X)))*M t

/-- A single unit eigenfunction of zero Neumann energy contributes one to
the trace at every duration. On an interior band of mark fractions this
alone forbids a finite bare scalar polarization at every fixed X ≥ 0. -/
theorem shell_constant_mode_diverges (m : ℝ) {X : ℝ} (hX : 0 ≤ X) (M : ℝ → ℝ)
    (hM : ∀ t ∈ Ioo (0:ℝ) 1, 1 ≤ M t) {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    ¬ IntegrableOn (fun t => shellUnmarkedIntegrand m X M t u) (Ioo (0:ℝ) 1) := by
  let h := u*(1-u)
  have hh : 0 < h := mul_pos hu.1 (sub_pos.mpr hu.2)
  let c := Real.exp (-(m^2))*h*Real.exp (-(h*X))
  have hc : 0 < c := mul_pos (mul_pos (Real.exp_pos _) hh) (Real.exp_pos _)
  intro hi
  have hj : IntegrableOn (fun t : ℝ => t^(-1:ℝ)) (Ioo 0 1) := by
    apply (hi.const_mul c⁻¹).mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.rpow_neg_one,Real.norm_of_nonneg (inv_nonneg.mpr ht.1.le)]
    have h₁ : Real.exp (-(m^2)) ≤ Real.exp (-(m^2*t)) := Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sq_nonneg m) (sub_nonneg.mpr ht.2.le)])
    have h₂ : Real.exp (-(h*X)) ≤ Real.exp (-(t*h*X)) := Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (mul_nonneg hh.le hX) (sub_nonneg.mpr ht.2.le)])
    have hp := mul_le_mul (mul_le_mul_of_nonneg_right h₁ hh.le) h₂ (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le hh.le)
    have hmt := mul_le_mul_of_nonneg_right hp (inv_nonneg.mpr ht.1.le)
    have hpos : 0 ≤ t⁻¹*Real.exp (-(m^2*t))*(h*Real.exp (-(t*h*X))) :=
      mul_nonneg (mul_nonneg (inv_nonneg.mpr ht.1.le) (Real.exp_pos _).le) (mul_nonneg hh.le (Real.exp_pos _).le)
    have hM' := mul_le_mul_of_nonneg_left (hM t ht) hpos
    rw [mul_one] at hM'
    have hl : c*t⁻¹ ≤ shellUnmarkedIntegrand m X M t u := by
      apply LE.le.trans _ hM'
      convert hmt using 1; dsimp [c]; ring
    simpa [hc.ne'] using mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hc.le)
  exact (lt_irrefl (-1:ℝ)) ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mp hj)

end UV
