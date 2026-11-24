import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Tactic

/-! The common depth is sampled once for a whole graph or vacuum. A
positive exponential moment of inverse depth cubed absorbs both the absolute
matter vacuum and all finite powers from marked components. -/

noncomputable section
open Real MeasureTheory Set
namespace UV.SectorPlane

/-- A bound uniform on the entire positive depth interval, including the tip. -/
theorem ordered_torus_depth_domination {c C r : ℝ} (hc : 0 < c)
    (hr : 0 < r) (hr₁ : r ≤ 1) (n : ℕ) :
    (1+r⁻¹)^n * exp (C*(1+(sqrt r)⁻¹^3)) ≤
      exp (C+((n:ℝ)+C)^2/(4*c)) * exp (c/r^3) := by
  let u := (sqrt r)⁻¹
  have hu : 1 ≤ u := by
    apply (one_le_inv₀ (sqrt_pos.mpr hr)).mpr
    exact sqrt_le_one.mpr hr₁
  have hu' : 0 ≤ u := zero_le_one.trans hu
  have huu : r⁻¹ = u^2 := by rw [← Real.sq_sqrt hr.le,inv_pow]
  have hu₆ : c/r^3 = c*(u^3)^2 := by rw [div_eq_mul_inv,← inv_pow,huu]; ring
  have hexp : 1+r⁻¹ ≤ exp (u^3) := by
    rw [huu]
    exact (add_le_add_left (pow_le_pow_right₀ hu (by decide : 2 ≤ 3)) _).trans (add_one_le_exp _ |>.trans_eq' (add_comm _ _))
  have hs : ((n:ℝ)+C)*u^3 ≤ c*(u^3)^2+((n:ℝ)+C)^2/(4*c) := by
    have hq : (((n:ℝ)+C)*u^3-c*(u^3)^2)*(4*c) ≤ ((n:ℝ)+C)^2 := by
      nlinarith only [sq_nonneg (2*c*u^3-((n:ℝ)+C))]
    have he := (le_div_iff₀ (show 0 < 4*c by positivity)).2 hq
    linarith
  calc
    _ ≤ exp (u^3)^n * exp (C*(1+u^3)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hexp _) (exp_pos _).le
    _ = exp ((n:ℝ)*u^3+C*(1+u^3)) := by rw [← exp_nat_mul, ← exp_add]
    _ ≤ _ := by rw [←exp_add,exp_le_exp,hu₆]; linarith

/-- Absolute marked coefficients remain integrable after multiplication by the
unexpanded vacuum bound and integration over one common depth. -/
theorem ordered_torus_joint_depth_integrable (μ : Measure ℝ) {c C : ℝ} (hc : 0 < c)
    (hs : ∀ᵐ r ∂μ, r ∈ Ioc (0:ℝ) 1) (hμ : Integrable (fun r : ℝ => exp (c/r^3)) μ)
    (n : ℕ) (f : ℝ → ℂ) (hf : AEStronglyMeasurable f μ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᵐ r ∂μ, ‖f r‖ ≤ B*((1+r⁻¹)^n*exp (C*(1+(sqrt r)⁻¹^3)))) : Integrable f μ := by
  apply ((hμ.const_mul (exp (C+((n:ℝ)+C)^2/(4*c)))).const_mul B).mono' hf
  filter_upwards [hs,hb] with r hr h
  exact h.trans (mul_le_mul_of_nonneg_left (ordered_torus_depth_domination hc hr.1 hr.2 n) hB)

end UV.SectorPlane
