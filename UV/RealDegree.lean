import UV.Convergence
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Real numerator degrees and the quadratic residual analytic estimate.
This removes the natural-degree restriction from the analytic majorant step. -/

noncomputable section
open MeasureTheory

namespace UV

theorem rpow_le_one_add_nat_power {x D : ℝ} (hx : 0 ≤ x) (hD : 0 ≤ D)
    (n : ℕ) (hn : D ≤ n) : x ^ D ≤ 1 + x ^ n := by
  by_cases hx1 : x ≤ 1
  · have hp := Real.rpow_le_one hx hx1 hD
    have hpow := pow_nonneg hx n
    linarith
  · have hp := Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge hx1)) hn
    rw [Real.rpow_natCast] at hp
    linarith

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {μ : Measure E} [μ.HasTemperateGrowth]

theorem integrable_real_degree_exp {a D : ℝ} (ha : 0 < a) (hD : 0 ≤ D) :
    Integrable (fun x : E => (1 + ‖x‖ ^ D) * Real.exp (-(a * ‖x‖))) μ := by
  let n := ⌈D⌉₊
  have h := integrable_polynomial_exp (μ := μ) ha n
  refine (h.const_mul 2).mono' (by fun_prop) ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (by positivity)]
  have hp := rpow_le_one_add_nat_power (norm_nonneg x) hD n (Nat.le_ceil D)
  have he := Real.exp_nonneg (-(a * ‖x‖))
  have hn := pow_nonneg (norm_nonneg x) n
  nlinarith [mul_le_mul_of_nonneg_right hp he]

theorem integrable_real_degree_gaussian {a D : ℝ} (ha : 0 < a) (hD : 0 ≤ D) :
    Integrable (fun x : E => (1 + ‖x‖ ^ D) * Real.exp (-(a * ‖x‖ ^ 2))) μ := by
  have h := integrable_real_degree_exp (μ := μ) ha hD
  refine (h.const_mul (Real.exp (a / 4))).mono' (by fun_prop) ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (by positivity)]
  have hs : ‖x‖ - 1 / 4 ≤ ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 1 / 2)]
  have he : Real.exp (-(a * ‖x‖ ^ 2)) ≤
      Real.exp (a / 4) * Real.exp (-(a * ‖x‖)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hs ha.le]
  have hp : 0 ≤ 1 + ‖x‖ ^ D := by positivity
  nlinarith [mul_le_mul_of_nonneg_left he hp]

theorem residual_linear_real_degree_convergence {F P : Type*}
    [NormedAddCommGroup F] {f : P → E → F} {ψ : P → E → ℝ}
    {a B C D : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ∀ p, AEStronglyMeasurable (f p) μ)
    (hb : ∀ p x, ‖f p x‖ ≤ C * (1 + ‖x‖ ^ D) * Real.exp (-ψ p x))
    (hc : ∀ p x, a * ‖x‖ - B ≤ ψ p x) : ∀ p, Integrable (f p) μ := by
  intro p
  refine ((integrable_real_degree_exp (μ := μ) ha hD).const_mul
    (C * Real.exp B)).mono' (hf p) ?_
  filter_upwards with x
  calc
    ‖f p x‖ ≤ C * (1 + ‖x‖ ^ D) * Real.exp (-ψ p x) := hb p x
    _ ≤ C * (1 + ‖x‖ ^ D) * Real.exp (B - a * ‖x‖) := by
      gcongr
      linarith [hc p x]
    _ = _ := by rw [Real.exp_sub, Real.exp_neg]; ring

theorem residual_quadratic_real_degree_convergence {F P : Type*}
    [NormedAddCommGroup F] {f : P → E → F} {ψ : P → E → ℝ}
    {a B C D : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ∀ p, AEStronglyMeasurable (f p) μ)
    (hb : ∀ p x, ‖f p x‖ ≤ C * (1 + ‖x‖ ^ D) * Real.exp (-ψ p x))
    (hc : ∀ p x, a * ‖x‖ ^ 2 - B ≤ ψ p x) : ∀ p, Integrable (f p) μ := by
  intro p
  refine ((integrable_real_degree_gaussian (μ := μ) ha hD).const_mul
    (C * Real.exp B)).mono' (hf p) ?_
  filter_upwards with x
  calc
    ‖f p x‖ ≤ C * (1 + ‖x‖ ^ D) * Real.exp (-ψ p x) := hb p x
    _ ≤ C * (1 + ‖x‖ ^ D) * Real.exp (B - a * ‖x‖ ^ 2) := by
      gcongr
      linarith [hc p x]
    _ = _ := by rw [Real.exp_sub, Real.exp_neg]; ring

/-- Direct specialization to the paper's 4L-dimensional loop-momentum space. -/
theorem euclidean_loop_real_degree_integrable (L : ℕ) {a D : ℝ}
    (ha : 0 < a) (hD : 0 ≤ D) :
    Integrable (fun k : EuclideanSpace ℝ (Fin (4 * L)) =>
      (1 + ‖k‖ ^ D) * Real.exp (-(a * ‖k‖))) :=
  integrable_real_degree_exp ha hD

end UV
