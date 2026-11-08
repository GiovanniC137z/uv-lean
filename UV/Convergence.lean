import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Pi
import UV.Kernel

/-! Checked analytic core of prop:residual-coercivity and the final selected-line
product step. Routing rank, line moments and vertex estimates remain separate
obligations; none is replaced with an axiom here. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace UV

theorem pow_mul_exp_neg_le {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (n : ℕ) :
    x ^ n * Real.exp (-(a * x)) ≤ (n.factorial : ℝ) / a ^ n := by
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h := (div_le_iff₀ hfac).mp
    (Real.pow_div_factorial_le_exp (a * x) (mul_nonneg ha.le hx) n)
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_nonneg (-(a * x)))
  have hc : Real.exp (a * x) * Real.exp (-(a * x)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hs : (a * x) ^ n * Real.exp (-(a * x)) ≤ (n.factorial : ℝ) := by
    calc
      _ ≤ (Real.exp (a * x) * (n.factorial : ℝ)) * Real.exp (-(a * x)) := hm
      _ = (n.factorial : ℝ) := by nlinarith [hc]
  apply (le_div_iff₀ (pow_pos ha n)).mpr
  simpa only [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hs

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {μ : Measure E} [μ.HasTemperateGrowth]

/-- Polynomial times strict exponential decay is integrable in any dimension
    for a measure of temperate growth, including finite-dimensional Lebesgue measure. -/
theorem integrable_norm_pow_exp {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Integrable (fun x : E => ‖x‖ ^ n * Real.exp (-(a * ‖x‖))) μ := by
  have h := SchwartzMap.integrable_of_le_of_pow_mul_le
    (μ := μ) (f := fun x : E => Real.exp (-(a * ‖x‖))) (k := n)
    (C₁ := 1) (C₂ := ((n + μ.integrablePower).factorial : ℝ) / a ^ (n + μ.integrablePower))
    (fun x => by
      rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ha.le (norm_nonneg x))))
    (fun x => by
      rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact pow_mul_exp_neg_le ha (norm_nonneg x) _)
    (by fun_prop)
  simpa only [Real.norm_of_nonneg (Real.exp_nonneg _)] using h

theorem integrable_polynomial_exp {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Integrable (fun x : E => (1 + ‖x‖ ^ n) * Real.exp (-(a * ‖x‖))) μ := by
  have h0 := integrable_norm_pow_exp (μ := μ) ha 0
  have hn := integrable_norm_pow_exp (μ := μ) ha n
  simpa only [pow_zero, one_mul, add_mul] using h0.add hn

variable {F : Type*} [NormedAddCommGroup F] {P : Type*}

/-- A common complete-graph bound gives absolute convergence, uniformly in the
    external parameter. Measurability of the actual graph is an explicit input. -/
theorem graph_integrable_of_common_bound {f : P → E → F} {a C : ℝ} {n : ℕ}
    (ha : 0 < a) (hf : ∀ p, AEStronglyMeasurable (f p) μ)
    (hbound : ∀ p x, ‖f p x‖ ≤ C * ((1 + ‖x‖ ^ n) * Real.exp (-(a * ‖x‖)))) :
    ∀ p, Integrable (f p) μ := by
  intro p
  exact ((integrable_polynomial_exp (μ := μ) ha n).const_mul C).mono'
    (hf p) (Filter.Eventually.of_forall (hbound p))

theorem uniform_integral_norm_bound {f : P → E → F} {a C : ℝ} {n : ℕ}
    (ha : 0 < a) (hf : ∀ p, AEStronglyMeasurable (f p) μ)
    (hbound : ∀ p x, ‖f p x‖ ≤ C * ((1 + ‖x‖ ^ n) * Real.exp (-(a * ‖x‖)))) :
    ∀ p, (∫ x, ‖f p x‖ ∂μ) ≤
      C * ∫ x : E, (1 + ‖x‖ ^ n) * Real.exp (-(a * ‖x‖)) ∂μ := by
  intro p
  rw [← integral_const_mul]
  exact integral_mono (graph_integrable_of_common_bound ha hf hbound p).norm
    ((integrable_polynomial_exp (μ := μ) ha n).const_mul C)
    (hbound p)

/-- Residual linear damping after the complete vertex growth is accounted for.
    The coercivity inequality can have an external-parameter-independent shift. -/
theorem residual_linear_convergence {f : P → E → F} {ψ : P → E → ℝ}
    {a B C : ℝ} {n : ℕ} (ha : 0 < a) (hC : 0 ≤ C)
    (hf : ∀ p, AEStronglyMeasurable (f p) μ)
    (hvertex : ∀ p x, ‖f p x‖ ≤ C * (1 + ‖x‖ ^ n) * Real.exp (-ψ p x))
    (hcoercive : ∀ p x, a * ‖x‖ - B ≤ ψ p x) :
    ∀ p, Integrable (f p) μ := by
  apply graph_integrable_of_common_bound (C := C * Real.exp B) ha hf
  intro p x
  calc
    ‖f p x‖ ≤ C * (1 + ‖x‖ ^ n) * Real.exp (-ψ p x) := hvertex p x
    _ ≤ C * (1 + ‖x‖ ^ n) * Real.exp (B - a * ‖x‖) := by
      gcongr
      linarith [hcoercive p x]
    _ = (C * Real.exp B) * ((1 + ‖x‖ ^ n) * Real.exp (-(a * ‖x‖))) := by
      rw [Real.exp_sub, Real.exp_neg]
      ring

/-- The final independent-line product step in thm:optimized-selected-lines.
    One-line integrability must be supplied for the actual selected factors. -/
theorem selected_product_integrable {ι X : Type*} [Fintype ι]
    [MeasurableSpace X] {ν : ι → Measure X} [∀ i, SigmaFinite (ν i)]
    {g : ι → X → ℝ} {f : (ι → X) → F}
    (hg : ∀ i, Integrable (g i) (ν i))
    (hf : AEStronglyMeasurable f (Measure.pi ν))
    (hb : ∀ x, ‖f x‖ ≤ ∏ i, g i (x i)) :
    Integrable f (Measure.pi ν) :=
  (Integrable.fintype_prod hg).mono' hf (Filter.Eventually.of_forall hb)

end UV
