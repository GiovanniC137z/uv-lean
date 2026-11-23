import UV.FormalBRST
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Basic

/-! Coefficient bounds for the last (normalized connected logarithm) step of
the constitutive quotient theorem. Each source order can have its own graph
integration space. The common strictly positive body is kept explicit. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace UV

/-- A finite Cauchy-product majorant for fixed degree and fixed power. -/
def omegaPowerBudget (b : ℕ → ℝ) (d k : ℕ) : ℝ :=
  ∑ l ∈ Finset.finsuppAntidiag (Finset.range k) d, ∏ i ∈ Finset.range k, b (l i)

private theorem coeff_pow_le_budget (f : PowerSeries ℂ) (b : ℕ → ℝ)
    (h : ∀ n, ‖PowerSeries.coeff n f‖ ≤ b n) (d k : ℕ) :
    ‖PowerSeries.coeff d (f^k)‖ ≤ omegaPowerBudget b d k := by
  rw [PowerSeries.coeff_pow]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro l hl
  rw [norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => h _)

/-- Normalize every nonvacuum derivative by the same vacuum denominator. -/
def omegaNormalizedPartition (v : ℝ) (a : ℕ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n => if n = 0 then 1 else a n / (v : ℂ))

theorem omega_normalized_partition_body (v : ℝ) (a : ℕ → ℂ) :
    PowerSeries.constantCoeff (omegaNormalizedPartition v a) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [omegaNormalizedPartition]

/-- Finite coefficient bound with the exact logarithm weights. Vacuum
normalization makes the zero-degree factor vanish in every Cauchy product. -/
theorem omega_normalized_connected_bound {v : ℝ} (hv : 0 < v) (a : ℕ → ℂ)
    (b : ℕ → ℝ) (hb : ∀ n, 0 < n → ‖a n‖ ≤ b n) (d : ℕ) :
    ‖PowerSeries.coeff d (formalConnectedLog (omegaNormalizedPartition v a))‖ ≤
      ∑ k ∈ Finset.range (d+1), ‖((-1:ℚ)^k)/(k+1:ℚ)‖ *
        omegaPowerBudget (fun n => if n = 0 then 0 else b n / v) d (k+1) := by
  have h (n : ℕ) : ‖PowerSeries.coeff n (omegaNormalizedPartition v a - 1)‖ ≤
      (if n = 0 then 0 else b n / v) := by
    cases n with
    | zero => simp [omegaNormalizedPartition, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    | succ n =>
      simpa [omegaNormalizedPartition, norm_div, abs_of_pos hv]
        using div_le_div_of_nonneg_right (hb (n+1) (Nat.succ_pos n)) hv.le
  rw [formalConnectedLog_coeff]
  simp only [finiteLogPolynomial, map_sum, PowerSeries.coeff_smul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (coeff_pow_le_budget _ _ h d (k+1)) (norm_nonneg _)

/-- Integrated source graphs on different spaces supply the coefficient
majorants. Absolute integrability is imposed order by order and the bound
retains the shared denominator and the finite convolution combinatorics. -/
theorem omega_connected_graph_integral_bound {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    (G : ∀ n, Ω n → ℂ) (g : ∀ n, Ω n → ℝ)
    (hG : ∀ n, 0 < n → AEStronglyMeasurable (G n) (μ n))
    (hg : ∀ n, 0 < n → Integrable (g n) (μ n))
    (hdom : ∀ n, 0 < n → ∀ᵐ x ∂μ n, ‖G n x‖ ≤ g n x)
    {v : ℝ} (hv : 0 < v) (d : ℕ) :
    ‖PowerSeries.coeff d (formalConnectedLog
        (omegaNormalizedPartition v (fun n => ∫ x, G n x ∂μ n)))‖ ≤
      ∑ k ∈ Finset.range (d+1), ‖((-1:ℚ)^k)/(k+1:ℚ)‖ *
        omegaPowerBudget (fun n => if n = 0 then 0 else (∫ x, g n x ∂μ n) / v) d (k+1) := by
  apply omega_normalized_connected_bound hv
  intro n hn
  have hi := (hg n hn).mono' (hG n hn) (hdom n hn)
  exact (norm_integral_le_integral_norm _).trans (integral_mono_ae hi.norm (hg n hn) (hdom n hn))

end UV
