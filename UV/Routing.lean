import UV.Convergence

noncomputable section
open scoped BigOperators

namespace UV

variable {E : Type*} [NormedAddCommGroup E]

/-- Signed residuals must use an absolute value in the affine error term. -/
theorem signed_norm_add_lower (h : ℝ) (x r : E) :
    h * ‖x‖ - |h| * ‖r‖ ≤ h * ‖x + r‖ := by
  have hupper := norm_add_le x r
  have hlower : ‖x‖ ≤ ‖x + r‖ + ‖r‖ := by
    calc
      ‖x‖ = ‖(x + r) - r‖ := by simp
      _ ≤ ‖x + r‖ + ‖r‖ := norm_sub_le _ _
  by_cases hh : 0 ≤ h
  · rw [abs_of_nonneg hh]
    nlinarith [mul_le_mul_of_nonneg_left hlower hh]
  · rw [abs_of_neg (lt_of_not_ge hh)]
    nlinarith [mul_le_mul_of_nonpos_left hupper (le_of_lt (lt_of_not_ge hh))]

/-- The signed affine bound in eq:signed-linear-affine-bound, with a supplied
    homogeneous coercivity certificate and uniform routing shift bounds. -/
theorem signed_affine_coercivity {ι K P : Type*} [Fintype ι]
    [NormedAddCommGroup K] (h : ι → ℝ) (T : ι → K → E)
    (R : ι → P → E) (b : ι → ℝ) (γ : ℝ)
    (hc : ∀ k, γ * ‖k‖ ≤ ∑ i, h i * ‖T i k‖)
    (hR : ∀ i p, ‖R i p‖ ≤ b i) (k : K) (p : P) :
    γ * ‖k‖ - ∑ i, |h i| * b i ≤ ∑ i, h i * ‖T i k + R i p‖ := by
  have hb : ∑ i, |h i| * ‖R i p‖ ≤ ∑ i, |h i| * b i := by
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hR i p) (abs_nonneg _))
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => signed_norm_add_lower (h i) (T i k) (R i p))
  rw [Finset.sum_sub_distrib] at hs
  linarith [hc k]

end UV
