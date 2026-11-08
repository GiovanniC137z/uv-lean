import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! Finite signed exponential remainders, derived by the mean-value theorem.
No exchange of an infinite series with an integral is involved. -/

noncomputable section
open Set

namespace UV

theorem negative_exp_iteratedDeriv (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun t : ℝ => Real.exp (-t)) x = (-1 : ℝ) ^ n * Real.exp (-x) := by
  simpa only [neg_one_mul] using congrFun (iteratedDeriv_exp_const_mul n (-1)) x

theorem negative_exp_taylorWithin {x : ℝ} (hx : 0 < x) (N : ℕ) :
    taylorWithinEval (fun t : ℝ => Real.exp (-t)) N (Icc 0 x) 0 x =
      ∑ n ∈ Finset.range (N + 1), (-x) ^ n / (n.factorial : ℝ) := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro n _
  have hc : ContDiffAt ℝ n (fun t : ℝ => Real.exp (-t)) 0 := by fun_prop
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx) hc ⟨le_rfl, hx.le⟩,
    negative_exp_iteratedDeriv]
  simp only [neg_zero, Real.exp_zero, mul_one, sub_zero, smul_eq_mul, div_eq_mul_inv]
  rw [neg_pow x n]
  ring

theorem exp_neg_signed_taylor_remainder {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    0 ≤ (-1 : ℝ) ^ (N + 1) *
        (Real.exp (-x) - ∑ n ∈ Finset.range (N + 1), (-x) ^ n / (n.factorial : ℝ)) ∧
      (-1 : ℝ) ^ (N + 1) *
        (Real.exp (-x) - ∑ n ∈ Finset.range (N + 1), (-x) ^ n / (n.factorial : ℝ)) ≤
          x ^ (N + 1) / ((N + 1).factorial : ℝ) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [Finset.sum_range_succ']
  have hc : ContDiffOn ℝ (N + 1) (fun t : ℝ => Real.exp (-t)) (Icc 0 x) := by fun_prop
  obtain ⟨c, hc', he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hx hc
  rw [negative_exp_taylorWithin hx N, negative_exp_iteratedDeriv, sub_zero] at he
  have hsign : (-1 : ℝ) ^ (N + 1) * (-1 : ℝ) ^ (N + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  have hr : (-1 : ℝ) ^ (N + 1) *
        (Real.exp (-x) - ∑ n ∈ Finset.range (N + 1), (-x) ^ n / (n.factorial : ℝ)) =
      Real.exp (-c) * (x ^ (N + 1) / ((N + 1).factorial : ℝ)) := by
    rw [he]
    calc
      _ = ((-1 : ℝ) ^ (N + 1) * (-1 : ℝ) ^ (N + 1)) *
          (Real.exp (-c) * (x ^ (N + 1) / ((N + 1).factorial : ℝ))) := by ring
      _ = _ := by rw [hsign, one_mul]
  rw [hr]
  constructor
  · positivity
  · have hce : Real.exp (-c) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hc'.1])
    exact (mul_le_mul_of_nonneg_right hce (by positivity)).trans_eq (one_mul _)

end UV
