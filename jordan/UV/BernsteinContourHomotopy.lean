import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue

/-! Lean 4.32.2 compatibility port: unfold Bernstein coefficient maps explicitly.

Smooth Bernstein curves and exact preservation of Lipschitz constants.
The derivative is derived from the actual Bernstein polynomial identities;
no approximation or derivative bound is supplied as a premise. -/

noncomputable section
open Set
open scoped BigOperators unitInterval Topology ContDiff NNReal

namespace UV

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def bernsteinVectorPolynomial (n : ℕ) (v : ℕ → E) (t : ℝ) : E :=
  ∑ k ∈ Finset.range (n+1), (bernsteinPolynomial ℝ n k).eval t • v k

def bernsteinCurveExtension (n : ℕ) (f : ℝ → E) : ℝ → E :=
  bernsteinVectorPolynomial n (fun k => f ((k : ℝ)/n))

theorem bernsteinVectorPolynomial_smooth (n : ℕ) (v : ℕ → E) :
    ContDiff ℝ ∞ (bernsteinVectorPolynomial n v) := by
  unfold bernsteinVectorPolynomial
  apply ContDiff.sum
  intro k _
  apply ContDiff.smul _ contDiff_const
  simp only [bernsteinPolynomial, Polynomial.eval_mul, Polynomial.eval_natCast,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]
  fun_prop

theorem bernsteinCurveExtension_smooth (n : ℕ) (f : ℝ → E) :
    ContDiff ℝ ∞ (bernsteinCurveExtension n f) := bernsteinVectorPolynomial_smooth n _

/-- The global smooth polynomial is exactly the library's continuous-map
Bernstein approximation on the unit interval. -/
theorem bernsteinCurveExtension_eq_approximation (n : ℕ) (f : ℝ → E) (g : C(I, E))
    (hext : ∀ t : I, f t = g t) (t : I) :
    bernsteinCurveExtension n f t = bernsteinApproximation n g t := by
  rw [bernsteinCurveExtension, bernsteinVectorPolynomial, Finset.sum_range,
    bernsteinApproximation.apply]
  apply Finset.sum_congr rfl
  intro k _
  change (bernsteinPolynomial ℝ n k).eval (t : ℝ) • f (bernstein.z k : ℝ) =
    bernstein n k t • g (bernstein.z k)
  rw [hext]
  rfl

theorem bernsteinCurveExtension_zero (n : ℕ) (f : ℝ → E) :
    bernsteinCurveExtension n f 0 = f 0 := by
  simp [bernsteinCurveExtension, bernsteinVectorPolynomial, bernsteinPolynomial.eval_at_0]

theorem bernsteinCurveExtension_one {n : ℕ} (hn : n ≠ 0) (f : ℝ → E) :
    bernsteinCurveExtension n f 1 = f 1 := by
  simp [bernsteinCurveExtension, bernsteinVectorPolynomial, bernsteinPolynomial.eval_at_1, hn]

/-- The actual global smooth polynomials converge uniformly on the unit
interval. This is the library Bernstein theorem with its restriction
identity proved above, rather than an approximation admission premise. -/
theorem bernsteinCurveExtension_uniform_error (f : ℝ → E) (g : C(I, E))
    (hext : ∀ t : I, f t = g t) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ t ∈ Icc (0:ℝ) 1,
      ‖bernsteinCurveExtension n f t-f t‖ < ε := by
  have h := (bernsteinApproximation_uniform g).eventually (Metric.ball_mem_nhds g hε)
  filter_upwards [h] with n hn t ht
  let x : I := ⟨t, ht⟩
  have hx := (ContinuousMap.dist_apply_le_dist (f := bernsteinApproximation n g) (g := g) x).trans_lt hn
  rw [← bernsteinCurveExtension_eq_approximation n f g hext x, ← hext x, dist_eq_norm] at hx
  exact hx

theorem bernsteinVectorPolynomial_derivative_sum (n : ℕ) (v : ℕ → E) (t : ℝ) :
    (∑ k ∈ Finset.range (n+2), (bernsteinPolynomial ℝ (n+1) k).derivative.eval t • v k) =
      (n+1 : ℝ) • ∑ k ∈ Finset.range (n+1),
        (bernsteinPolynomial ℝ n k).eval t • (v (k+1)-v k) := by
  let b : ℕ → ℝ := fun k => (bernsteinPolynomial ℝ n k).eval t
  have hshift : (∑ k ∈ Finset.range (n+1), b (k+1) • v (k+1)) =
      (∑ k ∈ Finset.range (n+1), b k • v k) - b 0 • v 0 := by
    have hh := Finset.sum_range_succ' (fun k => b k • v k) (n+1)
    rw [Finset.sum_range_succ] at hh
    have hlast : b (n+1) = 0 := by
      dsimp [b]
      rw [bernsteinPolynomial.eq_zero_of_lt ℝ (Nat.lt_succ_self n), Polynomial.eval_zero]
    rw [hlast, zero_smul, add_zero] at hh
    exact eq_sub_of_add_eq hh.symm
  rw [Finset.sum_range_succ']
  simp_rw [bernsteinPolynomial.derivative_succ, bernsteinPolynomial.derivative_zero]
  simp only [Nat.add_sub_cancel, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_natCast, Polynomial.eval_neg, Nat.cast_add, Nat.cast_one,
    Polynomial.eval_add, Polynomial.eval_one]
  change (∑ k ∈ Finset.range (n+1), ((n+1:ℝ)*(b k-b (k+1))) • v (k+1)) +
    (-(n+1:ℝ)*b 0) • v 0 = _
  simp_rw [mul_smul, sub_smul, smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hshift]
  simp only [smul_sub, neg_smul, Finset.sum_sub_distrib]
  rw [Finset.smul_sum]
  abel

theorem bernsteinVectorPolynomial_hasDerivAt_succ (n : ℕ) (v : ℕ → E) (t : ℝ) :
    HasDerivAt (bernsteinVectorPolynomial (n+1) v)
      ((n+1 : ℝ) • ∑ k ∈ Finset.range (n+1),
        (bernsteinPolynomial ℝ n k).eval t • (v (k+1)-v k)) t := by
  have h := HasDerivAt.fun_sum (u := Finset.range (n+2))
    (fun k _ => ((bernsteinPolynomial ℝ (n+1) k).hasDerivAt t).smul_const (v k))
  rw [bernsteinVectorPolynomial_derivative_sum n v t] at h
  exact h

theorem bernsteinCurveExtension_hasDerivAt_succ (n : ℕ) (f : ℝ → E) (t : ℝ) :
    HasDerivAt (bernsteinCurveExtension (n+1) f)
      ((n+1 : ℝ) • ∑ k ∈ Finset.range (n+1),
        (bernsteinPolynomial ℝ n k).eval t •
          (f (((k+1:ℕ):ℝ)/(n+1))-f ((k:ℝ)/(n+1)))) t :=
  by simpa only [bernsteinCurveExtension, Nat.cast_add, Nat.cast_one] using
    bernsteinVectorPolynomial_hasDerivAt_succ n (fun k => f ((k:ℝ)/(n+1:ℕ))) t

omit [NormedSpace ℝ E] in
theorem bernstein_adjacent_sample_norm_le {K : ℝ≥0} {f : ℝ → E}
    (hLip : LipschitzOnWith K f (Icc 0 1)) (n k : ℕ) (hk : k < n+1) :
    ‖f (((k+1 : ℕ) : ℝ)/(n+1))-f ((k:ℝ)/(n+1))‖ ≤ (K:ℝ)/(n+1) := by
  have hn : (0:ℝ) < n+1 := by positivity
  have ha : (((k+1 : ℕ) : ℝ)/(n+1)) ∈ Icc (0:ℝ) 1 := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) hn.le, (div_le_one hn).mpr ?_⟩
    exact_mod_cast (Nat.succ_le_of_lt hk)
  have hb : (k:ℝ)/(n+1) ∈ Icc (0:ℝ) 1 := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) hn.le, (div_le_one hn).mpr ?_⟩
    exact_mod_cast (Nat.le_of_lt hk)
  have hdist : dist (((k+1 : ℕ) : ℝ)/(n+1)) ((k:ℝ)/(n+1)) = 1/(n+1) := by
    rw [Real.dist_eq]
    have hh : (((k+1 : ℕ) : ℝ)/(n+1))-(k:ℝ)/(n+1) = 1/(n+1) := by push_cast; ring
    rw [hh, abs_of_pos (one_div_pos.mpr hn)]
  have h := hLip.dist_le_mul _ ha _ hb
  rw [hdist, dist_eq_norm] at h
  exact h.trans_eq (by ring)

theorem bernstein_polynomial_nonneg (n k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    0 ≤ (bernsteinPolynomial ℝ n k).eval t := by
  exact bernstein_nonneg (x := ⟨t, ht⟩)

theorem bernstein_polynomial_probability (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (∑ k ∈ Finset.range (n+1), (bernsteinPolynomial ℝ n k).eval t) = 1 := by
  have h := bernstein.probability n (⟨t,ht⟩ : I)
  change (∑ k : Fin (n+1), (bernsteinPolynomial ℝ n k).eval t) = 1 at h
  simpa only [Finset.sum_range] using h

/-- Smooth polynomial approximation preserves the original boundary
Lipschitz budget exactly, at every positive degree. -/
theorem bernsteinCurveExtension_deriv_norm_le {K : ℝ≥0} {f : ℝ → E}
    (hLip : LipschitzOnWith K f (Icc 0 1)) (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    ‖deriv (bernsteinCurveExtension (n+1) f) t‖ ≤ K := by
  rw [(bernsteinCurveExtension_hasDerivAt_succ n f t).deriv, norm_smul,
    Real.norm_eq_abs, abs_of_pos (show (0:ℝ)<n+1 by positivity)]
  have hsum : ‖∑ k ∈ Finset.range (n+1), (bernsteinPolynomial ℝ n k).eval t •
      (f (((k+1 : ℕ):ℝ)/(n+1))-f ((k:ℝ)/(n+1)))‖ ≤ (K:ℝ)/(n+1) := by
    calc
      _ ≤ ∑ k ∈ Finset.range (n+1), ‖(bernsteinPolynomial ℝ n k).eval t •
          (f (((k+1 : ℕ):ℝ)/(n+1))-f ((k:ℝ)/(n+1)))‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (n+1), (bernsteinPolynomial ℝ n k).eval t * ((K:ℝ)/(n+1)) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (bernstein_polynomial_nonneg n k ht)]
        exact mul_le_mul_of_nonneg_left (bernstein_adjacent_sample_norm_le hLip n k
          (Finset.mem_range.mp hk)) (bernstein_polynomial_nonneg n k ht)
      _ = _ := by rw [← Finset.sum_mul, bernstein_polynomial_probability n ht, one_mul]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by field_simp)

theorem bernsteinCurveExtension_lipschitzOnWith {K : ℝ≥0} {f : ℝ → E}
    (hLip : LipschitzOnWith K f (Icc 0 1)) (n : ℕ) :
    LipschitzOnWith K (bernsteinCurveExtension (n+1) f) (Icc 0 1) := by
  apply (convex_Icc (0:ℝ) 1).lipschitzOnWith_of_nnnorm_deriv_le
  · intro t _
    exact (bernsteinCurveExtension_hasDerivAt_succ n f t).differentiableAt
  · intro t ht
    exact_mod_cast bernsteinCurveExtension_deriv_norm_le hLip n ht

end UV
