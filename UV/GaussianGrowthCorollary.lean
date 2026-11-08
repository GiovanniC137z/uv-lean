import UV.GaussianBoundaryGrowth
import UV.StandardBoundaryBound

/-! Polynomial boundedness on the positive real axis and its cancellation
against the Gaussian exponential obstruction. -/

noncomputable section
open Filter
open scoped Topology

namespace UV

def PositiveAxisPolynomiallyBounded (f : ℝ → ℂ) : Prop :=
  ∃ C : ℝ, ∃ N : ℕ, ∀ᶠ s : ℝ in atTop, ‖f s‖ ≤ C * s ^ N

theorem positive_axis_polynomially_bounded_add {f g : ℝ → ℂ}
    (hf : PositiveAxisPolynomiallyBounded f) (hg : PositiveAxisPolynomiallyBounded g) :
    PositiveAxisPolynomiallyBounded (fun s => f s + g s) := by
  obtain ⟨C, N, hC⟩ := hf
  obtain ⟨D, M, hD⟩ := hg
  refine ⟨|C| + |D|, N + M, ?_⟩
  filter_upwards [hC, hD, eventually_ge_atTop (1 : ℝ)] with s hsf hsg hs1
  have hs0 : 0 ≤ s := zero_le_one.trans hs1
  have hfn : C * s ^ N ≤ |C| * s ^ (N + M) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hs0 N)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hs1 (Nat.le_add_right N M)) (abs_nonneg C))
  have hgn : D * s ^ M ≤ |D| * s ^ (N + M) :=
    (mul_le_mul_of_nonneg_right (le_abs_self D) (pow_nonneg hs0 M)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hs1 (Nat.le_add_left M N)) (abs_nonneg D))
  calc
    _ ≤ ‖f s‖ + ‖g s‖ := norm_add_le _ _
    _ ≤ |C| * s ^ (N + M) + |D| * s ^ (N + M) := add_le_add (hsf.trans hfn) (hsg.trans hgn)
    _ = _ := by ring

theorem positive_axis_polynomially_bounded_neg {f : ℝ → ℂ}
    (hf : PositiveAxisPolynomiallyBounded f) : PositiveAxisPolynomiallyBounded (fun s => -f s) := by
  simpa only [PositiveAxisPolynomiallyBounded, norm_neg] using hf

theorem positive_axis_polynomially_bounded_sub {f g : ℝ → ℂ}
    (hf : PositiveAxisPolynomiallyBounded f) (hg : PositiveAxisPolynomiallyBounded g) :
    PositiveAxisPolynomiallyBounded (fun s => f s - g s) := by
  simpa only [sub_eq_add_neg] using positive_axis_polynomially_bounded_add hf
    (positive_axis_polynomially_bounded_neg hg)

theorem complex_polynomial_positive_axis_bounded (p : Polynomial ℂ) :
    PositiveAxisPolynomiallyBounded (fun s : ℝ => p.eval (s : ℂ)) := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖, p.natDegree, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
  exact complex_polynomial_real_axis_bound p hs

theorem gaussian_remainder_plus_bounded_obstruction {t m : ℝ} (ht : 0 < t)
    {F : ℝ → ℂ} (hF : PositiveAxisPolynomiallyBounded F) :
    ¬ PositiveAxisPolynomiallyBounded (fun s => gaussianRemainder t m (s : ℂ) + F s) := by
  intro hsum
  have hb := positive_axis_polynomially_bounded_sub hsum hF
  have hR : PositiveAxisPolynomiallyBounded (fun s : ℝ => gaussianRemainder t m (s : ℂ)) := by
    simpa only [add_sub_cancel_right] using hb
  exact gaussian_remainder_not_polynomially_bounded ht hR

theorem standard_bubble_upper_boundary_positive_axis_bounded {m : ℝ} (hm : 0 < m) :
    PositiveAxisPolynomiallyBounded (standardBubbleUpperBoundary m) := by
  refine ⟨(|Real.log (m ^ 2)| + 7 + Real.pi) / (16 * Real.pi ^ 2), 1, ?_⟩
  filter_upwards [eventually_gt_atTop (4 * m ^ 2), eventually_ge_atTop (1 : ℝ)] with s hs hs1
  simpa only [pow_one] using standard_bubble_upper_boundary_norm_linear_bound hm hs hs1

theorem gaussian_upper_boundary_add_polynomial_not_bounded {t m : ℝ}
    (ht : 0 < t) (hm : 0 < m) (p : Polynomial ℂ) :
    ¬ PositiveAxisPolynomiallyBounded
      (fun s : ℝ => gaussianNormalizedBubbleUpperBoundary t m s + p.eval (s : ℂ)) := by
  have hstd := standard_bubble_upper_boundary_positive_axis_bounded hm
  have hF := positive_axis_polynomially_bounded_add hstd (complex_polynomial_positive_axis_bounded p)
  have hobstruction := gaussian_remainder_plus_bounded_obstruction (m := m) ht hF
  have he : (fun s : ℝ => gaussianRemainder t m (s : ℂ) +
      (standardBubbleUpperBoundary m s + p.eval (s : ℂ))) =
      (fun s : ℝ => gaussianNormalizedBubbleUpperBoundary t m s + p.eval (s : ℂ)) := by
    funext s
    unfold gaussianNormalizedBubbleUpperBoundary
    abel
  rw [he] at hobstruction
  exact hobstruction

/-- The complete source Gaussian-growth obstruction. The normalized bubble
boundary here is the actual upper-rim limit, proved by dominated convergence;
its ordinary logarithmic contribution is quantitatively bounded before the
exponential remainder is used. -/
theorem gaussian_growth_obstruction {t m : ℝ} (ht : 0 < t) (hm : 0 < m) :
    (∀ s : ℝ, 0 < s → Real.log 2 / (48 * Real.pi ^ 2) * Real.exp (-2 * t * m ^ 2) *
      (Real.exp (2 * t * s / 9) - 1) ≤ -(gaussianRemainder t m (s : ℂ)).re) ∧
    (∀ p : Polynomial ℂ, ¬ PositiveAxisPolynomiallyBounded
      (fun s : ℝ => gaussianRemainder t m (s : ℂ) + p.eval (s : ℂ))) ∧
    (∀ p : Polynomial ℂ, ¬ PositiveAxisPolynomiallyBounded
      (fun s : ℝ => gaussianNormalizedBubbleUpperBoundary t m s + p.eval (s : ℂ))) ∧
    (∀ s : ℝ, 0 ≤ s → Tendsto
      (fun η : ℝ => gaussianNormalizedBubble t m ((s : ℂ) + (η : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 (gaussianNormalizedBubbleUpperBoundary t m s))) := by
  refine ⟨fun s hs => gaussian_remainder_growth_lower ht hs.le, ?_,
    gaussian_upper_boundary_add_polynomial_not_bounded ht hm,
    fun _ hs => gaussian_normalized_bubble_upper_boundary_tendsto ht hm hs⟩
  intro p
  exact gaussian_remainder_add_polynomial_not_bounded ht p

end UV
