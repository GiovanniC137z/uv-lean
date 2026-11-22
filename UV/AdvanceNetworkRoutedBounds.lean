import UV.AdvanceNetworkRouted
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Uniform routed momentum bounds on positive duration boxes.
The affine shift is kept in the same fixed intrinsic Euclidean frame. -/

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix InnerProductSpace

namespace UV

private theorem networkEuclidean_dot_self_sq {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    x.ofLp ⬝ᵥ x.ofLp = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  simp only [dotProduct, pow_two]
  rfl

theorem networkSPD_eigenvalue_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) {a d : ℝ}
    (hlo : ∀ x : EuclideanSpace ℝ ι, a * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ (A *ᵥ x.ofLp))
    (hhi : ∀ x : EuclideanSpace ℝ ι, x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) ≤ d * ‖x‖ ^ 2)
    (i : ι) : a ≤ hA.1.eigenvalues i ∧ hA.1.eigenvalues i ≤ d := by
  let x := hA.1.eigenvectorBasis i
  have hx : ‖x‖ = 1 := hA.1.eigenvectorBasis.norm_eq_one i
  have he : A *ᵥ x.ofLp = hA.1.eigenvalues i • x.ofLp :=
    hA.1.mulVec_eigenvectorBasis i
  have hq : x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) = hA.1.eigenvalues i := by
    rw [he, dotProduct_smul, networkEuclidean_dot_self_sq, hx, one_pow, smul_eq_mul, mul_one]
  exact ⟨by simpa only [hq, hx, one_pow, mul_one] using hlo x,
    by simpa only [hq, hx, one_pow, mul_one] using hhi x⟩

/-- The reciprocal duration inequalities use the same precision and the
orthonormal eigenbasis, including the prescribed inverse. -/
theorem networkSPD_inverse_quadratic_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) {a d : ℝ} (ha : 0 < a)
    (hlo : ∀ x : EuclideanSpace ℝ ι, a * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ (A *ᵥ x.ofLp))
    (hhi : ∀ x : EuclideanSpace ℝ ι, x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) ≤ d * ‖x‖ ^ 2)
    (q : EuclideanSpace ℝ ι) :
    ‖q‖ ^ 2 / d ≤ q.ofLp ⬝ᵥ (A⁻¹ *ᵥ q.ofLp) ∧
      q.ofLp ⬝ᵥ (A⁻¹ *ᵥ q.ofLp) ≤ ‖q‖ ^ 2 / a := by
  rw [← networkSPD_inverse_quadratic A hA q]
  have hn : ‖q‖ ^ 2 = ∑ i, (hA.1.eigenvectorBasis.repr q i) ^ 2 := by
    rw [← hA.1.eigenvectorBasis.repr.norm_map q, EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
  rw [hn, Finset.sum_div, Finset.sum_div]
  constructor
  · exact Finset.sum_le_sum (fun i _ => div_le_div_of_nonneg_left (sq_nonneg _)
      (hA.eigenvalues_pos i) (networkSPD_eigenvalue_bounds A hA hlo hhi i).2)
  · exact Finset.sum_le_sum (fun i _ => div_le_div_of_nonneg_left (sq_nonneg _)
      ha (networkSPD_eigenvalue_bounds A hA hlo hhi i).1)

def networkSharedDamping {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (s : E → ℝ) (q : NetworkVisitSpace n) : ℝ :=
  q.ofLp ⬝ᵥ ((networkFullPrecision src dst s)⁻¹ *ᵥ q.ofLp)

theorem networkSharedDamping_duration_bounds {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n))
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∀ (s : E → ℝ) (smin smax : ℝ),
      0 < smin → 0 < smax → (∀ e, smin ≤ s e ∧ s e ≤ smax) →
      ∀ q : NetworkVisitSpace n,
        smin / C * ‖q‖ ^ 2 ≤ networkSharedDamping src dst s q ∧
          networkSharedDamping src dst s q ≤ smax / γ * ‖q‖ ^ 2 := by
  obtain ⟨γ, C, hγ, hC, hbound⟩ := networkSharedEnergy_duration_bounds G src dst hG hcover
  refine ⟨γ, C + 1, hγ, by positivity, ?_⟩
  intro s smin smax hmin hmax hs q
  have hA := networkFullPrecision_posDef G src dst s hG hcover
    (fun e => hmin.trans_le (hs e).1)
  have hLo (x : NetworkVisitSpace n) : γ / smax * ‖x‖ ^ 2 ≤
      x.ofLp ⬝ᵥ (networkFullPrecision src dst s *ᵥ x.ofLp) := by
    rw [networkFullPrecision_quadratic]
    exact (hbound s smin smax hmin hmax hs x).1
  have hHi (x : NetworkVisitSpace n) :
      x.ofLp ⬝ᵥ (networkFullPrecision src dst s *ᵥ x.ofLp) ≤ (C + 1) / smin * ‖x‖ ^ 2 := by
    rw [networkFullPrecision_quadratic]
    apply (hbound s smin smax hmin hmax hs x).2.trans
    gcongr
    linarith
  have hInv := networkSPD_inverse_quadratic_bounds _
    hA (div_pos hγ hmax) hLo hHi q
  have heLo : ‖q‖ ^ 2 / ((C + 1) / smin) = smin / (C + 1) * ‖q‖ ^ 2 := by
    rw [div_div_eq_mul_div]
    ring
  have heHi : ‖q‖ ^ 2 / (γ / smax) = smax / γ * ‖q‖ ^ 2 := by
    rw [div_div_eq_mul_div]
    ring
  rw [heLo, heHi] at hInv
  exact hInv

/-- A full-column-rank route has a positive Euclidean lower bound on
unit vectors, and its affine shift gives the stated subtraction of `‖b‖`. -/
theorem networkRouting_affine_lower {n L : ℕ}
    (B : NetworkVisitSpace L →L[ℝ] NetworkVisitSpace n) (hB : Function.Injective B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ b k, δ * ‖k‖ ≤ ‖B k + b‖ + ‖b‖ := by
  have hh (t : ℝ) (ht : 0 ≤ t) (k : NetworkVisitSpace L) :
      ‖B (t • k)‖ = t ^ 1 * ‖B k‖ := by
    rw [map_smul, norm_smul, Real.norm_of_nonneg ht, pow_one]
  have hp (k : NetworkVisitSpace L) (hk : ‖k‖ = 1) : 0 < ‖B k‖ := by
    refine norm_pos_iff.mpr fun h => ?_
    have hz := hB (h.trans B.map_zero.symm)
    simp only [hz, norm_zero] at hk
    norm_num at hk
  obtain ⟨δ, hδ, hδk⟩ := positive_homogeneous_coercivity (fun k => ‖B k‖)
    B.continuous.norm (by norm_num : 0 < 1) hh hp
  refine ⟨δ, hδ, fun b k => (by simpa only [pow_one] using hδk k :
    δ * ‖k‖ ≤ ‖B k‖).trans ?_⟩
  simpa only [add_sub_cancel_right] using norm_sub_le (B k + b) b

private theorem networkRouting_shifted_square {n L : ℕ}
    (B : NetworkVisitSpace L →L[ℝ] NetworkVisitSpace n) {δ R : ℝ}
    (hle : ∀ b k, δ * ‖k‖ ≤ ‖B k + b‖ + ‖b‖)
    (b : NetworkVisitSpace n) (hb : ‖b‖ ≤ R) (k : NetworkVisitSpace L)
    (hδ : 0 < δ) :
    (δ ^ 2 / 2) * ‖k‖ ^ 2 - R ^ 2 ≤ ‖B k + b‖ ^ 2 := by
  have h := (hle b k).trans (add_le_add_left hb ‖B k + b‖)
  have hs := pow_le_pow_left₀ (mul_nonneg hδ.le (norm_nonneg k)) h 2
  nlinarith [sq_nonneg (‖B k + b‖ - R)]

/-- With a bounded external shift, truncating the duration coefficient at
one keeps the Gaussian prefactor uniform even for large durations. -/
theorem networkRoutedGaussian_duration_envelope {E : Type*} [Fintype E] {n L : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n))
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst)
    (B : NetworkVisitSpace L →L[ℝ] NetworkVisitSpace n) (hB : Function.Injective B) (R : ℝ) :
    ∃ a K : ℝ, 0 < a ∧ 0 < K ∧ ∀ (s : E → ℝ) (smin smax : ℝ),
      0 < smin → 0 < smax → (∀ e, smin ≤ s e ∧ s e ≤ smax) →
      ∀ (b : NetworkVisitSpace n), ‖b‖ ≤ R → ∀ k : NetworkVisitSpace L,
        Real.exp (-networkSharedDamping src dst s (B k + b)) ≤
          K * Real.exp (-(a * min 1 smin * ‖k‖ ^ 2)) := by
  obtain ⟨γ, C, hγ, hC, hbound⟩ := networkSharedDamping_duration_bounds G src dst hG hcover
  obtain ⟨δ, hδ, hδk⟩ := networkRouting_affine_lower B hB
  let a := δ ^ 2 / (2 * C)
  let K := Real.exp (R ^ 2 / C)
  refine ⟨a, K, by dsimp [a]; positivity, Real.exp_pos _, ?_⟩
  intro s smin smax hmin hmax hs b hb k
  let t := min 1 smin
  have ht : 0 < t := lt_min zero_lt_one hmin
  have htmin : t ≤ smin := min_le_right _ _
  have ht1 : t ≤ 1 := min_le_left _ _
  have hd := (hbound s smin smax hmin hmax hs (B k + b)).1
  have hnon : (t / C) * ‖B k + b‖ ^ 2 ≤ networkSharedDamping src dst s (B k + b) :=
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right htmin hC.le) (sq_nonneg _)).trans hd
  have hsq := mul_le_mul_of_nonneg_left
    (networkRouting_shifted_square B hδk b hb k hδ) (div_nonneg ht.le hC.le)
  have hshift := mul_le_mul_of_nonneg_right ht1 (div_nonneg (sq_nonneg R) hC.le)
  have hEq : t / C * (δ ^ 2 / 2 * ‖k‖ ^ 2 - R ^ 2) =
      a * t * ‖k‖ ^ 2 - t * (R ^ 2 / C) := by
    dsimp [a]
    field_simp
  have hcost := hsq.trans hnon
  rw [hEq] at hcost
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  change -networkSharedDamping src dst s (B k + b) ≤ R ^ 2 / C + -(a * t * ‖k‖ ^ 2)
  linarith only [hcost, hshift]

end UV
