import UV.FurtherCurvatureDeterminant
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Weighted absolute sums of finite curvature contraction products. The
coefficient can encode conservation indicators, color sums, and fixed-mode
external factors. Its uniform bound is explicit in the graph interface. -/

noncomputable section

open Filter Real MeasureTheory
open scoped BigOperators Topology

namespace UV.FurtherCurvatureGraph

open UV.FurtherCurvatureShell UV.FurtherCurvatureLine UV.FurtherCurvatureDeterminant
open UV.RevisionCurvatureDeterminant

abbrev Assignment (I : ℕ) := Fin I → TorusMode

def absoluteTerm {I : ℕ} (H ℓ : ℝ) (coeff : Assignment I → ℝ) (a : Assignment I) : ℝ :=
  H * |coeff a| * ∏ e, curvatureLine ℓ (a e)

private theorem line_nonneg (ℓ : ℝ) (k : TorusMode) : 0 ≤ curvatureLine ℓ k := by
  unfold curvatureLine curvatureCovariance
  positivity

theorem absolute_term_nonneg {I : ℕ} {H ℓ : ℝ} (hH : 0 ≤ H)
    (coeff : Assignment I → ℝ) (a : Assignment I) :
    0 ≤ absoluteTerm H ℓ coeff a := by
  exact mul_nonneg (mul_nonneg hH (abs_nonneg _)) (Finset.prod_nonneg fun e _ => line_nonneg ℓ (a e))

private theorem line_product_weighted {I : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (ℓ : ℝ) (a : Assignment I) :
    (∏ e, curvatureLine ℓ (a e)) ≤ ∏ e, weightedLine s ℓ (a e) := by
  apply Finset.prod_le_prod (fun e _ => line_nonneg ℓ (a e))
  intro e _
  unfold weightedLine
  have hfreq : 0 ≤ latticeFrequency (a e) := sqrt_nonneg _
  exact le_mul_of_one_le_left (line_nonneg _ _) (Real.one_le_rpow (by linarith) hs)

private theorem high_line_product_weighted {I : ℕ} {s M : ℝ} (hs : 0 ≤ s) (hM : 0 < M)
    (ℓ : ℝ) (a : Assignment I) (high : ∃ e, M < latticeFrequency (a e)) :
    M^s * (∏ e, curvatureLine ℓ (a e)) ≤ ∏ e, weightedLine s ℓ (a e) := by
  obtain ⟨e, he⟩ := high
  let W := fun j : Fin I => (1+latticeFrequency (a j))^s
  have h1 (j : Fin I) : 1 ≤ W j := by
    apply Real.one_le_rpow _ hs
    have hj : 0 ≤ latticeFrequency (a j) := sqrt_nonneg _
    linarith
  have hMpow : M^s ≤ W e := Real.rpow_le_rpow hM.le (by linarith) hs
  have heW : W e ≤ ∏ j, W j := by
    rw [← Finset.mul_prod_erase Finset.univ W (Finset.mem_univ e)]
    refine le_mul_of_one_le_right (zero_le_one.trans (h1 e)) ?_
    simpa only [Finset.prod_const_one] using
      (Finset.prod_le_prod (s := Finset.univ.erase e) (f := fun _ => (1:ℝ))
        (g := W) (fun _ _ => zero_le_one) (fun j _ => h1 j))
  exact (mul_le_mul_of_nonneg_right (hMpow.trans heW)
    (Finset.prod_nonneg fun e _ => line_nonneg ℓ (a e))).trans (by
      simp_rw [weightedLine, Finset.prod_mul_distrib]
      rfl)

private theorem sum_weighted_assignments {I : ℕ} (modes : Finset TorusMode) (s ℓ : ℝ) :
    (∑ a ∈ Fintype.piFinset (fun _ : Fin I => modes), ∏ e, weightedLine s ℓ (a e)) =
      (∑ k ∈ modes, weightedLine s ℓ k)^I :=
  (Finset.sum_prod_piFinset modes (fun (_ : Fin I) k => weightedLine s ℓ k)).trans (by simp)

/-- The one-determinant absolute estimate for a finite contraction product
with bounded residual coefficients. -/
theorem finite_absolute_sum_bound {I : ℕ} {H ℓ B s : ℝ} (hH : 0 ≤ H) (hs : 0 ≤ s)
    (modes : Finset TorusMode) (coeff : Assignment I → ℝ) (hc : ∀ a, |coeff a| ≤ B) :
    ∑ a ∈ Fintype.piFinset (fun _ : Fin I => modes), absoluteTerm H ℓ coeff a ≤
      H * B * (∑ k ∈ modes, weightedLine s ℓ k)^I := by
  have hB := (abs_nonneg (coeff 0)).trans (hc 0)
  rw [← sum_weighted_assignments (I := I), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hc a) hH)
    (line_product_weighted hs ℓ a) (Finset.prod_nonneg fun e _ => line_nonneg ℓ (a e))
    (mul_nonneg hH hB)

def sphericalTail {I : ℕ} (n : ℕ) (Λ ℓ M : ℝ) (coeff : Assignment I → ℝ) : ℝ :=
  ∑ a ∈ (Fintype.piFinset (fun _ : Fin I => sphericalModes Λ)).filter
      (fun a => ∃ e, M < latticeFrequency (a e)),
    absoluteTerm (sphericalDeterminant n Λ ℓ) ℓ coeff a

private theorem spherical_tail_weighted {I n : ℕ} {s Λ ℓ M B : ℝ}
    (hs : 0 ≤ s) (hM : 0 < M) (coeff : Assignment I → ℝ) (hc : ∀ a, |coeff a| ≤ B) :
    M^s * sphericalTail n Λ ℓ M coeff ≤
      sphericalDeterminant n Λ ℓ * B * (∑ k ∈ sphericalModes Λ, weightedLine s ℓ k)^I := by
  classical
  let H := sphericalDeterminant n Λ ℓ
  have hH : 0 ≤ H := (relative_determinant_bounds (sphericalModes Λ) latticeFrequency ℓ n).1.le
  have hB := (abs_nonneg (coeff 0)).trans (hc 0)
  unfold sphericalTail
  rw [Finset.mul_sum, ← sum_weighted_assignments (I := I), Finset.mul_sum]
  refine (Finset.sum_le_sum ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun a _ _ => ?_))
  · intro a ha
    have high : ∃ e, M < latticeFrequency (a e) := (Finset.mem_filter.mp ha).2
    change M^s * absoluteTerm H ℓ coeff a ≤ H * B * ∏ e, weightedLine s ℓ (a e)
    unfold absoluteTerm
    calc
      _ = H * |coeff a| * (M^s * ∏ e, curvatureLine ℓ (a e)) := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left (hc a) hH)
        (high_line_product_weighted hs hM ℓ a high)
        (mul_nonneg (Real.rpow_nonneg hM.le _) (Finset.prod_nonneg fun e _ => line_nonneg ℓ (a e)))
        (mul_nonneg hH hB)
  · exact mul_nonneg (mul_nonneg hH hB)
      (Finset.prod_nonneg fun e _ => weightedLine_nonneg s ℓ (a e))

/-- The absolute high-momentum tail is uniformly O(M⁻ˢ) for every finite
contraction product with bounded residual coefficients and the literal
curvature lines. The depth and the spherical cutoff share one determinant. -/
theorem spherical_tail_uniform {I n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 ≤ s) :
    ∃ C > 0, ∀ {Λ ℓ M B : ℝ}, 0 ≤ Λ → 0 ≤ ℓ → 0 < M →
      ∀ coeff : Assignment I → ℝ, (∀ a, |coeff a| ≤ B) →
      sphericalTail n Λ ℓ M coeff ≤ C * B * M^(-s) := by
  obtain ⟨L, hL, hl⟩ := spherical_weighted_line_bound hs
  let D := (2+s) * (I:ℝ)
  have hD : 0 ≤ D := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  obtain ⟨P, hP, hp⟩ := spherical_determinant_polynomial_control hn hD
  refine ⟨L^I * P, by positivity, fun {Λ ℓ M B} hΛ hℓ hM coeff hc => ?_⟩
  let R := effectiveRadius Λ ℓ
  let H := sphericalDeterminant n Λ ℓ
  have hR : 0 ≤ R := by
    dsimp only [R, effectiveRadius]
    split
    · exact hΛ
    · exact le_min hΛ (inv_nonneg.mpr hℓ)
  have hH : 0 ≤ H := (relative_determinant_bounds (sphericalModes Λ) latticeFrequency ℓ n).1.le
  have hB := (abs_nonneg (coeff 0)).trans (hc 0)
  have hsum := spherical_tail_weighted hs hM coeff hc (Λ := Λ) (ℓ := ℓ) (n := n)
  have hsum' : M^s * sphericalTail n Λ ℓ M coeff ≤ (L^I * P) * B := by
    calc
      _ ≤ H * B * (∑ k ∈ sphericalModes Λ, weightedLine s ℓ k)^I := hsum
      _ ≤ H * B * (L * (1+R)^(2+s))^I := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Finset.sum_nonneg (fun k _ => weightedLine_nonneg s ℓ k)) (hl hΛ hℓ) _)
        (mul_nonneg hH hB)
      _ = L^I * B * (H * (1+R)^D) := by
        rw [mul_pow, ← Real.rpow_natCast ((1+R)^(2+s)), ← Real.rpow_mul (by positivity)]
        ring
      _ ≤ _ := by
        calc
          L^I * B * (H * (1+R)^D) ≤ L^I * B * P :=
            mul_le_mul_of_nonneg_left (hp hΛ hℓ) (by positivity)
          _ = _ := by ring
  rw [Real.rpow_neg hM.le, ← div_eq_mul_inv]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hM _)).mpr (by simpa only [mul_comm] using hsum')

end UV.FurtherCurvatureGraph
