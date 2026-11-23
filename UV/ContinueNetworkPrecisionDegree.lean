import UV.ContinueNetworkDirectional
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! The intrinsic polynomial growth degree on a coordinate subspace. -/

noncomputable section

open scoped BigOperators

namespace UV.ContinueNetworkPrecision

/-- The degree of one monomial in the weak coordinates. -/
def weakMonomialDegree {d : ℕ} (W : Finset (Fin d)) (α : Fin d →₀ ℕ) : ℕ :=
  ∑ i ∈ W, α i

/-- The greatest weak degree among supported monomials. -/
def weakDegree {d : ℕ} (W : Finset (Fin d)) (P : MvPolynomial (Fin d) ℂ) : ℕ :=
  P.support.sup (weakMonomialDegree W)

/-- The literal univariate polynomial obtained by substituting the real ray
(x+s w) in the multivariate polynomial. -/
def rayPolynomial {d : ℕ} (P : MvPolynomial (Fin d) ℂ) (x w : Fin d → ℝ) :
    Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (x i : ℂ) + Polynomial.C (w i : ℂ) * Polynomial.X) P

theorem rayPolynomial_eval {d : ℕ} (P : MvPolynomial (Fin d) ℂ)
    (x w : Fin d → ℝ) (s : ℂ) :
    (rayPolynomial P x w).eval s =
      MvPolynomial.eval (fun i => (x i : ℂ) + (w i : ℂ) * s) P := by
  let r := MvPolynomial.eval₂Hom Polynomial.C
    (fun i : Fin d => Polynomial.C (x i : ℂ) + Polynomial.C (w i : ℂ) * Polynomial.X)
  have h : (Polynomial.evalRingHom s).comp r =
      MvPolynomial.eval (fun i => (x i : ℂ) + (w i : ℂ) * s) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [r]
    · intro i
      simp [r]
  exact DFunLike.congr_fun h P

private theorem sum_weakMonomialDegree {d : ℕ} (W : Finset (Fin d)) (α : Fin d →₀ ℕ) :
    (∑ i : Fin d, if i ∈ W then α i else 0) = weakMonomialDegree W α := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

private theorem rayPolynomial_monomial {d : ℕ} (x w : Fin d → ℝ)
    (α : Fin d →₀ ℕ) (c : ℂ) :
    rayPolynomial (MvPolynomial.monomial α c) x w =
      Polynomial.C c *
        ∏ i : Fin d, (Polynomial.C (x i : ℂ) + Polynomial.C (w i : ℂ) * Polynomial.X) ^ α i := by
  change MvPolynomial.eval₂ _ _ _ = _
  rw [MvPolynomial.eval₂_monomial, Finsupp.prod_fintype]
  intro i
  exact pow_zero _

private theorem rayPolynomial_monomial_degree_le {d : ℕ} (W : Finset (Fin d))
    (x w : Fin d → ℝ) (hw : ∀ i ∉ W, w i = 0) (α : Fin d →₀ ℕ) (c : ℂ) :
    (rayPolynomial (MvPolynomial.monomial α c) x w).natDegree ≤ weakMonomialDegree W α := by
  rw [rayPolynomial_monomial, ← sum_weakMonomialDegree]
  apply (Polynomial.natDegree_mul_le).trans
  rw [Polynomial.natDegree_C, zero_add]
  apply (Polynomial.natDegree_prod_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  split_ifs with h
  · refine (Polynomial.natDegree_pow_le_of_le _ ?_).trans_eq (mul_one _)
    exact Polynomial.natDegree_add_le_of_le (m := 0) (n := 1) (by simp)
      ((Polynomial.natDegree_C_mul_le _ _).trans (by simp))
  · simp [hw i h, ← map_pow]

/-- Every ray parallel to the weak coordinate subspace has weak-degree bound. -/
theorem rayPolynomial_natDegree_le {d : ℕ} (W : Finset (Fin d))
    (P : MvPolynomial (Fin d) ℂ) (x w : Fin d → ℝ) (hw : ∀ i ∉ W, w i = 0) :
    (rayPolynomial P x w).natDegree ≤ weakDegree W P := by
  conv_lhs => rw [P.as_sum]
  unfold rayPolynomial
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro α hα
  exact (rayPolynomial_monomial_degree_le W x w hw α _).trans
    (Finset.le_sup (f := weakMonomialDegree W) hα)

private def rayBase {d : ℕ} (W : Finset (Fin d)) (z : DirectionalMomentum d) :
    Fin d → ℝ := fun i => if i ∈ W then 0 else z i

private def rayVelocity {d : ℕ} (W : Finset (Fin d)) (z : DirectionalMomentum d) :
    Fin d → ℝ := fun i => if i ∈ W then z i else 0

private theorem rayPolynomial_monomial_split {d : ℕ} (W : Finset (Fin d))
    (z : DirectionalMomentum d) (α : Fin d →₀ ℕ) (c : ℂ) :
    rayPolynomial (MvPolynomial.monomial α c) (rayBase W z) (rayVelocity W z) =
      Polynomial.C (c * ∏ i, (z i : ℂ)^α i) * Polynomial.X ^ weakMonomialDegree W α := by
  rw [rayPolynomial_monomial]
  have hsplit (i : Fin d) :
      (Polynomial.C ((rayBase W z i : ℝ) : ℂ) +
        Polynomial.C ((rayVelocity W z i : ℝ) : ℂ) * Polynomial.X) ^ α i =
      Polynomial.C ((z i : ℂ) ^ α i) * Polynomial.X ^ (if i ∈ W then α i else 0) := by
    by_cases hi : i ∈ W <;> simp [rayBase, rayVelocity, hi, ← map_pow, mul_pow]
  simp_rw [hsplit, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum,
    sum_weakMonomialDegree, ← mul_assoc, ← map_mul]

/-- An actual real ray realizes the greatest weak monomial degree, with
a nonzero univariate polynomial even if the weak subspace is zero. -/
theorem rayPolynomial_natDegree_attained {d : ℕ} (W : Finset (Fin d))
    (P : MvPolynomial (Fin d) ℂ) (hP : P ≠ 0) :
    ∃ x w : Fin d → ℝ, (∀ i ∉ W, w i = 0) ∧ rayPolynomial P x w ≠ 0 ∧
      (rayPolynomial P x w).natDegree = weakDegree W P := by
  classical
  let N := weakDegree W P
  have hsupport : P.support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
  obtain ⟨α, hα, hαN⟩ := Finset.exists_mem_eq_sup _ hsupport (weakMonomialDegree W)
  let S := P.support.filter (fun β => N = weakMonomialDegree W β)
  have hs : α ∈ S := Finset.mem_filter.mpr ⟨hα, hαN⟩
  let G := ∑ β ∈ S, MvPolynomial.monomial β (P.coeff β)
  have hG : G ≠ 0 := by
    have hc : G.coeff α = P.coeff α := by
      rw [MvPolynomial.coeff_sum]
      refine Finset.sum_eq_single_of_mem α hs ?_ |>.trans ?_
      · intro β hb hne
        simp [MvPolynomial.coeff_monomial, hne]
      · simp
    intro h
    rw [h, MvPolynomial.coeff_zero] at hc
    exact (MvPolynomial.mem_support_iff.mp hα) hc.symm
  obtain ⟨z,hz⟩ := directionalNumerator_exists_ne_zero hG
  let x := rayBase W z
  let w := rayVelocity W z
  have hw (i : Fin d) (hi : i ∉ W) : w i = 0 := by
    simp [w, rayVelocity, hi]
  have hsum :
      rayPolynomial P x w = ∑ β ∈ P.support, rayPolynomial (MvPolynomial.monomial β (P.coeff β)) x w := by
    conv_lhs => rw [P.as_sum]
    exact map_sum _ _ _
  have hc : (rayPolynomial P x w).coeff N = directionalNumerator G z := by
    rw [hsum, Polynomial.finset_sum_coeff]
    simp_rw [x, w, rayPolynomial_monomial_split, Polynomial.coeff_C_mul_X_pow]
    simp only [directionalNumerator, G, map_sum, MvPolynomial.eval_monomial]
    simp_rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rw [Finset.sum_filter]
  have hc' : (rayPolynomial P x w).coeff N ≠ 0 := hc ▸ hz
  refine ⟨x, w, hw, fun h => hc' (by simp [h]), ?_⟩
  exact le_antisymm (rayPolynomial_natDegree_le W P x w hw)
    (Polynomial.le_natDegree_of_ne_zero hc')

end UV.ContinueNetworkPrecision
