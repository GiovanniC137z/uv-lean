import UV.ContinueNetworkPrecisionDegree
import UV.ContinueNetworkPrecisionChart
import UV.ContinueNetworkPolynomialNormPullback
import Mathlib.Algebra.Polynomial.Roots

/-! Invariance of actual momentum-ray degrees and their maximal realization
in the greedy coordinates. -/

noncomputable section

open scoped BigOperators

namespace UV.ContinueNetworkPrecision

theorem rayPolynomial_eval_real {d : ℕ} (P : MvPolynomial (Fin d) ℂ)
    (x w : DirectionalMomentum d) (s : ℝ) :
    (rayPolynomial P (fun i => x i) (fun i => w i)).eval (s : ℂ) =
      directionalNumerator P (x + s • w) := by
  rw [rayPolynomial_eval, directionalNumerator]
  congr 2
  funext i
  simp [PiLp.add_apply, PiLp.smul_apply, mul_comm]

theorem rayPolynomial_eq_of_eval_real {p q : Polynomial ℂ}
    (h : ∀ s : ℝ, p.eval (s : ℂ) = q.eval (s : ℂ)) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
  rintro _ ⟨s,rfl⟩
  exact h s

theorem rayPolynomial_composeLinear {d : ℕ}
    (L : DirectionalMomentum d ≃L[ℝ] DirectionalMomentum d)
    (P : MvPolynomial (Fin d) ℂ) (x w : DirectionalMomentum d) :
    rayPolynomial (directionalPolynomialComposeLinear L.symm.toContinuousLinearMap P)
      (fun i => L x i) (fun i => L w i) =
      rayPolynomial P (fun i => x i) (fun i => w i) := by
  apply rayPolynomial_eq_of_eval_real
  intro s
  rw [rayPolynomial_eval_real, rayPolynomial_eval_real, directionalNumerator_compose_linear]
  simp only [ContinuousLinearEquiv.coe_coe, ← map_smul, ← map_add,
    ContinuousLinearEquiv.symm_apply_apply]

/-- Degrees of the nonzero literal restrictions to real affine rays with
velocity in the specified linear subspace. -/
def rayDegreeSet {d : ℕ} (K : Submodule ℝ (DirectionalMomentum d))
    (P : MvPolynomial (Fin d) ℂ) : Set ℕ :=
  {n | ∃ (x w : DirectionalMomentum d), w ∈ K ∧
    rayPolynomial P (fun i => x i) (fun i => w i) ≠ 0 ∧
    (rayPolynomial P (fun i => x i) (fun i => w i)).natDegree = n}

/-- The directional degree (n_K(P)) from the manuscript. -/
def directionalDegree {d : ℕ} (K : Submodule ℝ (DirectionalMomentum d))
    (P : MvPolynomial (Fin d) ℂ) : ℕ :=
  sSup (rayDegreeSet K P)

/-- The greatest weak-slot monomial degree is exactly the greatest
degree along actual rays in the original momentum subspace. -/
theorem rayDegreeSet_isGreatest_of_chart {d : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (hP : P ≠ 0)
    (K : Submodule ℝ (DirectionalMomentum d))
    (L : DirectionalMomentum d ≃L[ℝ] DirectionalMomentum d) (W : Finset (Fin d))
    (hW : ∀ w, w ∈ K ↔ ∀ i ∉ W, L w i = 0) :
    IsGreatest (rayDegreeSet K P)
      (weakDegree W (directionalPolynomialComposeLinear L.symm.toContinuousLinearMap P)) := by
  let P' := directionalPolynomialComposeLinear L.symm.toContinuousLinearMap P
  obtain ⟨x, w, hw, hne, hdeg⟩ := rayPolynomial_natDegree_attained W P'
    (directionalPolynomialComposeLinear_ne_zero L.symm hP)
  let x' := L.symm (WithLp.toLp 2 x)
  let w' := L.symm (WithLp.toLp 2 w)
  have hx' : (fun i => L x' i) = x := by
    funext i
    simp [x']
  have hw' : (fun i => L w' i) = w := by
    funext i
    simp [w']
  have heq := rayPolynomial_composeLinear L P x' w'
  rw [hx', hw'] at heq
  refine ⟨⟨x', w', (hW w').mpr ?_, heq ▸ hne, heq ▸ hdeg⟩, ?_⟩
  · intro i hi
    exact (congrFun hw' i).trans (hw i hi)
  · rintro n ⟨q, v, hv, hne, hdeg⟩
    rw [← hdeg, ← rayPolynomial_composeLinear L P q v]
    exact rayPolynomial_natDegree_le W P' _ _ ((hW v).mp hv)

theorem directionalDegree_eq_weakDegree {d : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (hP : P ≠ 0)
    (K : Submodule ℝ (DirectionalMomentum d))
    (L : DirectionalMomentum d ≃L[ℝ] DirectionalMomentum d) (W : Finset (Fin d))
    (hW : ∀ w, w ∈ K ↔ ∀ i ∉ W, L w i = 0) :
    directionalDegree K P =
      weakDegree W (directionalPolynomialComposeLinear L.symm.toContinuousLinearMap P) :=
  (rayDegreeSet_isGreatest_of_chart P hP K L W hW).csSup_eq

end UV.ContinueNetworkPrecision
