import UV.ContinueNetworkPrecisionDegree
import UV.ContinueNetworkPolynomialNormWeights
import UV.ContinueNetworkOrderedMonomial

/-! The strict endpoint power expressed as weak dimension plus the
maximum degree over supported monomials. -/

noncomputable section

open scoped BigOperators

namespace UV.ContinueNetworkPrecision

theorem directionalOrderedPrefix_monomial_eq_weakDegree {d m : ℕ}
    (ν : Fin m → ℝ) (label : Fin d → Option (Fin m)) (β : Fin d →₀ ℕ) (j : Fin m) :
    let W := directionalGaussianWeakRows label (Finset.univ.filter (· ≤ j))
    directionalOrderedPrefix (directionalMonomialExponent ν label β) j =
      directionalOrderedPrefix ν j - ((W.card : ℝ) + weakMonomialDegree W β) / 2 := by
  classical
  let W := directionalGaussianWeakRows label (Finset.univ.filter (· ≤ j))
  rw [directionalMonomialExponent_prefix]
  have h (i : Fin d) :
      (label i).elim 0 (fun k => if k ≤ j then directionalMonomialLoss (fun i => β i) i else 0) =
      if i ∈ W then ((β i : ℝ) + 1) / 2 else 0 := by
    cases hlabel : label i <;>
      simp [W, directionalGaussianWeakRows, hlabel, directionalMonomialLoss]
  simp_rw [h]
  rw [← Finset.sum_filter]
  have hW : (Finset.univ.filter fun i => i ∈ W) = W := by simp
  rw [hW, ← Finset.sum_div, Finset.sum_add_distrib]
  push_cast [weakMonomialDegree]
  simp [W, add_comm]

/-- All monomials pass the endpoint strictly exactly when the largest
supported degree in that prefix passes strictly. -/
theorem directionalOrderedPrefix_all_monomials_iff_weakDegree {d m : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (hP : P ≠ 0)
    (ν : Fin m → ℝ) (label : Fin d → Option (Fin m)) (j : Fin m) :
    let W := directionalGaussianWeakRows label (Finset.univ.filter (· ≤ j))
    (∀ β ∈ P.support, 0 < directionalOrderedPrefix (directionalMonomialExponent ν label β) j) ↔
      (W.card : ℝ) + weakDegree W P < 2 * directionalOrderedPrefix ν j := by
  classical
  let W := directionalGaussianWeakRows label (Finset.univ.filter (· ≤ j))
  have hsupport : P.support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
  obtain ⟨α, hα, hαN⟩ := Finset.exists_mem_eq_sup _ hsupport (weakMonomialDegree W)
  change weakDegree W P = weakMonomialDegree W α at hαN
  constructor
  · intro h
    have hh := h α hα
    rw [directionalOrderedPrefix_monomial_eq_weakDegree] at hh
    change (W.card : ℝ) + (weakDegree W P : ℝ) < _
    rw [hαN]
    linarith
  · intro h β hβ
    rw [directionalOrderedPrefix_monomial_eq_weakDegree]
    have hb : weakMonomialDegree W β ≤ weakDegree W P := Finset.le_sup hβ
    have hb' : (weakMonomialDegree W β : ℝ) ≤ weakDegree W P := by exact_mod_cast hb
    change (W.card : ℝ) + (weakDegree W P : ℝ) < _ at h
    linarith

end UV.ContinueNetworkPrecision
