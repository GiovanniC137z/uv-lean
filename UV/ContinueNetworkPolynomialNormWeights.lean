import UV.ContinueNetworkPolynomialNorm

/-! Regrouping the exact diagonal coefficient budget by the selected
row's Schwinger parameter. Rows selected from the undamped-parameter
Gaussian block have weight one. -/

noncomputable section
open scoped BigOperators

namespace UV

variable {d : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

theorem directionalGaussianCoefficientBudget_monomials {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) (P : MvPolynomial (Fin d) ℂ) :
    directionalGaussianCoefficientBudget w P =
      ∑ β ∈ P.support, ‖P.coeff β‖ * ∏ i, (w i)^(-(1+(β i : ℝ))/2) := by
  unfold directionalGaussianCoefficientBudget
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  rw [mul_left_comm (∏ i, w i ^ (-(1 / 2 : ℝ))) ‖P.coeff β‖, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [← Real.rpow_add (hw i)]
  congr 1
  ring

def directionalGaussianRowWeights (label : Fin d → Option E) (t : E → ℝ) : Fin d → ℝ :=
  fun i => (label i).elim 1 t

omit [Fintype E] [DecidableEq E] in
theorem directionalGaussianRowWeights_pos (label : Fin d → Option E) {t : E → ℝ}
    (ht : ∀ e, 0 < t e) (i : Fin d) : 0 < directionalGaussianRowWeights label t i := by
  unfold directionalGaussianRowWeights
  cases h : label i with
  | none => exact zero_lt_one
  | some e => exact ht e

def directionalGaussianEdgeCost (label : Fin d → Option E) (β : Fin d →₀ ℕ) (e : E) : ℕ :=
  ∑ i : {i // label i = some e}, (1+β i)

omit [Fintype E] in
/-- Each selected edge row contributes one dimension plus its monomial degree. -/
theorem directionalGaussianEdgeCost_count (label : Fin d → Option E) (β : Fin d →₀ ℕ)
    (e : E) :
    directionalGaussianEdgeCost label β e =
      Fintype.card {i // label i = some e} + ∑ i : {i // label i = some e}, β i := by
  simp [directionalGaussianEdgeCost, Finset.sum_add_distrib]

theorem directionalGaussianMonomial_grouped_weights (label : Fin d → Option E)
    {t : E → ℝ} (ht : ∀ e, 0 < t e) (β : Fin d →₀ ℕ) :
    (∏ i, (directionalGaussianRowWeights label t i)^(-(1+(β i : ℝ))/2)) =
      ∏ e, (t e)^(-(directionalGaussianEdgeCost label β e : ℝ)/2) := by
  rw [← Fintype.prod_fiberwise label, Fintype.prod_option]
  have hNone :
      (∏ i : {i // label i = none}, directionalGaussianRowWeights label t i ^
        (-(1+(β i : ℝ))/2)) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    simp [directionalGaussianRowWeights, i.property]
  rw [hNone, one_mul]
  apply Finset.prod_congr rfl
  intro e _
  have hprod : (∏ i : {i // label i = some e}, directionalGaussianRowWeights label t i ^
      (-(1+(β i : ℝ))/2)) =
       ∏ i : {i // label i = some e}, t e ^ (-(1+(β i : ℝ))/2) := by
    apply Finset.prod_congr rfl
    intro i _
    simp [directionalGaussianRowWeights, i.property]
  rw [hprod, ← Real.rpow_sum_of_pos (ht e)]
  congr 1
  push_cast [directionalGaussianEdgeCost]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_div]

/-- The full Schwinger density after the Gaussian monomial comparison.
An edge parameter contributes its original power diminished by one half
the number-plus-degree of the selected coordinates with that label. -/
theorem directionalGaussianCoefficientBudget_schwinger (label : Fin d → Option E)
    {t : E → ℝ} (ht : ∀ e, 0 < t e) (ν : E → ℝ) (P : MvPolynomial (Fin d) ℂ) :
    (∏ e, (t e)^(ν e-1)) *
      directionalGaussianCoefficientBudget (directionalGaussianRowWeights label t) P =
    ∑ β ∈ P.support, ‖P.coeff β‖ *
      ∏ e, (t e)^(ν e-(directionalGaussianEdgeCost label β e : ℝ)/2-1) := by
  rw [directionalGaussianCoefficientBudget_monomials (directionalGaussianRowWeights_pos label ht),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  rw [directionalGaussianMonomial_grouped_weights label ht, mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro e _
  rw [← Real.rpow_add (ht e)]
  congr 1
  ring

def directionalGaussianWeakRows (label : Fin d → Option E) (S : Finset E) : Finset (Fin d) :=
  Finset.univ.filter (fun i => label i ∈ S.map ⟨some, Option.some_injective E⟩)

omit [Fintype E] in
/-- The prefix power is the number of weak coordinates plus the degree
of the specified monomial along those same coordinates. -/
theorem directionalGaussianEdgeCost_sum_set (label : Fin d → Option E)
    (S : Finset E) (β : Fin d →₀ ℕ) :
    (∑ e ∈ S, directionalGaussianEdgeCost label β e) =
      (directionalGaussianWeakRows label S).card + ∑ i ∈ directionalGaussianWeakRows label S, β i := by
  let embed : E ↪ Option E := ⟨some, Option.some_injective E⟩
  have hf := Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset (Fin d))
    (S.map embed) label (fun i => 1+β i)
  rw [Finset.sum_map] at hf
  change (∑ e ∈ S, ∑ i ∈ (Finset.univ.filter (fun i => label i = some e)), (1+β i)) =
    ∑ i ∈ directionalGaussianWeakRows label S, (1+β i) at hf
  have he : (∑ i ∈ directionalGaussianWeakRows label S, (1+β i)) =
      (directionalGaussianWeakRows label S).card + ∑ i ∈ directionalGaussianWeakRows label S, β i := by
    simp [Finset.sum_add_distrib]
  rw [← he, ← hf]
  apply Finset.sum_congr rfl
  intro e _
  unfold directionalGaussianEdgeCost
  exact (Finset.sum_subtype _ (by simp) (fun i => 1+β i)).symm

end UV
