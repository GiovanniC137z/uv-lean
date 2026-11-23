import UV.ContinueNetworkOrdered

/-! The selected weights of each literal Gaussian monomial, grouped by
their routed Schwinger slots. A fixed unit Gaussian weight costs nothing. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace UV

variable {I : Type*} [Fintype I] {m : ℕ}

def directionalSelectedWeight (slot : I → Option (Fin m)) (t : Fin m → ℝ) (i : I) : ℝ :=
  (slot i).elim 1 t

def directionalMonomialLoss (γ : I → ℕ) (i : I) : ℝ := ((γ i : ℝ) + 1) / 2

def directionalMonomialExponent (ν : Fin m → ℝ) (slot : I → Option (Fin m))
    (γ : I → ℕ) (j : Fin m) : ℝ :=
  ν j - ∑ i ∈ Finset.univ.filter (fun i => slot i = some j), directionalMonomialLoss γ i

/-- The literal determinant and monomial powers written using positive
square roots of the selected Gaussian weights. -/
def directionalOrderedMonomial (ν : Fin m → ℝ) (slot : I → Option (Fin m))
    (γ : I → ℕ) (t : Fin m → ℝ) : ℝ≥0∞ :=
  directionalOrderedDensity ν t * ENNReal.ofReal
    ((∏ i, (Real.sqrt (directionalSelectedWeight slot t i))⁻¹) *
      ∏ i, ((Real.sqrt (directionalSelectedWeight slot t i))⁻¹) ^ γ i)

private theorem selectedWeight_root_factor {w : ℝ} (hw : 0 < w) (n : ℕ) :
    (Real.sqrt w)⁻¹ * ((Real.sqrt w)⁻¹) ^ n = w ^ (-(((n : ℝ) + 1) / 2)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hw.le, ← Real.rpow_mul_natCast hw.le,
    ← Real.rpow_add hw]
  congr 1
  ring

/-- Each selected row contributes half the dimension and half the
monomial degree to its proper Schwinger slot. -/
theorem directionalOrderedMonomial_eq_density (ν : Fin m → ℝ)
    (slot : I → Option (Fin m)) (γ : I → ℕ) (t : Fin m → ℝ) (ht : ∀ j, 0 < t j) :
    directionalOrderedMonomial ν slot γ t =
      directionalOrderedDensity (directionalMonomialExponent ν slot γ) t := by
  classical
  have hw (i : I) : 0 < directionalSelectedWeight slot t i := by
    unfold directionalSelectedWeight
    cases slot i with
    | none => exact zero_lt_one
    | some j => exact ht j
  let f (i : I) := ENNReal.ofReal
    ((directionalSelectedWeight slot t i) ^ (-(directionalMonomialLoss γ i)))
  have hgroup :
      (∏ i : I, f i) = ∏ j : Fin m, ENNReal.ofReal
        (t j ^ (-(∑ i ∈ Finset.univ.filter (fun i => slot i = some j),
          directionalMonomialLoss γ i))) := by
    rw [← Finset.prod_fiberwise Finset.univ slot f, Fintype.prod_option]
    have hn : (∏ i ∈ Finset.univ.filter (fun i => slot i = none), f i) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      simp [f, directionalSelectedWeight, (Finset.mem_filter.mp hi).2]
    rw [hn, one_mul]
    apply Finset.prod_congr rfl
    intro j _
    have he (i : I) (hi : i ∈ Finset.univ.filter (fun i => slot i = some j)) :
        f i = ENNReal.ofReal (t j ^ (-(directionalMonomialLoss γ i))) := by
      simp [f, directionalSelectedWeight, (Finset.mem_filter.mp hi).2]
    rw [Finset.prod_congr rfl he,
      ← ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.rpow_nonneg (ht j).le _),
      ← Real.rpow_sum_of_pos (ht j), Finset.sum_neg_distrib]
  unfold directionalOrderedMonomial
  rw [← Finset.prod_mul_distrib]
  have hf :
      ENNReal.ofReal (∏ i,
        (Real.sqrt (directionalSelectedWeight slot t i))⁻¹ *
          ((Real.sqrt (directionalSelectedWeight slot t i))⁻¹) ^ γ i) = ∏ i, f i := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity)]
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg ENNReal.ofReal (selectedWeight_root_factor (hw i) (γ i))
  rw [hf, hgroup]
  unfold directionalOrderedDensity
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (ht j).le _), ← Real.rpow_add (ht j)]
  congr 2
  unfold directionalMonomialExponent
  ring

theorem directionalOrderedMonomial_cost_eq (ν : Fin m → ℝ)
    (slot : I → Option (Fin m)) (γ : I → ℕ) :
    (∫⁻ t in directionalOrderedSet m, directionalOrderedMonomial ν slot γ t) =
      directionalOrderedCost (directionalMonomialExponent ν slot γ) := by
  unfold directionalOrderedCost
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (directionalOrderedSet_open m).measurableSet] with t ht
  exact directionalOrderedMonomial_eq_density ν slot γ t
    (fun j => ((directionalOrderedSet_mem_iff t).1 ht).2 j |>.1)

theorem directionalOrderedMonomial_cost_finite_iff (ν : Fin m → ℝ)
    (slot : I → Option (Fin m)) (γ : I → ℕ) :
    (∫⁻ t in directionalOrderedSet m, directionalOrderedMonomial ν slot γ t) < ⊤ ↔
      ∀ j, 0 < directionalOrderedPrefix (directionalMonomialExponent ν slot γ) j := by
  rw [directionalOrderedMonomial_cost_eq, directionalOrderedCost_finite_iff]

/-- The cumulative power is the sum of the original exponents minus
the losses of precisely the selected rows from the same prefix. -/
theorem directionalMonomialExponent_prefix (ν : Fin m → ℝ)
    (slot : I → Option (Fin m)) (γ : I → ℕ) (j : Fin m) :
    directionalOrderedPrefix (directionalMonomialExponent ν slot γ) j =
      directionalOrderedPrefix ν j -
        ∑ i : I, (slot i).elim 0 (fun k => if k ≤ j then directionalMonomialLoss γ i else 0) := by
  classical
  unfold directionalOrderedPrefix
  have hterm (k : Fin m) :
      (if k ≤ j then ν k else 0) -
          (∑ i : I, if k ≤ j ∧ slot i = some k then directionalMonomialLoss γ i else 0) =
        if k ≤ j then directionalMonomialExponent ν slot γ k else 0 := by
    by_cases hk : k ≤ j <;> simp [hk, directionalMonomialExponent, Finset.sum_filter]
  have hsum :
      (∑ k : Fin m, ∑ i : I,
        if k ≤ j ∧ slot i = some k then directionalMonomialLoss γ i else 0) =
      ∑ i : I, (slot i).elim 0 (fun k => if k ≤ j then directionalMonomialLoss γ i else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    cases slot i with
    | none => simp
    | some l =>
        have h (k : Fin m) : (if k ≤ j ∧ some l = some k then directionalMonomialLoss γ i else 0) =
            if k = l then (if l ≤ j then directionalMonomialLoss γ i else 0) else 0 := by
          by_cases hk : k = l
          · subst k
            simp
          · simp [hk, Ne.symm hk]
        simp only [h, Option.elim_some]
        simp
  rw [← hsum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => (hterm k).symm

end UV
