import UV.ContinueNetworkPrecisionGreedy
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

/-! The literal Euclidean block rows, with the fixed Gaussian block first
and the positive Schwinger weights in decreasing order after it. -/

noncomputable section

open scoped BigOperators

namespace UV.ContinueNetworkPrecision

/-- Enumerate every row once, placing its coarse block tag in increasing
order. The tie-breaking order is independent of the Schwinger values. -/
theorem exists_ordered_row_enumeration {α β : Type*} [Fintype α] [LinearOrder β] (tag : α → β) :
    ∃ e : Fin (Fintype.card α) ≃ α, Monotone (tag ∘ e) := by
  classical
  let idx := Fintype.equivFin α
  let key (x : α) : β ×ₗ Fin (Fintype.card α) := toLex (tag x, idx x)
  have hkey : Function.Injective key := by
    intro a b h
    exact idx.injective (congrArg (fun q : β ×ₗ Fin (Fintype.card α) => (ofLex q).2) h)
  letI : LinearOrder α := LinearOrder.lift' key hkey
  let e : Fin (Fintype.card α) ≃o ↥(Finset.univ : Finset α) :=
    Finset.orderIsoOfFin _ Finset.card_univ
  let d : ↥(Finset.univ : Finset α) ≃ α :=
    { toFun := Subtype.val
      invFun := fun a => ⟨a, Finset.mem_univ a⟩
      left_inv := fun a => Subtype.ext rfl
      right_inv := fun _ => rfl }
  refine ⟨e.toEquiv.trans d, fun i j hij => ?_⟩
  have h : key (e i).1 ≤ key (e j).1 := e.monotone hij
  exact (Prod.Lex.toLex_le_toLex'.mp h).1

/-- Tier zero is the unchanged Gaussian weight. The other tiers use the
same Schwinger slots, put in reverse order so the strongest is first. -/
def schwingerTierWeight {m : ℕ} (t : Fin m → ℝ) : Fin (m+1) → ℝ :=
  Fin.cases 1 (fun i => t i.rev)

theorem schwingerTierWeight_nonneg {m : ℕ} (t : Fin m → ℝ) (ht : ∀ i, 0 ≤ t i) :
    ∀ i, 0 ≤ schwingerTierWeight t i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact zero_le_one
  · exact ht j.rev

theorem schwingerTierWeight_antitone {m : ℕ} (t : Fin m → ℝ) (ht : Monotone t) (h1 : ∀ i, t i ≤ 1) :
    Antitone (schwingerTierWeight t) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact le_rfl
    | succ j => exact h1 j.rev
  | succ i =>
    induction j using Fin.cases with
    | zero => exact (not_le_of_gt (Fin.succ_pos i) hij).elim
    | succ j => exact ht (Fin.rev_le_rev.mpr (Fin.succ_le_succ_iff.mp hij))

abbrev NetworkRowLabel (a m : ℕ) (b : Fin m → ℕ) := Fin a ⊕ (Σ e : Fin m, Fin (b e))

/-- The actual Gaussian rows precede every route. The row block of a
route remembers its original Schwinger index. -/
def sourceRowTier {a m : ℕ} {b : Fin m → ℕ} : NetworkRowLabel a m b → Fin (m+1)
  | .inl _ => 0
  | .inr ei => ei.1.rev.succ

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {a m : ℕ} {b : Fin m → ℕ}

/-- The components of the original Euclidean Gaussian map and routed
vectors, with no direction or momentum rescaling. -/
def sourceRowForm (A : V →ₗ[ℝ] DirectionalMomentum a)
    (C : ∀ e, V →ₗ[ℝ] DirectionalMomentum (b e)) : NetworkRowLabel a m b → V →ₗ[ℝ] ℝ
  | .inl i => (EuclideanSpace.projₗ i).comp A
  | .inr ei => (EuclideanSpace.projₗ ei.2).comp (C ei.1)

/-- The quadratic precision in the literal Gaussian after Schwinger
parameterization, before taking the independent selected rows. -/
def sourcePrecision (A : V →ₗ[ℝ] DirectionalMomentum a)
    (C : ∀ e, V →ₗ[ℝ] DirectionalMomentum (b e)) (t : Fin m → ℝ) (k : V) : ℝ :=
  ‖A k‖^2 + ∑ e, t e * ‖C e k‖^2

/-- The full row sum is exactly the physical Schwinger precision. The
ordering permutes the rows but cannot change any term. -/
theorem sourcePrecision_eq_rows (A : V →ₗ[ℝ] DirectionalMomentum a)
    (C : ∀ e, V →ₗ[ℝ] DirectionalMomentum (b e))
    (e : Fin (Fintype.card (NetworkRowLabel a m b)) ≃ NetworkRowLabel a m b)
    (t : Fin m → ℝ) (k : V) :
    rowPrecision (sourceRowForm A C ∘ e) (schwingerTierWeight t ∘ sourceRowTier ∘ e) k =
      sourcePrecision A C t k := by
  unfold rowPrecision sourcePrecision
  let F (l : NetworkRowLabel a m b) := schwingerTierWeight t (sourceRowTier l) * (sourceRowForm A C l k)^2
  change (∑ i, F (e i)) = _
  rw [Equiv.sum_comp e]
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma, F, sourceRowTier, sourceRowForm,
    schwingerTierWeight, Fin.cases_zero, Fin.cases_succ, Fin.rev_rev, LinearMap.comp_apply, one_mul]
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, Finset.mul_sum]
  rfl

/-- With the actual largest-weight-first row enumeration, the literal
source precision is bounded above and below by the greedy diagonal form
with constants independent of all ordered Schwinger parameters. -/
theorem source_greedy_precision_compare (A : V →ₗ[ℝ] DirectionalMomentum a)
    (C : ∀ e, V →ₗ[ℝ] DirectionalMomentum (b e)) :
    ∃ (e : Fin (Fintype.card (NetworkRowLabel a m b)) ≃ NetworkRowLabel a m b) (D : ℝ),
      Monotone (sourceRowTier ∘ e) ∧ 1 ≤ D ∧
      ∀ (t : Fin m → ℝ) (k : V), Monotone t → (∀ j, 0 ≤ t j) → (∀ j, t j ≤ 1) →
        let rows := sourceRowForm A C ∘ e
        let w := schwingerTierWeight t ∘ sourceRowTier ∘ e
        selectedPrecision rows (greedyRows rows (Fintype.card (NetworkRowLabel a m b))) w k ≤
          sourcePrecision A C t k ∧
        sourcePrecision A C t k ≤ D *
          selectedPrecision rows (greedyRows rows (Fintype.card (NetworkRowLabel a m b))) w k := by
  obtain ⟨e,he⟩ := exists_ordered_row_enumeration (sourceRowTier (a := a) (b := b))
  obtain ⟨D,hD,hcmp⟩ := greedy_precision_compare (sourceRowForm A C ∘ e)
  refine ⟨e,D,he,hD,fun t k ht h0 h1 => ?_⟩
  dsimp only
  rw [← sourcePrecision_eq_rows A C e t k]
  exact hcmp _ k (fun r => schwingerTierWeight_nonneg t h0 (sourceRowTier (e r)))
    ((schwingerTierWeight_antitone t ht h1).comp_monotone he)

end UV.ContinueNetworkPrecision
