import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Fintype.Sum

/-! The score rank on a retained set of columns controls which deletion
minors add a width loss. The seam rows are kept for every deletion. -/

noncomputable section

open Function Set Submodule
open scoped BigOperators

namespace UV

private theorem retainedRank_sup (V : Type*) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (T U : Submodule ℝ V) :
    Module.finrank ℝ ↥(T ⊔ U) = Module.finrank ℝ T + Module.finrank ℝ (U.map T.mkQ) := by
  have hk : Module.finrank ℝ (LinearMap.ker (T.mkQ.domRestrict (T ⊔ U))) =
      Module.finrank ℝ T := by
    rw [LinearMap.ker_domRestrict, Submodule.ker_mkQ]
    exact (Submodule.comapSubtypeEquivOfLe (le_sup_left : T ≤ T ⊔ U)).finrank_eq
  have hr : LinearMap.range (T.mkQ.domRestrict (T ⊔ U)) = U.map T.mkQ := by
    rw [LinearMap.range_domRestrict, Submodule.map_sup]
    have ht : T.map T.mkQ = ⊥ := by
      apply le_antisymm _ bot_le
      rintro _ ⟨x, hx, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero T).mpr hx
    rw [ht, bot_sup_eq]
  have h := (T.mkQ.domRestrict (T ⊔ U)).finrank_range_add_finrank_ker
  rw [hr, hk, add_comm] at h
  exact h.symm

/-- The score rows relative to the seam span are the score rows projected
into the actual quotient. -/
theorem retainedRank_relative {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (T : Submodule ℝ V) (v : ι → V) :
    Module.finrank ℝ ↥(T ⊔ Submodule.span ℝ (Set.range v)) =
      Module.finrank ℝ T + Module.finrank ℝ (Submodule.span ℝ (Set.range (T.mkQ ∘ v))) := by
  rw [retainedRank_sup, Submodule.map_span, Set.range_comp]

private theorem retainedRank_delete_span {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    (v : ι → V) (j : ι) :
    Submodule.span ℝ (Set.range v) =
      Submodule.span ℝ {v j} ⊔ Submodule.span ℝ (v '' {i | i ≠ j}) := by
  have hr : Set.range v = insert (v j) (v '' {i | i ≠ j}) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      by_cases hij : i = j
      · subst i
        exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ ⟨i, hij, rfl⟩
    · rintro (rfl | ⟨i, _, rfl⟩)
      · exact ⟨j, rfl⟩
      · exact ⟨i, rfl⟩
  rw [hr, Submodule.span_insert]

/-- A single score-row deletion removes either zero or one dimension. -/
theorem retainedRank_delete_bounds {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (T : Submodule ℝ V) (v : ι → V) (j : ι) :
    let r := Module.finrank ℝ ↥(T ⊔ Submodule.span ℝ (Set.range v))
    let r' := Module.finrank ℝ ↥(T ⊔ Submodule.span ℝ (v '' {i | i ≠ j}))
    r' ≤ r ∧ r ≤ r' + 1 := by
  dsimp only
  let D := Submodule.span ℝ (v '' {i | i ≠ j})
  let J := Submodule.span ℝ {v j}
  rw [retainedRank_delete_span v j]
  change Module.finrank ℝ ↥(T ⊔ D) ≤ Module.finrank ℝ ↥(T ⊔ (J ⊔ D)) ∧
    Module.finrank ℝ ↥(T ⊔ (J ⊔ D)) ≤ Module.finrank ℝ ↥(T ⊔ D) + 1
  have hA : T ⊔ (J ⊔ D) = (T ⊔ D) ⊔ J := by ac_rfl
  rw [hA]
  refine ⟨Submodule.finrank_mono le_sup_left, ?_⟩
  have hsum := (T ⊔ D).finrank_sup_add_finrank_inf_eq J
  have hJ : Module.finrank ℝ J ≤ 1 := finrank_span_le_card _ |>.trans (by simp)
  omega

/-- A score row can be deleted with no loss of rank exactly when the
relative score rows fail to attain their full cardinality. -/
theorem retainedRank_delete_exists_iff {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [Fintype ι] (T : Submodule ℝ V) (v : ι → V) :
    (∃ j : ι, Module.finrank ℝ ↥(T ⊔ Submodule.span ℝ (v '' {i | i ≠ j})) =
      Module.finrank ℝ ↥(T ⊔ Submodule.span ℝ (Set.range v))) ↔
      Module.finrank ℝ ↥(T ⊔ Submodule.span ℝ (Set.range v)) - Module.finrank ℝ T <
        Fintype.card ι := by
  classical
  let w := T.mkQ ∘ v
  have hrel (j : ι) :
      Module.finrank ℝ ↥(T ⊔ Submodule.span ℝ (v '' {i | i ≠ j})) =
        Module.finrank ℝ T + Module.finrank ℝ (Submodule.span ℝ (w '' {i | i ≠ j})) := by
    rw [retainedRank_sup, Submodule.map_span, Set.image_image]
    rfl
  simp_rw [hrel]
  rw [retainedRank_relative T v]
  change (∃ j, Module.finrank ℝ T + Module.finrank ℝ (Submodule.span ℝ (w '' {i | i ≠ j})) =
    Module.finrank ℝ T + Module.finrank ℝ (Submodule.span ℝ (Set.range w))) ↔ _
  simp only [Nat.add_left_cancel_iff, Nat.add_sub_cancel_left]
  constructor
  · rintro ⟨j, hj⟩
    rw [← hj]
    have hr : w '' {i | i ≠ j} = Set.range (fun i : {i : ι // i ≠ j} => w i) := by
      ext x
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, hi⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i, i.2, rfl⟩
    rw [hr]
    apply (finrank_range_le_card _).trans_lt
    change Fintype.card {i : ι // ¬ i = j} < Fintype.card ι
    rw [Fintype.card_subtype_compl]
    have hj' : Fintype.card {i : ι // i = j} = 1 := by simp
    rw [hj']
    exact Nat.sub_lt (Fintype.card_pos_iff.mpr ⟨j⟩) zero_lt_one
  · intro h
    have hdep : ¬ LinearIndependent ℝ w := fun hind =>
      (lt_irrefl _ (finrank_span_eq_card hind ▸ h))
    have hmem : ∃ j, w j ∈ Submodule.span ℝ (w '' (univ \ {j})) := by
      by_contra hn
      exact hdep (linearIndependent_iff_notMem_span.mpr (fun j h => hn ⟨j, h⟩))
    obtain ⟨j, hj⟩ := hmem
    refine ⟨j, ?_⟩
    have hs : univ \ {j} = {i : ι | i ≠ j} := by ext; simp
    rw [hs] at hj
    rw [retainedRank_delete_span w j, sup_eq_right.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr hj)]

/-- The matrix obtained by deleting score row `j`, with all seam rows
kept. Row type distinguishes seam and score without coordinate aliases. -/
def retainedScoreDelete {ι κ E : Type*} (A : Matrix (ι ⊕ κ) E ℝ) (j : κ) :
    Matrix (ι ⊕ {i : κ // i ≠ j}) E ℝ :=
  A.submatrix (Sum.map id Subtype.val) id

private theorem retainedRank_matrix_row_span {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [Fintype E] (A : Matrix (ι ⊕ κ) E ℝ) :
    A.rank = Module.finrank ℝ ↥(Submodule.span ℝ (Set.range (A.row ∘ Sum.inl)) ⊔
      Submodule.span ℝ (Set.range (A.row ∘ Sum.inr))) := by
  rw [Matrix.rank_eq_finrank_span_row, ← Submodule.span_union]
  have hr : Set.range A.row = Set.range (A.row ∘ Sum.inl) ∪ Set.range (A.row ∘ Sum.inr) := by
    ext x
    constructor
    · rintro ⟨i | j, rfl⟩
      · exact Or.inl ⟨i, rfl⟩
      · exact Or.inr ⟨j, rfl⟩
    · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr j, rfl⟩
  rw [hr]

private theorem retainedRank_matrix_delete_span {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [Fintype E] [DecidableEq κ] (A : Matrix (ι ⊕ κ) E ℝ) (j : κ) :
    (retainedScoreDelete A j).rank =
      Module.finrank ℝ ↥(Submodule.span ℝ (Set.range (A.row ∘ Sum.inl)) ⊔
        Submodule.span ℝ ((A.row ∘ Sum.inr) '' {i : κ | i ≠ j})) := by
  rw [retainedRank_matrix_row_span]
  have hr : Set.range ((retainedScoreDelete A j).row ∘ Sum.inr) =
      (A.row ∘ Sum.inr) '' {i : κ | i ≠ j} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [hr]
  rfl

/-- The actual retained score-deletion rank differs by at most one. -/
theorem retainedScoreDelete_rank_bounds {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [Fintype E] [DecidableEq κ] (A : Matrix (ι ⊕ κ) E ℝ) (j : κ) :
    (retainedScoreDelete A j).rank ≤ A.rank ∧ A.rank ≤ (retainedScoreDelete A j).rank + 1 := by
  rw [retainedRank_matrix_delete_span, retainedRank_matrix_row_span]
  exact retainedRank_delete_bounds _ _ _

/-- The criterion applies to the matrix on any chosen complementary
column set, with no assumption on that restricted matrix's row rank. -/
theorem retainedScoreDelete_preserves_rank_iff {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [Fintype E] [DecidableEq κ] (A : Matrix (ι ⊕ κ) E ℝ) :
    (∃ j : κ, (retainedScoreDelete A j).rank = A.rank) ↔
      A.rank - (A.submatrix Sum.inl id).rank < Fintype.card κ := by
  simp_rw [retainedRank_matrix_delete_span]
  rw [retainedRank_matrix_row_span A, Matrix.rank_eq_finrank_span_row]
  exact retainedRank_delete_exists_iff _ _

end UV
