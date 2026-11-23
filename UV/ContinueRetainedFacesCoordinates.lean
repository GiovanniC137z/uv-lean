import UV.ContinueRetainedFacesGreedy
import UV.ContinueRetainedFacesRank

/-! Rank and determinant comparisons in the increasing-width
coordinates of each Schwinger sector. -/

noncomputable section

open Finset Function Set UV.ContinueNetworkPrecision
open scoped BigOperators Matrix

namespace UV

/-- Retain a concrete set of columns, with its original edge type. -/
def retainedColumns {ι E : Type*} (A : Matrix ι E ℝ) (S : Finset E) : Matrix ι S ℝ :=
  A.submatrix id Subtype.val

/-- Select the actual basis by scanning from the largest coordinate
down, then return its labels in the original increasing order. -/
def retainedIncreasingBasis {ι : Type*} {n : ℕ} (A : Matrix ι (Fin n) ℝ) : Finset (Fin n) :=
  (greedyRows (A.submatrix id Fin.rev).col n).map Fin.revPerm.toEmbedding

/-- Reindexing the diagonal widths and their columns leaves the
covariance determinant exactly invariant. -/
theorem retainedGramDet_reindex {ι E E' : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E] [Fintype E'] [DecidableEq E']
    (A : Matrix ι E ℝ) (e : E' ≃ E) (t : E' → ℝ) :
    retainedGramDet (A.submatrix id e) t = retainedGramDet A (t ∘ e.symm) := by
  unfold retainedGramDet
  congr 1
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.submatrix_apply, id_eq, Matrix.transpose_apply,
    Function.comp_apply]
  exact Fintype.sum_equiv e _ _ (by intro k; rw [e.symm_apply_apply])

/-- Actual ranks of restricted columns commute with relabelling the set. -/
theorem retainedColumns_rank_map {ι E E' : Type*} [Fintype ι] [Fintype E]
    (A : Matrix ι E ℝ) (e : E' ≃ E) (S : Finset E') :
    (retainedColumns (A.submatrix id e) S).rank =
      (retainedColumns A (S.map e.toEmbedding)).rank := by
  classical
  let e' : S ≃ S.map e.toEmbedding :=
    e.subtypeEquiv (fun i => by
      change i ∈ S ↔ e i ∈ S.map e.toEmbedding
      simp)
  change ((retainedColumns A (S.map e.toEmbedding)).submatrix (Equiv.refl ι) e').rank = _
  rw [Matrix.rank_submatrix]

/-- On increasing coordinates the basis loses exactly the rank defect of
the actual complementary columns. -/
theorem retainedIncreasingBasis_prefix_count {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (j : Fin n) :
    let S := Finset.univ.filter (fun i : Fin n => i ≤ j)
    (S.filter (· ∈ retainedIncreasingBasis A)).card =
      A.rank - (retainedColumns A Sᶜ).rank := by
  classical
  dsimp only
  let S := Finset.univ.filter (fun i : Fin n => i ≤ j)
  let A' := A.submatrix id Fin.rev
  let G := greedyRows A'.col n
  let k := n - (j.val + 1)
  have hkj : k ≤ n := Nat.sub_le _ _
  have hrev (i : Fin n) : i.rev.val < k ↔ ¬ i ≤ j := by
    simp only [k, Fin.val_rev, Fin.le_def]
    have hi := i.isLt
    have hj := j.isLt
    omega
  have hSm : (Finset.univ.filter (fun i : Fin n => i.val < k)).map Fin.revPerm.toEmbedding = Sᶜ := by
    ext i
    rw [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_compl, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    exact hrev i
  have hGp : ((retainedIncreasingBasis A).filter (fun i => ¬ i ≤ j)).card =
      (retainedColumns A Sᶜ).rank := by
    have hr := retainedGreedy_prefix_count A' k
    change (greedyRows A'.col k).card =
      (retainedColumns A' (Finset.univ.filter (fun i : Fin n => i.val < k))).rank at hr
    have hreindex := retainedColumns_rank_map A (Fin.revPerm (n := n))
      (Finset.univ.filter (fun i : Fin n => i.val < k))
    change (retainedColumns A' _).rank = _ at hreindex
    rw [hreindex, hSm] at hr
    rw [← hr, ← greedyRows_filter_prefix _ hkj]
    have hGf : (retainedIncreasingBasis A).filter (fun i => ¬ i ≤ j) =
        (G.filter (fun i => i.val < k)).map Fin.revPerm.toEmbedding := by
      ext i
      rw [Finset.mem_filter, retainedIncreasingBasis, Finset.mem_map_equiv, Finset.mem_map_equiv,
        Finset.mem_filter]
      apply and_congr_right
      intro _
      exact (hrev i).symm
    rw [hGf, Finset.card_map]
  have hG : (retainedIncreasingBasis A).card = A.rank := by
    unfold retainedIncreasingBasis
    rw [Finset.card_map, retainedGreedy_card]
    exact Matrix.rank_submatrix A (Equiv.refl ι) Fin.revPerm
  have hsum := Finset.filter_card_add_filter_neg_card_eq_card (s := retainedIncreasingBasis A)
    (fun i : Fin n => i ≤ j)
  rw [hGp, hG] at hsum
  have heq : S.filter (· ∈ retainedIncreasingBasis A) =
      (retainedIncreasingBasis A).filter (· ≤ j) := by
    ext i
    simp [S, and_comm]
  rw [heq]
  change _ = A.rank - (retainedColumns A Sᶜ).rank
  omega

/-- The same two-sided comparison on the source's smallest-to-largest
coordinates. -/
theorem retainedGramDet_increasing_comparison {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (A : Matrix ι (Fin n) ℝ) (hA : A.rank = Fintype.card ι) :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧ ∀ t : Fin n → ℝ,
      Monotone t → (∀ i, 0 ≤ t i) →
      lo * (∏ i ∈ retainedIncreasingBasis A, t i) ≤ retainedGramDet A t ∧
      retainedGramDet A t ≤ hi * (∏ i ∈ retainedIncreasingBasis A, t i) := by
  have hA' : (A.submatrix id Fin.rev).rank = Fintype.card ι :=
    (Matrix.rank_submatrix A (Equiv.refl ι) Fin.revPerm).trans hA
  obtain ⟨lo, hi, hlo, hhi, h⟩ := retainedGramDet_greedy_comparison _ hA'
  refine ⟨lo, hi, hlo, hhi, fun t hm ht => ?_⟩
  have hb := h (t ∘ Fin.rev) (fun i j hij => hm (Fin.rev_le_rev.mpr hij)) (fun i => ht _)
  have hB := retainedGramDet_reindex A (Fin.revPerm (n := n)) (t ∘ Fin.rev)
  change retainedGramDet (A.submatrix id Fin.rev) _ = _ at hB
  rw [hB] at hb
  have htime : (t ∘ Fin.rev) ∘ Fin.revPerm.symm = t := by
    funext i
    simp [Fin.revPerm]
  rw [htime] at hb
  simpa only [retainedIncreasingBasis, Finset.prod_map, Function.comp_apply] using hb

end UV
