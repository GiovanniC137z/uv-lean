import UV.ContinueRetainedFacesDeterminant
import UV.ContinueNetworkPrecisionGreedy
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev

/-! The retained basis is selected from the actual columns. Its prefix
losses are ranks of the complementary routed columns. -/

noncomputable section

open Function Set Finset UV.ContinueNetworkPrecision
open scoped BigOperators Matrix

namespace UV

private theorem retainedSpan_finrank_of_indep {V : Type*} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (v : Fin n → V) (S : Finset (Fin n))
    (h : LinearIndepOn ℝ v (S : Set (Fin n))) :
    Module.finrank ℝ (rowSpan v S) = S.card := by
  have hr : Set.range (fun i : (↑S : Set (Fin n)) => v i) = v '' (S : Set (Fin n)) :=
    by
      rw [show (fun i : (↑S : Set (Fin n)) => v i) = v ∘ Subtype.val from rfl,
        Set.range_comp, Subtype.range_coe_subtype]
      rfl
  rw [rowSpan, ← hr, finrank_span_eq_card h]
  exact Fintype.card_coe S

/-- A prefix of a greedy column basis has the rank of the actual scanned
column set. Here column labels are in descending width order. -/
theorem retainedGreedy_prefix_count {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (k : ℕ) :
    (greedyRows A.col k).card =
      (A.submatrix id (Subtype.val :
        (↑(Finset.univ.filter (fun i : Fin n => i.val < k)) : Set (Fin n)) → Fin n)).rank := by
  let S := Finset.univ.filter (fun i : Fin n => i.val < k)
  have hs : (S : Set (Fin n)) = {i | i.val < k} := by
    ext i
    simp [S]
  rw [← retainedSpan_finrank_of_indep _ _ (greedyRows_indep _ _),
    greedyRows_prefix_span_eq, Matrix.rank_eq_finrank_span_cols]
  have hr : A.col '' {i | i.val < k} = Set.range (fun i : (↑S : Set (Fin n)) => A.col i) := by
    rw [← hs]
    rw [show (fun i : (↑S : Set (Fin n)) => A.col i) = A.col ∘ Subtype.val from rfl,
      Set.range_comp, Subtype.range_coe_subtype]
    rfl
  rw [hr]
  rfl

/-- A greedy basis occupies as many positions in any scanned prefix as
any other independent column subset. -/
theorem retainedGreedy_card_prefix_ge {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (v : Fin n → V) (S : Finset (Fin n))
    (hS : LinearIndepOn ℝ v (S : Set (Fin n))) {k : ℕ} (hk : k ≤ n) :
    (S.filter (fun i => i.val < k)).card ≤
      ((greedyRows v n).filter fun i => i.val < k).card := by
  let P := S.filter (fun i => i.val < k)
  have hP : LinearIndepOn ℝ v (P : Set (Fin n)) := hS.mono (Finset.filter_subset _ _)
  change P.card ≤ _
  rw [greedyRows_filter_prefix _ hk,
    ← retainedSpan_finrank_of_indep _ _ hP, ← retainedSpan_finrank_of_indep _ _ (greedyRows_indep _ _),
    greedyRows_prefix_span_eq]
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  exact Set.image_mono (fun i hi => (Finset.mem_filter.mp hi).2)

private theorem retainedSorted_finrank_cut {n m : ℕ} (S : Finset (Fin n)) (hS : S.card = m)
    (j : Fin n) (i : Fin m) :
    S.orderEmbOfFin hS i ≤ j ↔ i.val < (S.filter (· ≤ j)).card := by
  let f := S.orderEmbOfFin hS
  have hcard : Fintype.card {k : Fin m // f k ≤ j} = (S.filter (· ≤ j)).card := by
    let e₁ : {k : Fin m // f k ≤ j} ≃ {a : S // a.1 ≤ j} :=
      (S.orderIsoOfFin hS).toEquiv.subtypeEquiv (fun _ => Iff.rfl)
    let e₂ : {a : S // a.1 ≤ j} ≃ (↑(S.filter (· ≤ j)) : Set (Fin n)) :=
        { toFun := fun a => ⟨a.1.1, Finset.mem_filter.mpr ⟨a.1.2, a.2⟩⟩
          invFun := fun a => ⟨⟨a.1, (Finset.mem_filter.mp a.2).1⟩, (Finset.mem_filter.mp a.2).2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    exact (Fintype.card_congr (e₁.trans e₂)).trans (Fintype.card_coe _)
  have H := Tuple.lt_card_le_iff_apply_le_of_monotone f j f.monotone i
  rw [hcard] at H
  exact H.symm

/-- Matching the ordered columns by position makes greedy basis products
maximal for decreasing nonnegative widths. -/
theorem retainedGreedy_prod_le {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (v : Fin n → V) (S : Finset (Fin n))
    (hS : LinearIndepOn ℝ v (S : Set (Fin n)))
    (hcard : S.card = (greedyRows v n).card) (t : Fin n → ℝ)
    (hmono : Antitone t) (ht : ∀ i, 0 ≤ t i) :
    (∏ i ∈ S, t i) ≤ ∏ i ∈ greedyRows v n, t i := by
  let G := greedyRows v n
  let f := S.orderEmbOfFin hcard
  let g := G.orderEmbOfFin rfl
  have hpos (i : Fin G.card) : g i ≤ f i := by
    have hcut := retainedGreedy_card_prefix_ge v S hS
      (k := (f i).val + 1) (f i).isLt
    simp only [Nat.lt_succ_iff, ← Fin.le_def] at hcut
    exact (retainedSorted_finrank_cut G rfl (f i) i).mpr
      (((retainedSorted_finrank_cut S hcard (f i) i).mp le_rfl).trans_le hcut)
  have hprod := Finset.prod_le_prod
    (s := Finset.univ) (f := t ∘ f) (g := t ∘ g) (fun i _ => ht (f i))
    (fun i _ => hmono (hpos i))
  have hf : Finset.univ.map f.toEmbedding = S := Finset.map_orderEmbOfFin_univ S hcard
  have hg : Finset.univ.map g.toEmbedding = G := Finset.map_orderEmbOfFin_univ G rfl
  change (∏ i ∈ S, t i) ≤ ∏ i ∈ G, t i
  rw [← hf, ← hg, Finset.prod_map, Finset.prod_map]
  exact hprod

private theorem retainedMinorCoefficient_pos_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (A : Matrix ι (Fin n) ℝ) (S : Finset (Fin n))
    (hS : S.card = Fintype.card ι) :
    0 < retainedMinorCoefficient A S ↔ LinearIndepOn ℝ A.col (S : Set (Fin n)) := by
  classical
  let e : ι ≃ S := Fintype.equivOfCardEq (by simp [hS])
  let B : Matrix ι ι ℝ := A.submatrix id (Subtype.val ∘ e)
  have hcomp : B.col = (fun i : (↑S : Set (Fin n)) => A.col i) ∘ e := rfl
  rw [retainedMinorCoefficient, dif_pos hS]
  change 0 < B.det ^ 2 ↔ _
  rw [sq_pos_iff, ← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.linearIndependent_cols_iff_isUnit, hcomp]
  exact linearIndependent_equiv e

theorem retainedGreedy_card {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) : (greedyRows A.col n).card = A.rank := by
  rw [← retainedSpan_finrank_of_indep _ _ (greedyRows_indep _ _),
    greedyRows_prefix_span_eq, Matrix.rank_eq_finrank_span_cols]
  have huniv : {i : Fin n | i.val < n} = Set.univ := Set.eq_univ_of_forall Fin.isLt
  rw [huniv, Set.image_univ]

/-- The genuine retained determinant is bounded above and below by the
maximal greedy basis monomial, with strictly positive width-independent
constants at full row rank. -/
theorem retainedGramDet_greedy_comparison {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (A : Matrix ι (Fin n) ℝ) (hA : A.rank = Fintype.card ι) :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧ ∀ t : Fin n → ℝ,
      Antitone t → (∀ i, 0 ≤ t i) →
      lo * (∏ i ∈ greedyRows A.col n, t i) ≤ retainedGramDet A t ∧
      retainedGramDet A t ≤ hi * (∏ i ∈ greedyRows A.col n, t i) := by
  classical
  let G := greedyRows A.col n
  let T := (Finset.univ : Finset (Fin n)).powersetCard (Fintype.card ι)
  have hcard : G.card = Fintype.card ι := (retainedGreedy_card A).trans hA
  have hG : G ∈ T := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
  have hpos : 0 < retainedMinorCoefficient A G :=
    (retainedMinorCoefficient_pos_iff A G hcard).mpr (greedyRows_indep _ _)
  refine ⟨retainedMinorCoefficient A G, ∑ S ∈ T, retainedMinorCoefficient A S,
    hpos, hpos.trans_le (Finset.single_le_sum (fun S _ => retainedMinorCoefficient_nonneg A S) hG),
    ?_⟩
  intro t hmono ht
  rw [retainedGramDet_eq_basis_sum]
  constructor
  · exact Finset.single_le_sum (f := fun S => retainedMinorCoefficient A S * ∏ i ∈ S, t i)
      (fun S _ => mul_nonneg (retainedMinorCoefficient_nonneg A S)
        (Finset.prod_nonneg fun i _ => ht i)) hG
  · rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro S hS
    by_cases hz : retainedMinorCoefficient A S = 0
    · simp [hz]
    · have hc := (Finset.mem_powersetCard.mp hS).2
      have hp := lt_of_le_of_ne (retainedMinorCoefficient_nonneg A S) (Ne.symm hz)
      have hSI := (retainedMinorCoefficient_pos_iff A S hc).mp hp
      exact mul_le_mul_of_nonneg_left
        (retainedGreedy_prod_le A.col S hSI (hc.trans hcard.symm) t hmono ht) hp.le

end UV
