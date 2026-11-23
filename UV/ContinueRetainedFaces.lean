import UV.ContinueRetainedFacesCoordinates
import UV.ContinueRetainedFacesPowers

/-! The retained-width power count for the actual routed determinant
and its score-deletion cofactors. -/

noncomputable section

open Function Set Finset MeasureTheory Filter
open scoped BigOperators ENNReal

namespace UV

/-- Full retained rank defect of a width face. -/
def retainedWidthDefect {ι κ : Type*} [Fintype ι] [Fintype κ]
    {n : ℕ} (A : Matrix (ι ⊕ κ) (Fin n) ℝ) (S : Finset (Fin n)) : ℕ :=
  Fintype.card (ι ⊕ κ) - (retainedColumns A Sᶜ).rank

/-- The remaining score rank above the seam rank on a width face. -/
def retainedWidthMissingScore {ι κ : Type*} [Fintype ι] [Fintype κ]
    {n : ℕ} (A : Matrix (ι ⊕ κ) (Fin n) ℝ) (S : Finset (Fin n)) : Prop :=
  let C := retainedColumns A Sᶜ
  C.rank - (C.submatrix Sum.inl id).rank < Fintype.card κ

instance retainedWidthMissingScoreDecidable {ι κ : Type*} [Fintype ι] [Fintype κ]
    {n : ℕ} (A : Matrix (ι ⊕ κ) (Fin n) ℝ) : DecidablePred (retainedWidthMissingScore A) :=
  fun _ => inferInstanceAs (Decidable (_ < _ : Prop))

/-- Full rank remains full rank after deletion of any score row. -/
theorem retainedScoreDelete_full_rank {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [Fintype E] [DecidableEq κ] (A : Matrix (ι ⊕ κ) E ℝ) (j : κ)
    (hA : A.rank = Fintype.card (ι ⊕ κ)) :
    (retainedScoreDelete A j).rank = Fintype.card (ι ⊕ {i : κ // i ≠ j}) := by
  have hlin : LinearIndependent ℝ A.row := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    exact hA.symm.trans (Matrix.rank_eq_finrank_span_row A)
  have hmap : Injective (Sum.map (id : ι → ι) (Subtype.val : {i : κ // i ≠ j} → κ)) := by
    intro a b hab
    cases a <;> cases b <;> simp_all [Subtype.ext_iff]
  have hsub : LinearIndependent ℝ (retainedScoreDelete A j).row :=
    hlin.comp (Sum.map id Subtype.val) hmap
  exact hsub.rank_matrix

private theorem retainedScoreDelete_card_add_one {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (j : κ) :
    Fintype.card (ι ⊕ {i : κ // i ≠ j}) + 1 = Fintype.card (ι ⊕ κ) := by
  rw [Fintype.card_sum, Fintype.card_sum]
  change Fintype.card ι + Fintype.card {i : κ // ¬ i = j} + 1 = _
  rw [Fintype.card_subtype_compl]
  have he : Fintype.card {i : κ // i = j} = 1 := by simp
  rw [he]
  have hp := Fintype.card_pos_iff.mpr ⟨j⟩
  omega

private theorem retainedColumns_map_compl {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    (retainedColumns (A.submatrix id σ) Sᶜ).rank =
      (retainedColumns A (S.map σ.toEmbedding)ᶜ).rank := by
  rw [retainedColumns_rank_map]
  have hcomp : Sᶜ.map σ.toEmbedding = (S.map σ.toEmbedding)ᶜ := by
    ext i
    simp only [Finset.mem_compl, Finset.mem_map_equiv]
  rw [hcomp]

private theorem retainedRank_reindex_columns {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (σ : Equiv.Perm (Fin n)) :
    (A.submatrix id σ).rank = A.rank :=
  Matrix.rank_submatrix A (Equiv.refl ι) σ

private theorem retainedPrefix_defect {ι κ : Type*} [Fintype ι] [Fintype κ]
    {n : ℕ} (A : Matrix (ι ⊕ κ) (Fin n) ℝ) (hA : A.rank = Fintype.card (ι ⊕ κ))
    (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    let S := Finset.univ.filter (fun i : Fin n => i ≤ j)
    let B := retainedIncreasingBasis (A.submatrix id σ)
    retainedWidthDefect A (S.map σ.toEmbedding) = (S.filter (· ∈ B)).card := by
  dsimp only
  rw [retainedIncreasingBasis_prefix_count, retainedColumns_map_compl A σ,
    retainedRank_reindex_columns A σ, hA]
  rfl

private theorem retainedPrefix_score_loss {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {n : ℕ} (A : Matrix (ι ⊕ κ) (Fin n) ℝ) (hA : A.rank = Fintype.card (ι ⊕ κ))
    (σ : Equiv.Perm (Fin n)) (q : κ) (j : Fin n) :
    let S := Finset.univ.filter (fun i : Fin n => i ≤ j)
    let B := retainedIncreasingBasis (A.submatrix id σ)
    let D := retainedIncreasingBasis ((retainedScoreDelete A q).submatrix id σ)
    let C := retainedColumns A (S.map σ.toEmbedding)ᶜ
    ((S.filter (· ∈ B)).card : ℝ) - ((S.filter (· ∈ D)).card : ℝ) =
      if (retainedScoreDelete C q).rank = C.rank then 1 else 0 := by
  dsimp only
  rw [retainedIncreasingBasis_prefix_count, retainedIncreasingBasis_prefix_count,
    retainedColumns_map_compl A σ, retainedColumns_map_compl (retainedScoreDelete A q) σ,
    retainedRank_reindex_columns A σ, retainedRank_reindex_columns (retainedScoreDelete A q) σ, hA, retainedScoreDelete_full_rank A q hA]
  let S := Finset.univ.filter (fun i : Fin n => i ≤ j)
  let C := retainedColumns A (S.map σ.toEmbedding)ᶜ
  change ((Fintype.card (ι ⊕ κ) - C.rank : ℕ) : ℝ) -
    ((Fintype.card (ι ⊕ {i : κ // i ≠ q}) - (retainedScoreDelete C q).rank : ℕ) : ℝ) = _
  have hcard := retainedScoreDelete_card_add_one (ι := ι) q
  have hdiff := retainedScoreDelete_rank_bounds C q
  have hC := C.rank_le_card_height
  have hD := (retainedScoreDelete C q).rank_le_card_height
  rw [Nat.cast_sub hC, Nat.cast_sub hD]
  have hcard' : (Fintype.card (ι ⊕ {i : κ // i ≠ q}) : ℝ) + 1 =
      (Fintype.card (ι ⊕ κ) : ℝ) := by exact_mod_cast hcard
  by_cases he : (retainedScoreDelete C q).rank = C.rank
  · rw [if_pos he, he]
    linarith
  · have hr : C.rank = (retainedScoreDelete C q).rank + 1 := by omega
    have hr' : (C.rank : ℝ) = ((retainedScoreDelete C q).rank : ℝ) + 1 := by exact_mod_cast hr
    rw [if_neg he, hr']
    linarith

/-- Width-face criterion for any extended coefficient density comparable
to the routed basis models on each sector. The rank tests here are ranks
of actual matrix restrictions, including every seam row. -/
theorem retainedRoutedWidths_finite_iff_faces {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {n : ℕ} (A : Matrix (ι ⊕ κ) (Fin n) ℝ) (hA : A.rank = Fintype.card (ι ⊕ κ))
    (β : Fin n → ℝ) {h : ℝ} (hh : 0 ≤ h) (F : (Fin n → ℝ) → ℝ≥0∞)
    (bounds : ∀ σ : Equiv.Perm (Fin n), ∃ lo hi : ℝ≥0∞,
      lo ≠ 0 ∧ lo ≠ ⊤ ∧ hi ≠ ⊤ ∧
      ∀ᵐ t ∂(volume.restrict (directionalOrderedSet n)),
        let G := retainedOrderedModel (β ∘ σ) h
          (retainedIncreasingBasis (A.submatrix id σ))
          (fun q : κ => retainedIncreasingBasis ((retainedScoreDelete A q).submatrix id σ)) t
        lo * G ≤ F (t ∘ σ.symm) ∧ F (t ∘ σ.symm) ≤ hi * G) :
    (∫⁻ t, F t ∂directionalSchwingerMeasure (Fin n)) < ⊤ ↔
      ∀ S : Finset (Fin n), S.Nonempty →
        retainedFaceAdmissible β h (retainedWidthDefect A) (retainedWidthMissingScore A) S := by
  refine retainedWidths_finite_iff_faces β hh (retainedWidthDefect A)
    (retainedWidthMissingScore A)
    (fun σ => retainedIncreasingBasis (A.submatrix id σ))
    (fun σ q => retainedIncreasingBasis ((retainedScoreDelete A q).submatrix id σ))
    F (retainedPrefix_defect A hA) ?_ ?_ bounds
  · intro σ q j
    dsimp only
    rw [retainedPrefix_score_loss A hA σ q j]
    split <;> simp
  · intro σ j
    let C := retainedColumns A ((Finset.univ.filter (fun i : Fin n => i ≤ j)).map σ.toEmbedding)ᶜ
    change C.rank - (C.submatrix Sum.inl id).rank < Fintype.card κ ↔ _
    rw [← retainedScoreDelete_preserves_rank_iff C]
    apply exists_congr
    intro q
    rw [retainedPrefix_score_loss A hA σ q j]
    change (retainedScoreDelete C q).rank = C.rank ↔
      (if (retainedScoreDelete C q).rank = C.rank then (1 : ℝ) else 0) = 1
    split <;> simp_all

/-- Determinant and cofactor expression for the weighted Gaussian mass,
including the width density. The normalization independent of widths is
immaterial to this integral's finiteness. -/
def retainedCofactorWidthDensity {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {n : ℕ} (A : Matrix (ι ⊕ κ) (Fin n) ℝ)
    (β : Fin n → ℝ) (h : ℝ) (t : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (retainedWidthDensity β t / (retainedGramDet A t) ^ 2 *
    (1 + ∑ q : κ, retainedGramDet (retainedScoreDelete A q) t / retainedGramDet A t) ^ h)

private theorem retainedWidthDensity_reindex {n : ℕ} (β t : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) :
    retainedWidthDensity (β ∘ σ) t = retainedWidthDensity β (t ∘ σ.symm) := by
  unfold retainedWidthDensity
  exact Fintype.prod_equiv σ _ _ (by intro i; simp)

private theorem retainedCofactorWidthDensity_sector_bounds {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {n : ℕ} (A : Matrix (ι ⊕ κ) (Fin n) ℝ)
    (hA : A.rank = Fintype.card (ι ⊕ κ)) (β : Fin n → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (σ : Equiv.Perm (Fin n)) :
    ∃ lo hi : ℝ≥0∞, lo ≠ 0 ∧ lo ≠ ⊤ ∧ hi ≠ ⊤ ∧
      ∀ᵐ t ∂(volume.restrict (directionalOrderedSet n)),
        let G := retainedOrderedModel (β ∘ σ) h
          (retainedIncreasingBasis (A.submatrix id σ))
          (fun q : κ => retainedIncreasingBasis ((retainedScoreDelete A q).submatrix id σ)) t
        lo * G ≤ retainedCofactorWidthDensity A β h (t ∘ σ.symm) ∧
          retainedCofactorWidthDensity A β h (t ∘ σ.symm) ≤ hi * G := by
  classical
  let B := retainedIncreasingBasis (A.submatrix id σ)
  let D (q : κ) := retainedIncreasingBasis ((retainedScoreDelete A q).submatrix id σ)
  let X (t : Fin n → ℝ) (q : Option κ) := q.elim (retainedGramDet A (t ∘ σ.symm))
    (fun j => retainedGramDet (retainedScoreDelete A j) (t ∘ σ.symm))
  let Y (t : Fin n → ℝ) (q : Option κ) := ∏ i ∈ q.elim B D, t i
  have hb (q : Option κ) : ∃ l u : ℝ, 0 < l ∧ 0 < u ∧ ∀ t : Fin n → ℝ,
      Monotone t → (∀ i, 0 ≤ t i) → l * Y t q ≤ X t q ∧ X t q ≤ u * Y t q := by
    cases q with
    | none =>
        have hAr := (Matrix.rank_submatrix A (Equiv.refl _) σ).trans hA
        obtain ⟨l, u, hl, hu, hb⟩ := retainedGramDet_increasing_comparison _ hAr
        refine ⟨l, u, hl, hu, fun t hm ht => ?_⟩
        dsimp only [X, Y, Option.elim_none]
        rw [← retainedGramDet_reindex A σ]
        exact hb t hm ht
    | some q =>
        have hAr := (Matrix.rank_submatrix (retainedScoreDelete A q) (Equiv.refl _) σ).trans
          (retainedScoreDelete_full_rank A q hA)
        obtain ⟨l, u, hl, hu, hb⟩ := retainedGramDet_increasing_comparison _ hAr
        refine ⟨l, u, hl, hu, fun t hm ht => ?_⟩
        change l * (∏ i ∈ D q, t i) ≤ _ ∧ _
        dsimp only [X, Option.elim_some]
        rw [← retainedGramDet_reindex (retainedScoreDelete A q) σ]
        exact hb t hm ht
  choose l u hl hu H using hb
  obtain ⟨qlo, _, hmin⟩ := Finset.exists_min_image Finset.univ l Finset.univ_nonempty
  obtain ⟨qhi, _, hmax⟩ := Finset.exists_max_image Finset.univ u Finset.univ_nonempty
  let lo := l qlo
  let hi := u qhi
  let c : ℝ := Fintype.card (Option κ)
  let left := (hi ^ 2)⁻¹ * (lo / hi) ^ h / c
  let right := (lo ^ 2)⁻¹ * (hi / lo) ^ h * c ^ h
  have hlo : 0 < lo := hl qlo
  have hhi : 0 < hi := hu qhi
  have hc : 0 < c := by
    unfold c
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨none⟩
  have hleft : 0 < left := by dsimp only [left]; positivity
  have hright : 0 ≤ right := by dsimp only [right]; positivity
  refine ⟨ENNReal.ofReal left, ENNReal.ofReal right,
    ENNReal.ofReal_ne_zero_iff.mpr hleft, ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top, ?_⟩
  filter_upwards [ae_restrict_mem (directionalOrderedSet_open n).measurableSet] with t ht
  have hmt := (directionalOrderedSet_mem_iff t).mp ht
  have htpos (i : Fin n) : 0 < t i := (hmt.2 i).1
  have hy (q : Option κ) : 0 < Y t q := Finset.prod_pos fun i _ => htpos i
  have hbound (q : Option κ) : lo * Y t q ≤ X t q ∧ X t q ≤ hi * Y t q := by
    have hq := H q t hmt.1.monotone (fun i => (htpos i).le)
    exact ⟨(mul_le_mul_of_nonneg_right (hmin q (Finset.mem_univ q)) (hy q).le).trans hq.1,
      hq.2.trans (mul_le_mul_of_nonneg_right (hmax q (Finset.mem_univ q)) (hy q).le)⟩
  let w := retainedWidthDensity (β ∘ σ) t
  have hw : 0 ≤ w := Finset.prod_nonneg fun i _ => Real.rpow_nonneg (htpos i).le _
  have hX : X t none ≠ 0 := ((mul_pos hlo (hy none)).trans_le (hbound none).1).ne'
  have hF : retainedCofactorWidthDensity A β h (t ∘ σ.symm) =
      ENNReal.ofReal (w / X t none ^ 2 * (∑ q, X t q / X t none) ^ h) := by
    unfold retainedCofactorWidthDensity
    rw [← retainedWidthDensity_reindex β t σ, Fintype.sum_option]
    dsimp only [X, Option.elim_none, Option.elim_some]
    exact congrArg ENNReal.ofReal (by rw [div_self (show retainedGramDet A (t ∘ σ.symm) ≠ 0 from hX)])
  have hG : retainedOrderedModel (β ∘ σ) h B D t =
      ENNReal.ofReal (∑ q, w / Y t none ^ 2 * (Y t q / Y t none) ^ h) := by
    unfold retainedOrderedModel
    rw [ENNReal.ofReal_sum_of_nonneg (fun q _ => mul_nonneg (div_nonneg hw (sq_nonneg _))
      (Real.rpow_nonneg (div_nonneg (hy q).le (hy none).le) _))]
    apply Finset.sum_congr rfl
    intro q _
    exact retainedOrderedDensity_eq_basisRatio (β ∘ σ) h B (q.elim B D) t htpos
  change ENNReal.ofReal left * retainedOrderedModel (β ∘ σ) h B D t ≤
      retainedCofactorWidthDensity A β h (t ∘ σ.symm) ∧
    retainedCofactorWidthDensity A β h (t ∘ σ.symm) ≤
      ENNReal.ofReal right * retainedOrderedModel (β ∘ σ) h B D t
  rw [hF, hG, ← ENNReal.ofReal_mul hleft.le, ← ENNReal.ofReal_mul hright]
  have hm := retainedMoment_comparison (X t) (Y t) hlo hhi hh hw hy hbound
  exact ⟨ENNReal.ofReal_le_ofReal hm.1, ENNReal.ofReal_le_ofReal hm.2⟩

/-- The actual retained determinant and its score-row cofactors obey the
strict width-face criterion. Equality in any inequality diverges. -/
theorem retainedCofactorWidthDensity_finite_iff_faces {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {n : ℕ} (A : Matrix (ι ⊕ κ) (Fin n) ℝ)
    (hA : A.rank = Fintype.card (ι ⊕ κ)) (β : Fin n → ℝ) {h : ℝ} (hh : 0 ≤ h) :
    (∫⁻ t, retainedCofactorWidthDensity A β h t ∂directionalSchwingerMeasure (Fin n)) < ⊤ ↔
      ∀ S : Finset (Fin n), S.Nonempty →
        retainedFaceAdmissible β h (retainedWidthDefect A) (retainedWidthMissingScore A) S :=
  retainedRoutedWidths_finite_iff_faces A hA β hh (retainedCofactorWidthDensity A β h)
    (retainedCofactorWidthDensity_sector_bounds A hA β hh)

end UV
