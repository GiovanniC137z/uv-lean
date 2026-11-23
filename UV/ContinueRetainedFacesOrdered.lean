import UV.ContinueNetworkOrderedSectors
import UV.ContinueNetworkPrefixSubsets

/-! Ordered-sector endpoint tests for the retained-score determinant and its
score-row cofactors. Every nonempty face is tested in at least one sector. -/

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace UV

/-- A selected width occurs with unit exponent in a basis monomial. -/
def retainedBasisExponent {n : ℕ} (B : Finset (Fin n)) (i : Fin n) : ℝ :=
  if i ∈ B then 1 else 0

/-- The density exponent after division by the square of the retained
basis monomial and multiplication by the selected cofactor ratio to power
`h`. Taking `D = B` gives the unweighted term. -/
def retainedOrderedExponent {n : ℕ} (β : Fin n → ℝ) (h : ℝ)
    (B D : Finset (Fin n)) (i : Fin n) : ℝ :=
  β i - 2 * retainedBasisExponent B i -
    h * (retainedBasisExponent B i - retainedBasisExponent D i)

/-- The baseline term and all individually weighted cofactor terms. -/
def retainedOrderedModel {n : ℕ} {ι : Type*} [Fintype ι]
    (β : Fin n → ℝ) (h : ℝ) (B : Finset (Fin n)) (D : ι → Finset (Fin n))
    (t : Fin n → ℝ) : ℝ≥0∞ :=
  ∑ q : Option ι, directionalOrderedDensity
    (retainedOrderedExponent β h B (q.elim B D)) t

theorem retainedOrderedModel_measurable {n : ℕ} {ι : Type*} [Fintype ι]
    (β : Fin n → ℝ) (h : ℝ) (B : Finset (Fin n)) (D : ι → Finset (Fin n)) :
    Measurable (retainedOrderedModel β h B D) := by
  apply Finset.measurable_sum
  intro q _
  exact directionalOrderedDensity_measurable _

private theorem retainedBasisExponent_sum {n : ℕ} (S B : Finset (Fin n)) :
    (∑ i ∈ S, retainedBasisExponent B i) = ((S.filter (· ∈ B)).card : ℝ) := by
  classical
  simp [retainedBasisExponent, Finset.filter_mem_eq_inter]


/-- At a prefix, determinant losses count the selected columns in that
prefix, including the possibly different count for a deleted row. -/
theorem retainedOrderedExponent_prefix {n : ℕ} (β : Fin n → ℝ) (h : ℝ)
    (B D : Finset (Fin n)) (j : Fin n) :
    let S := Finset.univ.filter (fun i : Fin n => i ≤ j)
    directionalOrderedPrefix (retainedOrderedExponent β h B D) j =
      (∑ i ∈ S, β i) - 2 * ((S.filter (· ∈ B)).card : ℝ) -
        h * (((S.filter (· ∈ B)).card : ℝ) - ((S.filter (· ∈ D)).card : ℝ)) := by
  classical
  dsimp only
  rw [directionalOrderedPrefix, ← Finset.sum_filter]
  simp_rw [retainedOrderedExponent, Finset.sum_sub_distrib, ← Finset.mul_sum,
    retainedBasisExponent_sum]
  rw [Finset.sum_sub_distrib, retainedBasisExponent_sum, retainedBasisExponent_sum]

theorem retainedOrderedModel_finite_iff {n : ℕ} {ι : Type*} [Fintype ι]
    (β : Fin n → ℝ) (h : ℝ) (B : Finset (Fin n)) (D : ι → Finset (Fin n)) :
    (∫⁻ t in directionalOrderedSet n, retainedOrderedModel β h B D t) < ⊤ ↔
      ∀ (q : Option ι) (j : Fin n),
        0 < directionalOrderedPrefix (retainedOrderedExponent β h B (q.elim B D)) j := by
  classical
  unfold retainedOrderedModel
  rw [lintegral_finset_sum _ fun q _ => directionalOrderedDensity_measurable _]
  simp only [ENNReal.sum_lt_top, Finset.mem_univ, forall_true_left]
  exact forall_congr' fun _ => directionalOrderedCost_finite_iff _

/-- A finite positive comparison factor preserves the divergence at a
critical prefix. The two constants can differ between sectors. -/
theorem retainedOrderedModel_comparable_finite_iff {n : ℕ} {ι : Type*} [Fintype ι]
    (β : Fin n → ℝ) (h : ℝ) (B : Finset (Fin n)) (D : ι → Finset (Fin n))
    (F : (Fin n → ℝ) → ℝ≥0∞) (lo hi : ℝ≥0∞) (hlo : lo ≠ 0)
    (hlo' : lo ≠ ⊤) (hhi : hi ≠ ⊤)
    (bounds : ∀ᵐ t ∂(volume.restrict (directionalOrderedSet n)),
      lo * retainedOrderedModel β h B D t ≤ F t ∧
      F t ≤ hi * retainedOrderedModel β h B D t) :
    (∫⁻ t in directionalOrderedSet n, F t) < ⊤ ↔
      (∫⁻ t in directionalOrderedSet n, retainedOrderedModel β h B D t) < ⊤ := by
  constructor
  · intro hf
    have hf' := (lintegral_mono_ae (bounds.mono fun _ ht => ht.1)).trans_lt hf
    rw [lintegral_const_mul' _ _ hlo'] at hf'
    by_contra hmodel
    rw [not_lt, top_le_iff] at hmodel
    rw [hmodel, ENNReal.mul_top hlo] at hf'
    exact (lt_irrefl _ hf')
  · intro hf
    apply (lintegral_mono_ae (bounds.mono fun _ ht => ht.2)).trans_lt
    rw [lintegral_const_mul' _ _ hhi]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hhi) hf

/-- A one-sided upper comparison suffices for convergence. -/
theorem retainedOrderedModel_finite_of_upper {n : ℕ} {ι : Type*} [Fintype ι]
    (β : Fin n → ℝ) (h : ℝ) (B : Finset (Fin n)) (D : ι → Finset (Fin n))
    (F : (Fin n → ℝ) → ℝ≥0∞) (hi : ℝ≥0∞) (hhi : hi ≠ ⊤)
    (upper : ∀ᵐ t ∂(volume.restrict (directionalOrderedSet n)),
      F t ≤ hi * retainedOrderedModel β h B D t)
    (finite : (∫⁻ t in directionalOrderedSet n, retainedOrderedModel β h B D t) < ⊤) :
    (∫⁻ t in directionalOrderedSet n, F t) < ⊤ := by
  apply (lintegral_mono_ae upper).trans_lt
  rw [lintegral_const_mul' _ _ hhi]
  exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hhi) finite

/-- Width faces in the original edge labels. `d` is the full retained
rank defect and `missing` marks a positive score-rank defect. -/
def retainedFaceAdmissible {n : ℕ} (β : Fin n → ℝ) (h : ℝ)
    (d : Finset (Fin n) → ℕ) (missing : Finset (Fin n) → Prop)
    [DecidablePred missing] (S : Finset (Fin n)) : Prop :=
  2 * (d S : ℝ) + h * (if missing S then 1 else 0) < ∑ i ∈ S, β i

/-- Prefix counts for each selected basis give the exact integrability
criterion, including the unweighted term and a cofactor realizing one
extra power exactly when the score rank drops. -/
theorem retainedOrderedModel_finite_iff_rank_faces {n : ℕ} {ι : Type*} [Fintype ι]
    (β : Fin n → ℝ) {h : ℝ} (hh : 0 ≤ h) (B : Finset (Fin n)) (D : ι → Finset (Fin n))
    (d : Fin n → ℕ) (missing : Fin n → Prop) [DecidablePred missing]
    (base : ∀ j, d j = ((Finset.univ.filter (fun i : Fin n => i ≤ j)).filter (· ∈ B)).card)
    (loss : ∀ (q : ι) (j : Fin n),
      let S := Finset.univ.filter (fun i : Fin n => i ≤ j)
      ((S.filter (· ∈ B)).card : ℝ) - ((S.filter (· ∈ D q)).card : ℝ) ∈ ({0, 1} : Set ℝ))
    (realizes : ∀ j, missing j ↔ ∃ q : ι,
      let S := Finset.univ.filter (fun i : Fin n => i ≤ j)
      ((S.filter (· ∈ B)).card : ℝ) - ((S.filter (· ∈ D q)).card : ℝ) = 1) :
    (∫⁻ t in directionalOrderedSet n, retainedOrderedModel β h B D t) < ⊤ ↔
      ∀ j, 2 * (d j : ℝ) + h * (if missing j then 1 else 0) <
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => i ≤ j), β i := by
  classical
  rw [retainedOrderedModel_finite_iff]
  constructor
  · intro H j
    by_cases hm : missing j
    · obtain ⟨q, hq⟩ := (realizes j).mp hm
      have hp := H (some q) j
      rw [retainedOrderedExponent_prefix] at hp
      simp only [Option.elim_some, ← base j, if_pos hm] at hp ⊢
      dsimp only at hq
      rw [← base j] at hq
      rw [hq] at hp
      linarith
    · have hp := H none j
      rw [retainedOrderedExponent_prefix] at hp
      simp only [Option.elim_none, ← base j, sub_self, mul_zero, sub_zero, if_neg hm,
        add_zero] at hp ⊢
      linarith
  · intro H q j
    have hj := H j
    rw [retainedOrderedExponent_prefix]
    cases q with
    | none =>
        simp only [Option.elim_none, ← base j, sub_self, mul_zero, sub_zero]
        by_cases hm : missing j <;> simp [hm] at hj <;> linarith
    | some q =>
        simp only [Option.elim_some, ← base j]
        have hl := loss q j
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, ← base j] at hl
        rcases hl with h0 | h1
        · rw [h0]
          by_cases hm : missing j <;> simp [hm] at hj <;> linarith
        · have h1' := h1
          rw [base j] at h1'
          have hm := (realizes j).mpr ⟨q, h1'⟩
          rw [h1]
          simp [hm] at hj
          linarith

/-- The original width faces are exactly the nonempty prefixes of all
coordinate orderings. This turns sector inequalities into tests for
arbitrary simultaneous limits. -/
theorem retainedFaceAdmissible_iff_prefixes {n : ℕ} (β : Fin n → ℝ) (h : ℝ)
    (d : Finset (Fin n) → ℕ) (missing : Finset (Fin n) → Prop)
    [DecidablePred missing] :
    (∀ S : Finset (Fin n), S.Nonempty → retainedFaceAdmissible β h d missing S) ↔
      ∀ (σ : Equiv.Perm (Fin n)) (j : Fin n),
        retainedFaceAdmissible β h d missing
          ((Finset.univ.filter (fun i : Fin n => i ≤ j)).map σ.toEmbedding) := by
  constructor
  · intro H σ j
    apply H
    refine ⟨σ j, Finset.mem_map.mpr ⟨j, ?_, rfl⟩⟩
    simp
  · intro H S hS
    obtain ⟨σ, j, -, hj⟩ := route_subset_is_nonempty_prefix S hS
    exact hj ▸ H σ j

/-- Ignoring null sector boundaries, comparison against the greedy
monomials transfers the exact rank inequalities to the full integral. -/
theorem retainedWidths_finite_iff_faces {n : ℕ} {ι : Type*} [Fintype ι]
    (β : Fin n → ℝ) {h : ℝ} (hh : 0 ≤ h) (d : Finset (Fin n) → ℕ)
    (missing : Finset (Fin n) → Prop) [DecidablePred missing]
    (B : Equiv.Perm (Fin n) → Finset (Fin n))
    (D : Equiv.Perm (Fin n) → ι → Finset (Fin n))
    (F : (Fin n → ℝ) → ℝ≥0∞)
    (base : ∀ (σ : Equiv.Perm (Fin n)) (j : Fin n),
      let S := Finset.univ.filter (fun i : Fin n => i ≤ j)
      d (S.map σ.toEmbedding) = (S.filter (· ∈ B σ)).card)
    (loss : ∀ (σ : Equiv.Perm (Fin n)) (q : ι) (j : Fin n),
      let S := Finset.univ.filter (fun i : Fin n => i ≤ j)
      ((S.filter (· ∈ B σ)).card : ℝ) - ((S.filter (· ∈ D σ q)).card : ℝ) ∈ ({0, 1} : Set ℝ))
    (realizes : ∀ (σ : Equiv.Perm (Fin n)) (j : Fin n),
      let S := Finset.univ.filter (fun i : Fin n => i ≤ j)
      missing (S.map σ.toEmbedding) ↔ ∃ q : ι,
      ((S.filter (· ∈ B σ)).card : ℝ) - ((S.filter (· ∈ D σ q)).card : ℝ) = 1)
    (bounds : ∀ σ : Equiv.Perm (Fin n), ∃ lo hi : ℝ≥0∞,
      lo ≠ 0 ∧ lo ≠ ⊤ ∧ hi ≠ ⊤ ∧
      ∀ᵐ t ∂(volume.restrict (directionalOrderedSet n)),
        lo * retainedOrderedModel (β ∘ σ) h (B σ) (D σ) t ≤ F (t ∘ σ.symm) ∧
        F (t ∘ σ.symm) ≤ hi * retainedOrderedModel (β ∘ σ) h (B σ) (D σ) t) :
    (∫⁻ t, F t ∂directionalSchwingerMeasure (Fin n)) < ⊤ ↔
      ∀ S : Finset (Fin n), S.Nonempty → retainedFaceAdmissible β h d missing S := by
  rw [directionalSchwinger_finite_iff_ordered_sectors, retainedFaceAdmissible_iff_prefixes]
  apply forall_congr'
  intro σ
  obtain ⟨lo, hi, hlo, hlo', hhi, hb⟩ := bounds σ
  rw [directionalPermutedSector_lintegral_eq,
    retainedOrderedModel_comparable_finite_iff _ _ _ _ _ _ _ hlo hlo' hhi hb]
  refine (retainedOrderedModel_finite_iff_rank_faces _ hh _ _
    (fun j => d ((Finset.univ.filter (fun i : Fin n => i ≤ j)).map σ.toEmbedding))
    (fun j => missing ((Finset.univ.filter (fun i : Fin n => i ≤ j)).map σ.toEmbedding))
    (base σ) (loss σ) (realizes σ)).trans ?_
  apply forall_congr'
  intro j
  simp only [retainedFaceAdmissible, Finset.sum_map, Function.comp_apply,
    Equiv.toEmbedding_apply]

end UV
