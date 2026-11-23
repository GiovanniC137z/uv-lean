import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A finite Cauchy–Binet expansion of the retained covariance determinant,
with repeated column selections removed by alternation. -/

noncomputable section

open Function Finset
open scoped BigOperators Matrix

namespace UV

/-- Expand a rectangular product determinant by its intermediate column
assignments. This form also works with unequal inner and outer sizes. -/
theorem retainedDet_mul_eq_sum_assignments {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] (A : Matrix ι κ ℝ) (B : Matrix κ ι ℝ) :
    (A * B).det = ∑ p : ι → κ, (A.submatrix id p).det * ∏ i, B (p i) i := by
  classical
  calc
    _ = ∑ p : ι → κ, ∑ σ : Equiv.Perm ι,
        (Equiv.Perm.sign σ : ℝ) * ∏ i, A (σ i) (p i) * B (p i) i := by
      simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum,
        Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq, Finset.sum_mul,
        Finset.prod_mul_distrib, mul_assoc]

private theorem retainedDet_assignment_eq_zero {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι κ ℝ) (p : ι → κ) (hp : ¬ Injective p) :
    (A.submatrix id p).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, p i = p j ∧ i ≠ j := by
    by_contra h
    exact hp (fun i j hij => by_contra fun hne => h ⟨i, j, hij, hne⟩)
  exact Matrix.det_zero_of_column_eq hne (fun k => congrArg (A k) hij)

/-- Ordered relabeling of the inner summation gives an actual square
minor and its transpose. -/
theorem retainedDet_weighted_minor {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι κ ℝ) (t : κ → ℝ) (p : ι → κ) :
    ((A.submatrix id p) * Matrix.diagonal (t ∘ p) * (A.submatrix id p)ᵀ).det =
      (A.submatrix id p).det ^ 2 * ∏ i, t (p i) := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  simp only [Function.comp_apply]
  ring

/-- A determinant square depends only on the selected columns, so any
enumeration of the given cardinality supplies the coefficient. -/
def retainedMinorCoefficient {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι κ ℝ) (S : Finset κ) : ℝ := by
  classical
  exact if hS : S.card = Fintype.card ι then
    let e : ι ≃ S := Fintype.equivOfCardEq (by simp [hS])
    (A.submatrix id (Subtype.val ∘ e)).det ^ 2
  else 0

theorem retainedMinorCoefficient_nonneg {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι κ ℝ) (S : Finset κ) :
    0 ≤ retainedMinorCoefficient A S := by
  classical
  unfold retainedMinorCoefficient
  split
  · exact sq_nonneg _
  · rfl

/-- The retained covariance determinant `B_A(t)`. -/
def retainedGramDet {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix ι κ ℝ) (t : κ → ℝ) : ℝ :=
  (A * Matrix.diagonal t * Aᵀ).det

private theorem retainedDet_weighted_expansion {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ ℝ) (t : κ → ℝ) :
    retainedGramDet A t =
      ∑ p : ι → κ, (A.submatrix id p).det * ∏ i, t (p i) * A i (p i) := by
  rw [retainedGramDet, Matrix.mul_assoc, retainedDet_mul_eq_sum_assignments]
  simp only [Matrix.diagonal_mul, Matrix.transpose_apply]

private theorem retainedDet_fiber_eq {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix ι κ ℝ) (t : κ → ℝ)
    (S : Finset κ) (hS : S.card = Fintype.card ι) :
    (∑ p ∈ (Finset.univ.filter (Injective : (ι → κ) → Prop)).filter
      (fun p => Finset.univ.image p = S),
      (A.submatrix id p).det * ∏ i, t (p i) * A i (p i)) =
        retainedMinorCoefficient A S * ∏ i ∈ S, t i := by
  classical
  let e : ι ≃ S := Fintype.equivOfCardEq (by simp [hS])
  let B : Matrix ι ι ℝ := A.submatrix id (Subtype.val ∘ e)
  let v : ι → ℝ := t ∘ Subtype.val ∘ e
  let F (p : ι → κ) := (A.submatrix id p).det * ∏ i, t (p i) * A i (p i)
  let P (q : ι → ι) := (Subtype.val ∘ e) ∘ q
  have hinj : Injective (Subtype.val ∘ e : ι → κ) :=
    Subtype.val_injective.comp e.injective
  have hsum :
      (∑ p ∈ (Finset.univ.filter (Injective : (ι → κ) → Prop)).filter
          (fun p => Finset.univ.image p = S), F p) =
        ∑ q ∈ (Finset.univ.filter (Injective : (ι → ι) → Prop)), F (P q) := by
    symm
    apply Finset.sum_bij (fun q _ => P q)
    · intro q hq
      have hq' := (Finset.mem_filter.mp hq).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hinj.comp hq', ?_⟩
      ext k
      constructor
      · rintro hk
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hk
        exact (e (q i)).2
      · intro hk
        obtain ⟨i, hi⟩ := (Finite.injective_iff_surjective.mp hq') (e.symm ⟨k, hk⟩)
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by simp [P, hi]⟩
    · intro q _ q' _ heq
      funext i
      exact hinj (congrFun heq i)
    · intro p hp
      have hp' := (Finset.mem_filter.mp hp).1
      have himage := (Finset.mem_filter.mp hp).2
      have hmem (i : ι) : p i ∈ S := by
        rw [← himage]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      let q (i : ι) := e.symm ⟨p i, hmem i⟩
      have hq : P q = p := by
        funext i
        simp [P, q]
      refine ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hq⟩
      intro i j hij
      apply (Finset.mem_filter.mp hp').2
      rw [← hq]
      exact congrArg (Subtype.val ∘ e) hij
    · intros
      rfl
  have hdrop :
      (∑ q ∈ Finset.univ.filter (Injective : (ι → ι) → Prop), F (P q)) =
        ∑ q : ι → ι, F (P q) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro q _ hq
    have hni : ¬ Injective q := by simpa using hq
    have hnP : ¬ Injective (P q) := fun h =>
      hni (fun _ _ hh => h (congrArg (Subtype.val ∘ e) hh))
    simp [F, retainedDet_assignment_eq_zero A (P q) hnP]
  have hreindex : (∏ i : ι, v i) = ∏ k ∈ S, t k := by
    apply Finset.prod_bij (fun i _ => (e i).1)
    · exact fun i _ => (e i).2
    · exact fun _ _ _ _ hij => hinj hij
    · intro k hk
      exact ⟨e.symm ⟨k, hk⟩, Finset.mem_univ _, by simp⟩
    · intros
      rfl
  change (∑ p ∈ _, F p) = _
  rw [hsum, hdrop]
  have hweighted := retainedDet_weighted_expansion B v
  change retainedGramDet B v = ∑ q : ι → ι, F (P q) at hweighted
  rw [← hweighted]
  change (B * Matrix.diagonal (t ∘ (Subtype.val ∘ e)) * Bᵀ).det = _
  rw [retainedDet_weighted_minor]
  simp only [retainedMinorCoefficient, dif_pos hS]
  change B.det ^ 2 * (∏ i, v i) = B.det ^ 2 * _
  rw [hreindex]

/-- Cauchy–Binet for the actual retained Gram determinant with diagonal
Schwinger widths, indexed by sets of distinct columns. -/
theorem retainedGramDet_eq_basis_sum {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix ι κ ℝ) (t : κ → ℝ) :
    retainedGramDet A t = ∑ S ∈ Finset.univ.powersetCard (Fintype.card ι),
      retainedMinorCoefficient A S * ∏ i ∈ S, t i := by
  classical
  rw [retainedDet_weighted_expansion]
  let F (p : ι → κ) := (A.submatrix id p).det * ∏ i, t (p i) * A i (p i)
  let T := Finset.univ.filter (Injective : (ι → κ) → Prop)
  have hdrop : (∑ p ∈ T, F p) = ∑ p : ι → κ, F p := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p _ hp
    have hp' : ¬ Injective p := by simpa [T] using hp
    simp [F, retainedDet_assignment_eq_zero A p hp']
  change (∑ p, F p) = _
  rw [← hdrop, ← Finset.sum_fiberwise_of_maps_to
    (g := fun p : ι → κ => Finset.univ.image p)
    (t := Finset.univ.powersetCard (Fintype.card ι)) (fun p hp => ?_) F]
  · apply Finset.sum_congr rfl
    intro S hS
    exact retainedDet_fiber_eq A t S (Finset.mem_powersetCard.mp hS).2
  · have hp' := (Finset.mem_filter.mp hp).2
    simp [Finset.mem_powersetCard, Finset.card_image_of_injective _ hp']

end UV
