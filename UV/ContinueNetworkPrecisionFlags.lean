import UV.ContinueNetworkPrecisionGreedy
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The greedy coordinates realize the actual flag of null subspaces.
A weak direction is precisely a coordinate from a later selected row. -/

noncomputable section

open Module
open scoped BigOperators

namespace UV.ContinueNetworkPrecision

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {N : ℕ}

/-- The vectors unseen by every processed row of the fixed sector. -/
def nullPrefix (rows : Fin N → V →ₗ[ℝ] ℝ) (n : ℕ) : Submodule ℝ V where
  carrier := {k | ∀ i : Fin N, i.val < n → rows i k = 0}
  zero_mem' := by intro i _; exact map_zero _
  add_mem' := by
    intro x y hx hy i hi
    rw [map_add, hx i hi, hy i hi, add_zero]
  smul_mem' := by
    intro r k hk i hi
    rw [map_smul, hk i hi, smul_zero]

/-- No row outside the selected prefix is needed to impose its exact
annihilator. -/
theorem nullPrefix_iff_selected (rows : Fin N → V →ₗ[ℝ] ℝ) (n : ℕ) (k : V) :
    k ∈ nullPrefix rows n ↔ ∀ i ∈ greedyRows rows n, rows i k = 0 := by
  constructor
  · intro hk i hi
    exact hk i (greedyRows_mem_lt rows n hi)
  · intro hk i hi
    let ev := Module.Dual.eval ℝ V k
    have hker : rowSpan rows (greedyRows rows n) ≤ LinearMap.ker ev := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,hj,rfl⟩
      exact hk j hj
    apply hker
    rw [greedyRows_prefix_span_eq]
    apply Submodule.subset_span
    exact ⟨i,hi,rfl⟩

abbrev GreedyIndex (rows : Fin N → V →ₗ[ℝ] ℝ) := ↥(greedyRows rows N)

abbrev WeakIndex (rows : Fin N → V →ₗ[ℝ] ℝ) (n : ℕ) :=
  {i : GreedyIndex rows // n ≤ i.val.val}

private theorem selectedRange_eq_image (rows : Fin N → V →ₗ[ℝ] ℝ) :
    Set.range (fun i : GreedyIndex rows => rows i.val) = rows '' (greedyRows rows N : Set (Fin N)) := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨i.1,i.2,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨⟨i,hi⟩,rfl⟩

private theorem greedy_final_span (rows : Fin N → V →ₗ[ℝ] ℝ) :
    rowSpan rows (greedyRows rows N) = Submodule.span ℝ (Set.range rows) := by
  rw [greedyRows_prefix_span_eq, show {i : Fin N | i.val < N} = Set.univ by ext i; simp,
    Set.image_univ]

/-- An injective complete row family spans the dual of the momentum
space. The input is exactly the combined row-map injectivity. -/
theorem rowSpan_top_of_injective (rows : Fin N → V →ₗ[ℝ] ℝ)
    (hinj : Function.Injective (fun k : V => fun i => rows i k)) :
    Submodule.span ℝ (Set.range rows) = ⊤ := by
  apply top_unique
  intro f _
  apply mem_span_of_iInf_ker_le_ker
  intro k hk
  have h0 : k = 0 := hinj (by
    funext i
    have hh := ((Submodule.mem_iInf _).mp hk i : k ∈ LinearMap.ker (rows i))
    change rows i k = rows i 0
    rw [map_zero]
    exact hh)
  rw [h0]
  exact (LinearMap.ker f).zero_mem

/-- The selected rows themselves form the dual basis. -/
def greedyDualBasis (rows : Fin N → V →ₗ[ℝ] ℝ)
    (hspan : Submodule.span ℝ (Set.range rows) = ⊤) : Basis (GreedyIndex rows) ℝ (Module.Dual ℝ V) :=
  Basis.mk (greedyRows_indep rows N) (by
    change ⊤ ≤ Submodule.span ℝ (Set.range fun i : GreedyIndex rows => rows i.val)
    rw [selectedRange_eq_image, ← rowSpan, greedy_final_span, hspan])

@[simp] theorem greedyDualBasis_apply (rows : Fin N → V →ₗ[ℝ] ℝ)
    (hspan : Submodule.span ℝ (Set.range rows) = ⊤) (i : GreedyIndex rows) :
    greedyDualBasis rows hspan i = rows i.1 := Basis.mk_apply _ _ _

variable [FiniteDimensional ℝ V]

/-- The complete momentum coordinates are exact evaluations of the
selected rows, with no rescaling or weight dependence. -/
def greedyCoordinates (rows : Fin N → V →ₗ[ℝ] ℝ)
    (hspan : Submodule.span ℝ (Set.range rows) = ⊤) : V ≃ₗ[ℝ] (GreedyIndex rows → ℝ) :=
  (Module.evalEquiv ℝ V).trans (greedyDualBasis rows hspan).dualBasis.equivFun

@[simp] theorem greedyCoordinates_apply (rows : Fin N → V →ₗ[ℝ] ℝ)
    (hspan : Submodule.span ℝ (Set.range rows) = ⊤) (k : V) (i : GreedyIndex rows) :
    greedyCoordinates rows hspan k i = rows i.1 k := by
  simp only [greedyCoordinates, LinearEquiv.trans_apply, Basis.dualBasis_equivFun,
    Module.evalEquiv_apply, Module.Dual.eval_apply, greedyDualBasis_apply]

/-- In those actual coordinates a strong prefix imposes exactly the zero
conditions on the selected strong coordinates. -/
theorem nullPrefix_iff_coordinate_zero (rows : Fin N → V →ₗ[ℝ] ℝ)
    (hspan : Submodule.span ℝ (Set.range rows) = ⊤) {n : ℕ} (hn : n ≤ N) (k : V) :
    k ∈ nullPrefix rows n ↔ ∀ i : GreedyIndex rows, i.val.val < n →
      greedyCoordinates rows hspan k i = 0 := by
  constructor
  · intro hk i hi
    rw [greedyCoordinates_apply]
    exact hk i.1 hi
  · intro h
    apply (nullPrefix_iff_selected rows n k).mpr
    intro i hi
    let j : GreedyIndex rows := ⟨i,greedyRows_monotone rows hn hi⟩
    simpa only [greedyCoordinates_apply] using h j (greedyRows_mem_lt rows n hi)

private def extendWeak (rows : Fin N → V →ₗ[ℝ] ℝ) (n : ℕ) (z : WeakIndex rows n → ℝ)
    (i : GreedyIndex rows) : ℝ := if h : n ≤ i.val.val then z ⟨i,h⟩ else 0

/-- Restrict to the weak coordinates. The inverse extends by zero in
all the strong coordinates and uses the same selected-row basis. -/
def weakCoordinateEquiv (rows : Fin N → V →ₗ[ℝ] ℝ)
    (hspan : Submodule.span ℝ (Set.range rows) = ⊤) {n : ℕ} (hn : n ≤ N) :
    nullPrefix rows n ≃ₗ[ℝ] (WeakIndex rows n → ℝ) where
  toFun k i := greedyCoordinates rows hspan k.1 i.1
  invFun z := ⟨(greedyCoordinates rows hspan).symm (extendWeak rows n z), by
    apply (nullPrefix_iff_coordinate_zero rows hspan hn _).2
    intro i hi
    rw [LinearEquiv.apply_symm_apply, extendWeak, dif_neg (Nat.not_le.mpr hi)]⟩
  left_inv k := by
    apply Subtype.ext
    apply (greedyCoordinates rows hspan).injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    unfold extendWeak
    split
    · rfl
    · rename_i hi
      exact ((nullPrefix_iff_coordinate_zero rows hspan hn _).1 k.2 i (Nat.lt_of_not_le hi)).symm
  right_inv z := by
    funext i
    simp only [LinearEquiv.apply_symm_apply, extendWeak, dif_pos i.2]
  map_add' k x := by
    funext i
    change greedyCoordinates rows hspan (k.1+x.1) i.1 = _
    rw [map_add]
    rfl
  map_smul' a k := by
    funext i
    change greedyCoordinates rows hspan (a • k.1) i.1 = _
    rw [map_smul]
    rfl

/-- The number of weak selected coordinates is exactly the dimension of
this null subspace. -/
theorem nullPrefix_finrank (rows : Fin N → V →ₗ[ℝ] ℝ)
    (hspan : Submodule.span ℝ (Set.range rows) = ⊤) {n : ℕ} (hn : n ≤ N) :
    Module.finrank ℝ (nullPrefix rows n) = Fintype.card (WeakIndex rows n) := by
  rw [(weakCoordinateEquiv rows hspan hn).finrank_eq, Module.finrank_pi]

theorem greedyRows_card_finrank (rows : Fin N → V →ₗ[ℝ] ℝ)
    (hspan : Submodule.span ℝ (Set.range rows) = ⊤) :
    (greedyRows rows N).card = Module.finrank ℝ V := by
  rw [(greedyCoordinates rows hspan).finrank_eq, Module.finrank_pi, Fintype.card_coe]

/-- The diagonal precision in the actual coordinate space is precisely
the selected finite row sum with unmodified inherited weights. -/
theorem selectedPrecision_eq_coordinates (rows : Fin N → V →ₗ[ℝ] ℝ)
    (hspan : Submodule.span ℝ (Set.range rows) = ⊤) (w : Fin N → ℝ) (k : V) :
    selectedPrecision rows (greedyRows rows N) w k =
      ∑ i : GreedyIndex rows, w i.1 * (greedyCoordinates rows hspan k i)^2 := by
  simp only [greedyCoordinates_apply, selectedPrecision]
  exact (Finset.sum_coe_sort (greedyRows rows N) (fun i => w i * (rows i k)^2)).symm

end UV.ContinueNetworkPrecision
