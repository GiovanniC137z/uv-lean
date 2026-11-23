import UV.ContinueNetworkPrecisionSector
import UV.ContinueNetworkPrecisionFlags

/-! Euclidean realization of the selected coordinates and the actual
Gaussian-and-unseen-route flag used by the directional criterion. -/

noncomputable section

open Module
open scoped BigOperators

namespace UV.ContinueNetworkPrecision

/-- The finite coordinate index set of the selected basis has the exact
Euclidean momentum dimension. -/
def greedyEuclideanIndex {N d : ℕ} (rows : Fin N → DirectionalMomentum d →ₗ[ℝ] ℝ)
    (hspan : Submodule.span ℝ (Set.range rows) = ⊤) : Fin d ≃ GreedyIndex rows :=
  let h : Fintype.card (GreedyIndex rows) = d := by
    rw [Fintype.card_coe, greedyRows_card_finrank rows hspan]
    exact finrank_euclideanSpace_fin
  (finCongr h.symm).trans (Fintype.equivFin _).symm

/-- The Euclidean chart uses the literal row values as its coordinate
functions, reindexed by the same finite set of selected rows. -/
def greedyEuclideanChart {N d : ℕ} (rows : Fin N → DirectionalMomentum d →ₗ[ℝ] ℝ)
    (hspan : Submodule.span ℝ (Set.range rows) = ⊤) : DirectionalMomentum d ≃L[ℝ] DirectionalMomentum d :=
  let index := greedyEuclideanIndex rows hspan
  (((greedyCoordinates rows hspan).trans (LinearEquiv.funCongrLeft ℝ ℝ index)).trans
    (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm).toContinuousLinearEquiv

@[simp] theorem greedyEuclideanChart_apply {N d : ℕ} (rows : Fin N → DirectionalMomentum d →ₗ[ℝ] ℝ)
    (hspan : Submodule.span ℝ (Set.range rows) = ⊤) (k : DirectionalMomentum d) (i : Fin d) :
    greedyEuclideanChart rows hspan k i = rows (greedyEuclideanIndex rows hspan i).val k := by
  change greedyCoordinates rows hspan k (greedyEuclideanIndex rows hspan i) = _
  exact greedyCoordinates_apply rows hspan k _

/-- The diagonal precision in the actual Euclidean chart uses exactly
its original weights. -/
theorem selectedPrecision_eq_euclideanChart {N d : ℕ} (rows : Fin N → DirectionalMomentum d →ₗ[ℝ] ℝ)
    (hspan : Submodule.span ℝ (Set.range rows) = ⊤) (w : Fin N → ℝ) (k : DirectionalMomentum d) :
    selectedPrecision rows (greedyRows rows N) w k =
      ∑ i : Fin d, w (greedyEuclideanIndex rows hspan i).val * (greedyEuclideanChart rows hspan k i)^2 := by
  rw [selectedPrecision_eq_coordinates rows hspan]
  simp only [greedyCoordinates_apply, greedyEuclideanChart_apply]
  exact (Equiv.sum_comp (greedyEuclideanIndex rows hspan) (fun i => w i.1 * (rows i.1 k)^2)).symm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {a m : ℕ} {b : Fin m → ℕ}

/-- Recover the original route index of each row. Gaussian rows carry
no route index and receive weight one. -/
def sourceRowSlot : NetworkRowLabel a m b → Option (Fin m)
  | .inl _ => none
  | .inr ei => some ei.1

theorem sourceRowTierWeight_eq_slot (t : Fin m → ℝ) (l : NetworkRowLabel a m b) :
    schwingerTierWeight t (sourceRowTier l) = (sourceRowSlot l).elim 1 t := by
  cases l <;> simp [sourceRowTier, sourceRowSlot, schwingerTierWeight]

/-- The injectivity of the complete physical block map is exactly enough
for the linear functionals defining the greedy chart to span. -/
theorem sourceRows_injective_of_combined (A : V →ₗ[ℝ] DirectionalMomentum a)
    (C : ∀ e, V →ₗ[ℝ] DirectionalMomentum (b e))
    (ord : Fin (Fintype.card (NetworkRowLabel a m b)) ≃ NetworkRowLabel a m b)
    (hinj : Function.Injective (fun k : V => (A k, fun e => C e k))) :
    Function.Injective (fun k : V => fun i => sourceRowForm A C (ord i) k) := by
  intro k p h
  apply hinj
  apply Prod.ext
  · apply PiLp.ext
    intro i
    have he := congrFun h (ord.symm (.inl i))
    change sourceRowForm A C (ord (ord.symm (.inl i))) k =
      sourceRowForm A C (ord (ord.symm (.inl i))) p at he
    simpa only [Equiv.apply_symm_apply, sourceRowForm, LinearMap.comp_apply] using he
  · funext e
    apply PiLp.ext
    intro i
    have he := congrFun h (ord.symm (.inr ⟨e,i⟩))
    change sourceRowForm A C (ord (ord.symm (.inr ⟨e,i⟩))) k =
      sourceRowForm A C (ord (ord.symm (.inr ⟨e,i⟩))) p at he
    simpa only [Equiv.apply_symm_apply, sourceRowForm, LinearMap.comp_apply] using he

/-- `j` is the number of the weakest original Schwinger slots. The
Gaussian and every original route outside those slots vanish on this space. -/
def sourceNullFlag (A : V →ₗ[ℝ] DirectionalMomentum a)
    (C : ∀ e, V →ₗ[ℝ] DirectionalMomentum (b e)) (j : ℕ) : Submodule ℝ V where
  carrier := {k | A k = 0 ∧ ∀ e : Fin m, j ≤ e.val → C e k = 0}
  zero_mem' := ⟨map_zero _,fun _ _ => map_zero _⟩
  add_mem' := by
    rintro k p ⟨hA,hC⟩ ⟨hA',hC'⟩
    exact ⟨by rw [map_add,hA,hA',add_zero],fun e he => by rw [map_add,hC e he,hC' e he,add_zero]⟩
  smul_mem' := by
    rintro r k ⟨hA,hC⟩
    exact ⟨by rw [map_smul,hA,smul_zero],fun e he => by rw [map_smul,hC e he,smul_zero]⟩

private theorem sourceStrongTag {j : ℕ} (hj : j ≤ m) (l : NetworkRowLabel a m b) :
    (sourceRowTier l).val ≤ m-j ↔ (sourceRowSlot l).elim True (fun e => j ≤ e.val) := by
  cases l with
  | inl i => simp [sourceRowTier, sourceRowSlot]
  | inr u =>
    simp only [sourceRowTier, sourceRowSlot, Fin.val_succ, Fin.val_rev, Option.elim_some]
    have hu := u.1.isLt
    omega

private theorem prefix_from_mono {N L : ℕ} (tag : Fin N → Fin L) (h : Monotone tag) (u : ℕ) :
    ∃ n : ℕ, n ≤ N ∧ ∀ i : Fin N, (tag i).val ≤ u ↔ i.val < n := by
  classical
  let s : Finset (Fin N) := Finset.univ.filter (fun i => (tag i).val ≤ u)
  by_cases hs : s.Nonempty
  · let p := s.max' hs
    refine ⟨p.val+1,p.isLt,fun i => ?_⟩
    have hp : (tag p).val ≤ u := (Finset.mem_filter.mp (Finset.max'_mem s hs)).2
    constructor
    · intro hi
      exact Nat.lt_succ_iff.mpr (Finset.le_max' s i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩))
    · intro hi
      exact (Fin.le_iff_val_le_val.mp (h (Fin.le_iff_val_le_val.mpr (Nat.lt_succ_iff.mp hi)))).trans hp
  · refine ⟨0,zero_le _,fun i => ?_⟩
    simp only [Nat.not_lt_zero, iff_false]
    intro hi
    exact hs ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩

/-- The actual Gaussian-and-unseen-route kernel is one of the greedy
prefix annihilators. Row ordering and the literal route blocks determine
its prefix, with no arbitrary rank or coordinate assumption. -/
theorem sourceNullFlag_eq_prefix (A : V →ₗ[ℝ] DirectionalMomentum a)
    (C : ∀ e, V →ₗ[ℝ] DirectionalMomentum (b e))
    (ord : Fin (Fintype.card (NetworkRowLabel a m b)) ≃ NetworkRowLabel a m b)
    (hord : Monotone (sourceRowTier ∘ ord)) {j : ℕ} (hj : j ≤ m) :
    ∃ n : ℕ, n ≤ Fintype.card (NetworkRowLabel a m b) ∧
      (∀ i, i.val < n ↔ (sourceRowSlot (ord i)).elim True (fun e => j ≤ e.val)) ∧
      sourceNullFlag A C j = nullPrefix (sourceRowForm A C ∘ ord) n := by
  obtain ⟨n,hn,hnp⟩ := prefix_from_mono _ hord (m-j)
  have ht (i : Fin (Fintype.card (NetworkRowLabel a m b))) :
      i.val < n ↔ (sourceRowSlot (ord i)).elim True (fun e => j ≤ e.val) :=
    (hnp i).symm.trans (sourceStrongTag hj _)
  refine ⟨n,hn,ht,?_⟩
  ext k
  change (A k = 0 ∧ ∀ e : Fin m, j ≤ e.val → C e k = 0) ↔
    ∀ i, i.val < n → sourceRowForm A C (ord i) k = 0
  constructor
  · rintro ⟨ha,hc⟩ i hi
    have hstrong := (ht i).1 hi
    cases hlabel : ord i with
    | inl z => simp [sourceRowForm,ha]
    | inr t =>
      have he : j ≤ t.1.val := by simpa only [hlabel,sourceRowSlot,Option.elim_some] using hstrong
      simp [sourceRowForm,hc _ he]
  · intro h
    have he (l : NetworkRowLabel a m b) (hl : (sourceRowSlot l).elim True (fun e => j ≤ e.val)) :
        sourceRowForm A C l k = 0 := by
      have hs : (sourceRowSlot (ord (ord.symm l))).elim True (fun e => j ≤ e.val) := by rwa [Equiv.apply_symm_apply]
      simpa only [Equiv.apply_symm_apply] using h (ord.symm l) ((ht _).2 hs)
    refine ⟨PiLp.ext (fun i => ?_),fun e hj => PiLp.ext (fun i => ?_)⟩
    · simpa only [sourceRowForm, LinearMap.comp_apply] using he (Sum.inl i) trivial
    · simpa only [sourceRowForm, LinearMap.comp_apply] using he (.inr ⟨e,i⟩) hj

/-- The physical null flag has dimension equal to the number of chosen
coordinates with original route slots among the first `j` weakest ones. -/
theorem sourceNullFlag_finrank_eq_weak_slots [FiniteDimensional ℝ V]
    (A : V →ₗ[ℝ] DirectionalMomentum a) (C : ∀ e, V →ₗ[ℝ] DirectionalMomentum (b e))
    (ord : Fin (Fintype.card (NetworkRowLabel a m b)) ≃ NetworkRowLabel a m b)
    (hord : Monotone (sourceRowTier ∘ ord))
    (hinj : Function.Injective (fun k : V => (A k, fun e => C e k))) {j : ℕ} (hj : j ≤ m) :
    let rows := sourceRowForm A C ∘ ord
    Module.finrank ℝ (sourceNullFlag A C j) =
      Nat.card {i : GreedyIndex rows // (sourceRowSlot (ord i.val)).elim False (fun e => e.val < j)} := by
  classical
  let rows := sourceRowForm A C ∘ ord
  have hi : Function.Injective (fun k : V => fun i => rows i k) := sourceRows_injective_of_combined A C ord hinj
  have hspan := rowSpan_top_of_injective rows hi
  obtain ⟨n,hn,ht,he⟩ := sourceNullFlag_eq_prefix A C ord hord hj
  change Module.finrank ℝ (sourceNullFlag A C j) =
    Nat.card {i : GreedyIndex rows // (sourceRowSlot (ord i.val)).elim False (fun e => e.val < j)}
  rw [he, nullPrefix_finrank rows hspan hn, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr (Equiv.subtypeEquivRight (fun i : GreedyIndex rows => ?_))
  change n ≤ i.val.val ↔ (sourceRowSlot (ord i.val)).elim False (fun e => e.val < j)
  rw [← Nat.not_lt, ht]
  cases sourceRowSlot (ord i.val) <;> simp

/-- One fixed Euclidean chart on the ordered sector diagonalizes the
precision up to uniform positive constants and realizes every original
weak-route flag. The original route label of each chart coordinate
records whether its weight is one or one of the exact `t` values. -/
theorem source_greedy_euclidean_chart {d : ℕ}
    (A : DirectionalMomentum d →ₗ[ℝ] DirectionalMomentum a)
    (C : ∀ e, DirectionalMomentum d →ₗ[ℝ] DirectionalMomentum (b e))
    (hinj : Function.Injective (fun k : DirectionalMomentum d => (A k, fun e => C e k))) :
    ∃ (chart : DirectionalMomentum d ≃L[ℝ] DirectionalMomentum d)
      (label : Fin d → Option (Fin m)) (D : ℝ), 1 ≤ D ∧
      (∀ (t : Fin m → ℝ) (k : DirectionalMomentum d),
        Monotone t → (∀ e, 0 ≤ t e) → (∀ e, t e ≤ 1) →
        let dQ := ∑ i, (label i).elim 1 t * (chart k i)^2
        dQ ≤ sourcePrecision A C t k ∧ sourcePrecision A C t k ≤ D*dQ) ∧
      (∀ j : ℕ, j ≤ m →
        Module.finrank ℝ (sourceNullFlag A C j) = Nat.card {i : Fin d // (label i).elim False (fun e => e.val < j)} ∧
        ∀ k : DirectionalMomentum d, k ∈ sourceNullFlag A C j ↔
          ∀ i : Fin d, (label i).elim True (fun e => j ≤ e.val) → chart k i = 0) := by
  obtain ⟨ord,D,hord,hD,hcmp⟩ := source_greedy_precision_compare A C
  let rows := sourceRowForm A C ∘ ord
  let hspan := rowSpan_top_of_injective rows (sourceRows_injective_of_combined A C ord hinj)
  let idx := greedyEuclideanIndex rows hspan
  let label (i : Fin d) := sourceRowSlot (ord (idx i).val)
  refine ⟨greedyEuclideanChart rows hspan,label,D,hD,?_,?_⟩
  · intro t k ht h0 h1
    have he := selectedPrecision_eq_euclideanChart rows hspan
      (schwingerTierWeight t ∘ sourceRowTier ∘ ord) k
    change selectedPrecision rows (greedyRows rows _) (schwingerTierWeight t ∘ sourceRowTier ∘ ord) k =
      (∑ i : Fin d, schwingerTierWeight t (sourceRowTier (ord (idx i).val)) *
        (greedyEuclideanChart rows hspan k i)^2) at he
    simp only [sourceRowTierWeight_eq_slot] at he
    dsimp only [label]
    rw [← he]
    exact hcmp t k ht h0 h1
  · intro j hj
    constructor
    · rw [sourceNullFlag_finrank_eq_weak_slots A C ord hord hinj hj]
      exact Nat.card_congr (Equiv.subtypeEquivOfSubtype idx).symm
    · intro k
      obtain ⟨n,hn,ht,hflag⟩ := sourceNullFlag_eq_prefix A C ord hord hj
      rw [hflag, nullPrefix_iff_coordinate_zero rows hspan hn]
      constructor
      · intro h i hi
        rw [greedyEuclideanChart_apply]
        have hval := h (idx i) ((ht (idx i).val).2 hi)
        rwa [greedyCoordinates_apply] at hval
      · intro h i hi
        have hz := h (idx.symm i) (show (label (idx.symm i)).elim True (fun e => j ≤ e.val) from by
          dsimp only [label]
          rw [Equiv.apply_symm_apply]
          exact (ht i.val).1 hi)
        rw [greedyEuclideanChart_apply, Equiv.apply_symm_apply] at hz
        rwa [greedyCoordinates_apply]

end UV.ContinueNetworkPrecision
