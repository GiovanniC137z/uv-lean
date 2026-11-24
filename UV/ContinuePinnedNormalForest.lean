import UV.ContinuePinnedNormalMinors
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! The complementary incidence polynomial selects exactly the
rooted forest bases. Their labelled edge selections become spanning
trees when the held vertices are identified at the common root. -/

noncomputable section
open Matrix Set MeasureTheory
open scoped BigOperators Matrix
namespace UV

def groundedSupportGraph {E : Type*} {L : ℕ}
    (src dst : E → Option (Fin L)) : SimpleGraph (Option (Fin L)) where
  Adj u v := u ≠ v ∧ ∃ e, (src e = u ∧ dst e = v) ∨ (src e = v ∧ dst e = u)
  symm := by intro u v h; exact ⟨h.1.symm,h.2.imp (fun _ he => he.symm)⟩
  loopless := by intro u h; exact h.1 rfl

theorem grounded_incidence_injective_iff_connected {E : Type*} [Fintype E] {L : ℕ}
    (src dst : E → Option (Fin L)) :
    Function.Injective (groundedNetworkIncidence src dst).mulVec ↔ (groundedSupportGraph src dst).Connected := by
  classical
  let G := groundedSupportGraph src dst
  have hcover : NetworkOrientationCovers G src dst := fun _ _ h => h.2
  constructor
  · intro h
    have hall (u : Option (Fin L)) : G.Reachable none u := by
      cases u with
      | none => exact SimpleGraph.Reachable.refl _
      | some i =>
        by_contra hi
        let x := fun j : Fin L => if G.Reachable none (some j) then (0:ℝ) else 1
        have hLift (v : Option (Fin L)) : networkRootLift x v = if G.Reachable none v then 0 else 1 := by
          cases v with
          | none => simp [networkRootLift]
          | some j => rfl
        have hx : groundedNetworkIncidence src dst *ᵥ x = 0 := by
          funext e
          have hR : G.Reachable none (src e) ↔ G.Reachable none (dst e) := by
            by_cases he : src e = dst e
            · rw [he]
            · have hA : G.Adj (src e) (dst e) := ⟨he,⟨e,Or.inl ⟨rfl,rfl⟩⟩⟩
              exact ⟨fun h => h.trans hA.reachable,fun h => h.trans hA.symm.reachable⟩
          rw [groundedNetworkIncidence_mulVec,hLift,hLift,hR,sub_self]
          rfl
        have hx₀ : x = 0 := h (hx.trans (Matrix.mulVec_zero _).symm)
        have he := congrFun hx₀ i
        simp [x,hi] at he
    exact (SimpleGraph.connected_iff_exists_forall_reachable (G := G)).mpr ⟨none,hall⟩
  · intro h
    exact groundedNetworkIncidence_injective G src dst h hcover

private theorem groundedSupportGraph_edge_card_le {E : Type*} [Fintype E] {L : ℕ}
    (src dst : E → Option (Fin L)) : Nat.card (groundedSupportGraph src dst).edgeSet ≤ Nat.card E := by
  classical
  let G := groundedSupportGraph src dst
  let U := {e : E // src e ≠ dst e}
  let f : U → G.edgeSet := fun e => ⟨s(src e,dst e),G.mem_edgeSet.mpr ⟨e.2,⟨e,Or.inl ⟨rfl,rfl⟩⟩⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨a,ha⟩
    induction a using Sym2.inductionOn with
    | _ u v =>
      obtain ⟨hn,e,he|he⟩ := G.mem_edgeSet.mp ha
      · refine ⟨⟨e,by rw [he.1,he.2]; exact hn⟩,Subtype.ext ?_⟩
        simp only [f,he.1,he.2]
      · refine ⟨⟨e,by rw [he.1,he.2]; exact hn.symm⟩,Subtype.ext ?_⟩
        simp only [f,he.1,he.2,Sym2.eq_swap]
  exact (Nat.card_le_card_of_surjective f hf).trans
    (Nat.card_le_card_of_injective (Subtype.val : U → E) Subtype.val_injective)

/-- A square independent selection of labelled lines is a spanning
tree in the graph obtained by identifying the held vertices. -/
theorem grounded_incidence_injective_iff_tree {E : Type*} [Fintype E] {L : ℕ}
    (src dst : E → Option (Fin L)) (hcard : Nat.card E = L) :
    Function.Injective (groundedNetworkIncidence src dst).mulVec ↔ (groundedSupportGraph src dst).IsTree := by
  rw [grounded_incidence_injective_iff_connected,SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨fun h => ⟨h,?_⟩,And.left⟩
  have hlo := h.card_vert_le_card_edgeSet_add_one
  have hhi := groundedSupportGraph_edge_card_le src dst
  have he : Nat.card (Option (Fin L)) = L+1 := by simp [Nat.card_eq_fintype_card]
  omega

def pinnedSelectedGraph {L N : ℕ} {B : Type*} (src dst : Fin N → Fin L ⊕ B)
    (S : Finset (Fin N)) : SimpleGraph (Option (Fin L)) :=
  groundedSupportGraph (pinnedHeldEndpoint ∘ src ∘ (Subtype.val : S → Fin N))
    (pinnedHeldEndpoint ∘ dst ∘ (Subtype.val : S → Fin N))

private theorem groundedSupportGraph_reindex {E E' : Type*} {L : ℕ}
    (src dst : E → Option (Fin L)) (e : E' ≃ E) :
    groundedSupportGraph (src ∘ e) (dst ∘ e) = groundedSupportGraph src dst := by
  ext u v
  constructor
  · rintro ⟨hn,i,h⟩
    exact ⟨hn,e i,h⟩
  · rintro ⟨hn,i,h⟩
    refine ⟨hn,e.symm i,?_⟩
    simpa only [Function.comp_apply,e.apply_symm_apply] using h

theorem pinnedHeldMinorCoefficient_eq_one_iff_tree {L N : ℕ} {B : Type*}
    (src dst : Fin N → Fin L ⊕ B) (S : Finset (Fin N)) (hS : S.card = L) :
    retainedMinorCoefficient (pinnedHeldIncidence src dst) S = 1 ↔ (pinnedSelectedGraph src dst S).IsTree := by
  classical
  let e : Fin L ≃ S := Fintype.equivOfCardEq (by simp [hS])
  let u := pinnedHeldEndpoint ∘ src ∘ (Subtype.val : S → Fin N)
  let v := pinnedHeldEndpoint ∘ dst ∘ (Subtype.val : S → Fin N)
  let A := groundedNetworkIncidence (u ∘ e) (v ∘ e)
  have he : retainedMinorCoefficient (pinnedHeldIncidence src dst) S = A.det^2 := by
    unfold retainedMinorCoefficient
    rw [dif_pos (hS.trans (Fintype.card_fin L).symm),← Matrix.det_transpose A]
    rfl
  have h := pinnedHeldMinorCoefficient_zero_or_one src dst S
  change retainedMinorCoefficient (pinnedHeldIncidence src dst) S = 1 ↔ (groundedSupportGraph u v).IsTree
  rw [he,← groundedSupportGraph_reindex u v e]
  rw [← grounded_incidence_injective_iff_tree _ _ (by simp [Nat.card_eq_fintype_card])]
  rw [Matrix.mulVec_injective_iff_isUnit,Matrix.isUnit_iff_isUnit_det,isUnit_iff_ne_zero]
  constructor
  · intro hs hz
    rw [hz] at hs
    norm_num at hs
  · intro hne
    rcases h with hzero|hone
    · rw [he,sq_eq_zero_iff] at hzero
      exact (hne hzero).elim
    · rw [← he,hone]

def pinnedRootedForestSelections {L N : ℕ} {B : Type*}
    (src dst : Fin N → Fin L ⊕ B) : Finset (Finset (Fin N)) := by
  classical
  exact ((Finset.univ : Finset (Fin N)).powersetCard L).filter
    (fun S => (pinnedSelectedGraph src dst S).IsTree)

/-- The exact forest polynomial for the equal-position pinned normal
graph. Self-loops remain in the products over complementary edges. -/
theorem pinnedHeldDurationPolynomial_eq_forest_sum {L N : ℕ} {B : Type*}
    (src dst : Fin N → Fin L ⊕ B) (t : Fin N → ℝ) (ht : ∀ i, 0 < t i) :
    pinnedDurationPolynomial (pinnedHeldIncidence src dst) t =
      ∑ S ∈ pinnedRootedForestSelections src dst, ∏ i ∈ Sᶜ, t i := by
  classical
  rw [pinnedDurationPolynomial_eq_minor_sum _ _ ht,Fintype.card_fin,pinnedRootedForestSelections,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S hS
  have he := pinnedHeldMinorCoefficient_eq_one_iff_tree src dst S (Finset.mem_powersetCard.mp hS).2
  by_cases hT : (pinnedSelectedGraph src dst S).IsTree
  · rw [if_pos hT,he.mpr hT,one_mul]
  · obtain h0|h1 := pinnedHeldMinorCoefficient_zero_or_one src dst S
    · rw [if_neg hT,h0,zero_mul]
    · exact (hT (he.mp h1)).elim

theorem pinnedHeld_selfLoop_complement {L N : ℕ} {B : Type*}
    (src dst : Fin N → Fin L ⊕ B) {S : Finset (Fin N)} (hS : S ∈ pinnedRootedForestSelections src dst)
    {e : Fin N} (he : src e = dst e) : e ∈ Sᶜ := by
  classical
  obtain ⟨hcard,hT⟩ := Finset.mem_filter.mp hS
  have hs : S.card = L := (Finset.mem_powersetCard.mp hcard).2
  have hone := (pinnedHeldMinorCoefficient_eq_one_iff_tree src dst S hs).mpr hT
  by_contra hn
  have hem : e ∈ S := Finset.notMem_compl.mp hn
  let f : Fin L ≃ S := Fintype.equivOfCardEq (by simp [hs])
  let j := f.symm ⟨e,hem⟩
  have hj : (f j).val = e := congrArg Subtype.val (f.apply_symm_apply ⟨e,hem⟩)
  have hzero : ((pinnedHeldIncidence src dst).submatrix id (Subtype.val ∘ f)).det = 0 :=
    Matrix.det_eq_zero_of_column_eq_zero j (fun i => by
      rw [Matrix.submatrix_apply,id_eq,Function.comp_apply,hj]
      exact pinnedHeldIncidence_selfLoop src dst he i)
  unfold retainedMinorCoefficient at hone
  rw [dif_pos (hs.trans (Fintype.card_fin L).symm)] at hone
  change ((pinnedHeldIncidence src dst).submatrix id (Subtype.val ∘ f)).det^2 = 1 at hone
  norm_num [hzero] at hone

theorem pinnedRootedForestSelections_nonempty {L N : ℕ} {B : Type*} (b : B)
    (G : SimpleGraph (Fin L ⊕ B)) (src dst : Fin N → Fin L ⊕ B) (hG : G.Connected)
    (hcover : ∀ u v, G.Adj u v → ∃ e, (src e = u ∧ dst e = v) ∨ (src e = v ∧ dst e = u)) :
    (pinnedRootedForestSelections src dst).Nonempty := by
  let A := pinnedHeldIncidence src dst
  have hi := pinnedHeldIncidence_injective b G src dst hG hcover
  have hr : A.rank = Fintype.card (Fin L) := (pinned_normal_rank A hi).trans (Fintype.card_fin L).symm
  obtain ⟨lo,_,hlo,_,hb⟩ := pinnedDurationPolynomial_ordered_bounds A hr
  have hl := (hb (fun _ => 1) (fun _ _ _ => le_rfl) (fun _ => Real.zero_lt_one)).1
  have hpos := hlo.trans_le (by simpa using hl)
  apply Finset.nonempty_of_ne_empty
  intro hempty
  unfold A at hpos
  rw [pinnedHeldDurationPolynomial_eq_forest_sum _ _ _ (fun _ => Real.zero_lt_one),hempty,Finset.sum_empty] at hpos
  exact (lt_irrefl _ hpos)

theorem pinnedHeldHeatIntegral_forest {L N d : ℕ} {B : Type*} (b : B)
    (G : SimpleGraph (Fin L ⊕ B)) (src dst : Fin N → Fin L ⊕ B) (hG : G.Connected)
    (hcover : ∀ u v, G.Adj u v → ∃ e, (src e = u ∧ dst e = v) ∨ (src e = v ∧ dst e = u))
    {D : ℝ} (hD : 0 < D) (t : Fin N → ℝ) (ht : ∀ e, 0 < t e) :
    (∫ y : Fin d → EuclideanSpace ℝ (Fin L), pinnedHeldHeatProduct src dst D t y) =
      (4*Real.pi*D)^(-((N:ℝ)-L)*((d:ℝ)/2)) *
      (∑ S ∈ pinnedRootedForestSelections src dst, ∏ e ∈ Sᶜ, t e)^(-(d:ℝ)/2) := by
  simp_rw [pinnedHeldHeatProduct_incidence]
  rw [pinned_normal_heat_integral _ (pinnedHeldIncidence_injective b G src dst hG hcover) hD t ht,
    pinnedHeldDurationPolynomial_eq_forest_sum src dst t ht]

end UV
