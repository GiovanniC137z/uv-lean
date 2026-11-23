import UV.ContinueNormalRankGraph

/-! Photon momenta of a finite connected contracted multigraph. Edges have
independent labels and an orientation. A spanning tree is connected and
each of its edges disconnects its endpoints upon erasure. -/

noncomputable section

open Classical Finset
open scoped BigOperators

namespace UV

structure MomentumNetwork (V E : Type*) where
  tail : E → V
  head : E → V

variable {V E A : Type*} (G : MomentumNetwork V E)

def MomentumNetwork.Reaches (S : Finset E) : V → V → Prop :=
  Relation.EqvGen (fun x y => ∃ e ∈ S, G.tail e = x ∧ G.head e = y)

def MomentumNetwork.Connected (S : Finset E) : Prop := ∀ x y, G.Reaches S x y

def MomentumNetwork.IsSpanningTree (S : Finset E) : Prop :=
  G.Connected S ∧ ∀ e ∈ S, ¬G.Reaches (S.erase e) (G.tail e) (G.head e)

theorem MomentumNetwork.reaches_edge {S : Finset E} {e : E} (h : e ∈ S) :
    G.Reaches S (G.tail e) (G.head e) := .rel _ _ ⟨e,h,rfl,rfl⟩

theorem MomentumNetwork.reaches_lift {S T : Finset E}
    (h : ∀ e ∈ S, G.Reaches T (G.tail e) (G.head e)) {x y : V} (p : G.Reaches S x y) : G.Reaches T x y := by
  induction p with
  | rel _ _ hp => obtain ⟨e,he,rfl,rfl⟩ := hp; exact h e he
  | refl x => exact .refl x
  | symm x y _ ih => exact .symm x y ih
  | trans x y z _ _ ih₁ ih₂ => exact .trans x y z ih₁ ih₂

theorem MomentumNetwork.spanning_tree {S : Finset E} (h : G.Connected S) :
    ∃ T ⊆ S, G.IsSpanningTree T := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases ht : G.IsSpanningTree S
    · exact ⟨S,fun _ hx => hx,ht⟩
    obtain ⟨e,he,hconn⟩ : ∃ e ∈ S, G.Reaches (S.erase e) (G.tail e) (G.head e) := by
      by_contra! hn; exact ht ⟨h,hn⟩
    have hr : G.Connected (S.erase e) := fun x y => G.reaches_lift (fun f hf => by
      by_cases hfe : f = e
      · simpa only [hfe] using hconn
      · exact G.reaches_edge (mem_erase.mpr ⟨hfe,hf⟩)) (h x y)
    obtain ⟨T,hT,htr⟩ := ih (S.erase e) (erase_ssubset he) hr
    exact ⟨T,hT.trans (erase_subset ..),htr⟩

variable [AddCommGroup A]

/-- Outgoing minus incoming at each vertex. In particular a self-edge
has zero incidence even though its momentum is an independent variable. -/
def MomentumNetwork.boundary (S : Finset E) (q : E → A) : V → A :=
  ∑ e ∈ S, (Pi.single (G.tail e) (q e) - Pi.single (G.head e) (q e))

private def momentumBoundaryHom (S : Finset E) : (E → A) →+ (V → A) where
  toFun := G.boundary S
  map_zero' := by simp [MomentumNetwork.boundary]
  map_add' a b := by
    simp only [MomentumNetwork.boundary,Pi.add_apply,Pi.single_add,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    abel

theorem MomentumNetwork.boundary_one_edge {S : Finset E} {e : E} (he : e ∈ S) (t : A) :
    G.boundary S (Pi.single e t) = Pi.single (G.tail e) t - Pi.single (G.head e) t := by
  classical
  unfold MomentumNetwork.boundary
  rw [Finset.sum_eq_single e]
  · simp
  · intro f _ hfe; simp [Pi.single_eq_of_ne hfe]
  · exact fun hh => False.elim (hh he)

private theorem momentum_difference_in_range {S : Finset E} {x y : V} (p : G.Reaches S x y) (t : A) :
    Pi.single x t-Pi.single y t ∈ (momentumBoundaryHom (A := A) G S).range := by
  induction p with
  | rel _ _ hp =>
    obtain ⟨e,he,rfl,rfl⟩ := hp
    exact ⟨Pi.single e t,G.boundary_one_edge he t⟩
  | refl x => simp
  | symm x y _ ih => simpa only [neg_sub] using (momentumBoundaryHom (A := A) G S).range.neg_mem ih
  | trans x y z _ _ ih₁ ih₂ => simpa only [sub_add_sub_cancel] using (momentumBoundaryHom (A := A) G S).range.add_mem ih₁ ih₂

variable [Fintype V]

theorem MomentumNetwork.conserved_in_range {S : Finset E} (hS : G.Connected S) (root : V) (s : V → A)
    (hs : ∑ v, s v = 0) : ∃ q, G.boundary S q = s := by
  have h := (momentumBoundaryHom (A := A) G S).range.sum_mem (t := univ) (f := fun v => Pi.single v (s v)-Pi.single root (s v)) (fun v _ => momentum_difference_in_range G (hS v root) (s v))
  suffices he : (∑ v, (Pi.single v (s v)-Pi.single root (s v))) = s by
    rw [he] at h
    exact h
  rw [Finset.sum_sub_distrib]
  funext v
  simp only [Pi.sub_apply,Finset.sum_apply,Pi.single_apply]
  by_cases hv : v=root <;> simp [hv,hs]

private def momentumCutHom (C : Finset V) : (V → A) →+ A where
  toFun s := ∑ v ∈ C, s v
  map_zero' := by simp
  map_add' _ _ := by simp [Finset.sum_add_distrib]

omit [Fintype V] in
private theorem momentum_cut_single (C : Finset V) (v : V) (t : A) :
    momentumCutHom C (Pi.single v t) = if v ∈ C then t else 0 := by
  simp [momentumCutHom,Pi.single_apply]

theorem MomentumNetwork.total_boundary (S : Finset E) (q : E → A) : ∑ v, G.boundary S q v = 0 := by
  change momentumCutHom univ (G.boundary S q) = 0
  simp [MomentumNetwork.boundary,map_sum,momentum_cut_single]

/-- The component on the tail side of the cut formed by deleting e. -/
def MomentumNetwork.tailCut (T : Finset E) (e : E) : Finset V :=
  univ.filter (fun v => G.Reaches (T.erase e) (G.tail e) v)

theorem MomentumNetwork.tree_cut_momentum {T : Finset E} (hT : G.IsSpanningTree T)
    {e : E} (he : e ∈ T) (q : E → A) :
    (∑ v ∈ G.tailCut T e, G.boundary T q v) = q e := by
  classical
  let C := G.tailCut T e
  have hc (v : V) : v ∈ C ↔ G.Reaches (T.erase e) (G.tail e) v := by simp [C,MomentumNetwork.tailCut]
  have h₁ : G.tail e ∈ C := (hc _).mpr (.refl _)
  have h₂ : G.head e ∉ C := fun h => hT.2 e he ((hc _).mp h)
  change momentumCutHom C (G.boundary T q) = _
  rw [MomentumNetwork.boundary,map_sum,Finset.sum_eq_single e]
  · simp only [map_sub,momentum_cut_single,if_pos h₁,if_neg h₂,sub_zero]
  · intro f hf hfe
    have hp := G.reaches_edge (mem_erase.mpr ⟨hfe,hf⟩)
    have hiff : G.tail f ∈ C ↔ G.head f ∈ C := by
      rw [hc,hc]
      exact ⟨fun h => .trans _ _ _ h hp,fun h => .trans _ _ _ h (.symm _ _ hp)⟩
    simp only [map_sub,momentum_cut_single,hiff,sub_self]
  · exact fun h => False.elim (h he)

end UV
