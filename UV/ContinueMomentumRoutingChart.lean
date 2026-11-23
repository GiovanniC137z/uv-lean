import UV.ContinueMomentumRouting

/-! Exact solution of the momentum conservation equations for a
spanning tree of a finite labelled multigraph. The momentum group
can be the full carrier plane or its reciprocal lattice. -/

noncomputable section

open Classical Finset MeasureTheory

namespace UV

variable {V E A : Type*} [Fintype V] [Fintype E] [AddCommGroup A] (G : MomentumNetwork V E)

abbrev MomentumNetwork.Chords (T : Finset E) := {e : E // e ∉ T}

def MomentumNetwork.extendChords (T : Finset E) (c : MomentumNetwork.Chords T → A) (e : E) : A :=
  if he : e ∈ T then 0 else c ⟨e,he⟩

def MomentumNetwork.residual (T : Finset E) (s : V → A) (c : MomentumNetwork.Chords T → A) : V → A :=
  s-G.boundary (univ \ T) (MomentumNetwork.extendChords T c)

def MomentumNetwork.route (T : Finset E) (s : V → A) (c : MomentumNetwork.Chords T → A) (e : E) : A :=
  if he : e ∈ T then ∑ v ∈ G.tailCut T e, G.residual T s c v else c ⟨e,he⟩

omit [Fintype V] [Fintype E] in
theorem MomentumNetwork.boundary_congr {S : Finset E} {f g : E → A} (he : ∀ e ∈ S, f e = g e) :
    G.boundary S f = G.boundary S g :=
  Finset.sum_congr rfl fun e h => by rw [he e h]

omit [Fintype V] in
theorem MomentumNetwork.boundary_partition (T : Finset E) (q : E → A) :
    G.boundary univ q = G.boundary (univ \ T) q + G.boundary T q :=
  (Finset.sum_sdiff (Finset.subset_univ T)).symm

theorem MomentumNetwork.route_conserved {T : Finset E} (hT : G.IsSpanningTree T) (root : V) (s : V → A)
    (hs : ∑ v, s v = 0) (c : MomentumNetwork.Chords T → A) : G.boundary univ (G.route T s c) = s := by
  let r := G.residual T s c
  have hr : ∑ v, r v = 0 := by
    simp only [r,MomentumNetwork.residual,Pi.sub_apply,Finset.sum_sub_distrib,hs,G.total_boundary,sub_zero]
  obtain ⟨q,hq⟩ := G.conserved_in_range hT.1 root r hr
  have ht : G.boundary T (G.route T s c) = r := by
    rw [←hq]; apply G.boundary_congr
    intro e he
    simp only [MomentumNetwork.route,dif_pos he]
    simpa only [hq,r] using G.tree_cut_momentum hT he q
  have hc : G.boundary (univ \ T) (G.route T s c) = G.boundary (univ \ T) (MomentumNetwork.extendChords T c) := by
    apply G.boundary_congr
    intro e he
    simp only [MomentumNetwork.route,MomentumNetwork.extendChords,dif_neg (mem_sdiff.mp he).2]
  rw [G.boundary_partition T,hc,ht]
  dsimp only [r,MomentumNetwork.residual]
  abel

theorem MomentumNetwork.route_recovers {T : Finset E} (hT : G.IsSpanningTree T) (q : E → A) :
    G.route T (G.boundary univ q) (fun e => q e.val) = q := by
  let c : MomentumNetwork.Chords T → A := fun e => q e.val
  have hc : G.boundary (univ \ T) (MomentumNetwork.extendChords T c) = G.boundary (univ \ T) q := by
    apply G.boundary_congr
    intro e he
    simp only [MomentumNetwork.extendChords,c,dif_neg (mem_sdiff.mp he).2]
  have hr : G.residual T (G.boundary univ q) c = G.boundary T q := by
    rw [MomentumNetwork.residual,G.boundary_partition T,hc]; abel
  funext e
  change G.route T (G.boundary univ q) c e = _
  by_cases he : e ∈ T
  · simpa only [MomentumNetwork.route,dif_pos he,hr] using G.tree_cut_momentum hT he q
  · simp only [MomentumNetwork.route,dif_neg he,c]

/-- With external momentum conserved, every assignment on the chords
extends uniquely to a flow obeying every vertex equation. -/
def MomentumNetwork.routingEquiv {T : Finset E} (hT : G.IsSpanningTree T) (root : V) (s : V → A) (hs : ∑ v, s v = 0) :
    (MomentumNetwork.Chords T → A) ≃ {q : E → A // G.boundary univ q = s} where
  toFun c := ⟨G.route T s c,G.route_conserved hT root s hs c⟩
  invFun q e := q.val e.val
  left_inv c := funext fun e => by simp [MomentumNetwork.route,e.property]
  right_inv q := Subtype.ext (by simpa only [←q.property] using G.route_recovers hT q.val)

theorem MomentumNetwork.routing_exists (hc : G.Connected univ) (root : V) (s : V → A) (hs : ∑ v, s v = 0) :
    ∃ T : Finset E, G.IsSpanningTree T ∧ Nonempty ((MomentumNetwork.Chords T → A) ≃ {q : E → A // G.boundary univ q = s}) := by
  obtain ⟨T,_,hT⟩ := G.spanning_tree hc
  exact ⟨T,hT,⟨G.routingEquiv hT root s hs⟩⟩

variable {Z : Type*} [MeasurableSpace Z] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableSub₂ A]

/-- Every routed edge is a finite signed sum of the external momenta and
independent chord momenta. The result applies directly to shared transfers. -/
theorem MomentumNetwork.route_measurable (T : Finset E) {s : Z → V → A} (hs : ∀ v, Measurable (s · v))
    {c : Z → MomentumNetwork.Chords T → A} (hc : ∀ e, Measurable (c · e)) (e : E) : Measurable (fun z => G.route T (s z) (c z) e) := by
  classical
  by_cases he : e ∈ T
  · simp only [MomentumNetwork.route,dif_pos he]
    apply Finset.measurable_sum
    intro v _
    change Measurable (fun z => s z v - (G.boundary (univ \ T) (MomentumNetwork.extendChords T (c z))) v)
    apply (hs v).sub
    simp only [MomentumNetwork.boundary,Finset.sum_apply,Pi.sub_apply,Pi.single_apply]
    apply Finset.measurable_sum
    intro f hf
    have hf' := (mem_sdiff.mp hf).2
    simp only [MomentumNetwork.extendChords,dif_neg hf']
    split_ifs <;> first | exact (hc _).sub (hc _) | exact (hc _).sub measurable_const | exact measurable_const.sub (hc _) | exact measurable_const
  · simpa only [MomentumNetwork.route,dif_neg he] using hc ⟨e,he⟩

end UV
