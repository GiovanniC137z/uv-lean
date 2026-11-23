import UV.ContinueMomentumRoutingChart

/-! Cumulative carrier translations from the directed momenta incident on
the ordered charged insertions. A self-edge may attach to two different
marks on one loop; the two contributions cancel only in the vertex total. -/

noncomputable section

open Classical Finset MeasureTheory

namespace UV

variable {V E A : Type*} [Fintype V] [Fintype E] [AddCommGroup A] (G : MomentumNetwork V E)

structure MomentumMarks (G : MomentumNetwork V E) (r : V → ℕ) where
  outgoing : ∀ e, Fin (r (G.tail e))
  incoming : ∀ e, Fin (r (G.head e))

private def momentumMarkDelta {r : V → ℕ} (t : (v : V) × Fin (r v)) (a : A) (v : V) (j : Fin (r v)) : A :=
  if t = ⟨v,j⟩ then a else 0

omit [Fintype V] in
private theorem momentum_mark_sum {r : V → ℕ} (v w : V) (j : Fin (r w)) (a : A) :
    (∑ i : Fin (r v), momentumMarkDelta ⟨w,j⟩ a v i) = (Pi.single w a : V → A) v := by
  classical
  by_cases hv : w=v
  · subst w; simp [momentumMarkDelta]
  · have hn (i : Fin (r v)) : (⟨w,j⟩ : (u : V) × Fin (r u)) ≠ ⟨v,i⟩ := fun h => hv (congrArg Sigma.fst h)
    simp [momentumMarkDelta,hn,Ne.symm hv]

variable {r : V → ℕ}

def MomentumMarks.impulse (M : MomentumMarks G r) (q : E → A) (x : (v : V) → Fin (r v) → A)
    (v : V) (j : Fin (r v)) : A :=
  x v j - ∑ e, (momentumMarkDelta ⟨G.tail e,M.outgoing e⟩ (q e) v j -
                  momentumMarkDelta ⟨G.head e,M.incoming e⟩ (q e) v j)

def MomentumMarks.translation (M : MomentumMarks G r) (q : E → A) (x : (v : V) → Fin (r v) → A)
    (v : V) (j : Fin (r v+1)) : A := Fin.partialSum (M.impulse G q x v) j

omit [Fintype V] in
theorem MomentumMarks.total_impulse (M : MomentumMarks G r) (q : E → A) (x : (v : V) → Fin (r v) → A) (v : V) :
    ∑ j, M.impulse G q x v j = (∑ j, x v j)-G.boundary univ q v := by
  unfold MomentumMarks.impulse MomentumNetwork.boundary
  rw [Finset.sum_sub_distrib,Finset.sum_comm (s := univ) (t := univ) (f := fun (j : Fin (r v)) (e : E) =>
    momentumMarkDelta ⟨G.tail e,M.outgoing e⟩ (q e) v j-momentumMarkDelta ⟨G.head e,M.incoming e⟩ (q e) v j)]
  simp only [Finset.sum_sub_distrib,momentum_mark_sum,Finset.sum_apply,Pi.sub_apply]

omit [Fintype V] in
theorem MomentumMarks.translation_step (M : MomentumMarks G r) (q : E → A) (x : (v : V) → Fin (r v) → A) (v : V) (j : Fin (r v)) :
    M.translation G q x v j.succ = M.translation G q x v j.castSucc + M.impulse G q x v j :=
  Fin.partialSum_succ _ j

/-- Net external transfers include the prescribed change at tested endpoints. -/
def momentumMarkedSources {r : V → ℕ} (x : (v : V) → Fin (r v) → A) (δ : V → A) (v : V) : A := (∑ j, x v j)-δ v

theorem MomentumMarks.routed_endpoint (M : MomentumMarks G r) {T : Finset E} (hT : G.IsSpanningTree T)
    (root : V) (x : (v : V) → Fin (r v) → A) (δ : V → A) (hs : ∑ v, momentumMarkedSources x δ v = 0)
    (c : MomentumNetwork.Chords T → A) (v : V) :
    let q := G.route T (momentumMarkedSources x δ) c
    ∀ k : A, k+M.translation G q x v (Fin.last (r v)) = k+δ v := by
  intro q k
  have hh := G.route_conserved hT root (momentumMarkedSources x δ) hs c
  have he : (G.boundary univ q) v = (∑ j, x v j)-δ v := congrFun hh v
  have hsum := M.total_impulse G q x v
  rw [he,sub_sub_cancel] at hsum
  have hl : (List.ofFn (M.impulse G q x v)).length ≤ r v := by simp
  change k+((List.ofFn (M.impulse G q x v)).take (r v)).sum = k+δ v
  rw [List.take_of_length_le hl,List.sum_ofFn,hsum]

/-- A charged loop translated successively by its oriented incident
momenta returns to its starting momentum for every chord assignment. -/
theorem MomentumMarks.routed_return (M : MomentumMarks G r) {T : Finset E} (hT : G.IsSpanningTree T)
    (root : V) (x : (v : V) → Fin (r v) → A) (hs : ∑ v, ∑ j, x v j = 0) (c : MomentumNetwork.Chords T → A) (v : V) :
    let q := G.route T (fun v => ∑ j, x v j) c
    ∀ k : A, k+M.translation G q x v (Fin.last (r v)) = k+M.translation G q x v 0 := by
  intro q k
  have hh := G.route_conserved hT root (fun v => ∑ j, x v j) hs c
  have he : (G.boundary univ q) v = ∑ j, x v j := congrFun hh v
  have hsum := M.total_impulse G q x v
  rw [he,sub_self] at hsum
  unfold MomentumMarks.translation
  rw [Fin.partialSum_zero]
  have hl : (List.ofFn (M.impulse G q x v)).length ≤ r v := by simp
  change k+((List.ofFn (M.impulse G q x v)).take (r v)).sum = k+0
  rw [List.take_of_length_le hl,List.sum_ofFn,hsum]

variable {Z : Type*} [MeasurableSpace Z] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableSub₂ A]

omit [Fintype V] in
theorem MomentumMarks.translation_measurable (M : MomentumMarks G r) {q : Z → E → A} (hq : ∀ e, Measurable (q · e))
    {x : Z → (v : V) → Fin (r v) → A} (hx : ∀ v j, Measurable (fun z => x z v j)) (v : V) (i : Fin (r v+1)) :
    Measurable (fun z => M.translation G (q z) (x z) v i) := by
  have h j : Measurable (fun z => M.impulse G (q z) (x z) v j) := by
    apply (hx v j).sub (Finset.measurable_sum _ fun e _ => ?_)
    unfold momentumMarkDelta
    split_ifs <;> first | exact (hq _).sub (hq _) | exact (hq _).sub measurable_const | exact measurable_const.sub (hq _) | exact measurable_const
  induction i using Fin.inductionOn with
  | zero => simp only [MomentumMarks.translation,Fin.partialSum_zero]; exact measurable_const
  | succ j ih => simpa only [M.translation_step] using ih.add (h j)

end UV
