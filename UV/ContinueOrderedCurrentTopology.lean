import UV.ContinueOrderedEnvelopeRouting
import UV.ContinueCompressedModesFockGraphs
import UV.ContinueOrderedCurrentTopologyData

/-! Finite combinatorics at fixed electric order, independently of unbounded
hopping length. Labels are all electric insertions. A permutation gives the
cyclic order of insertions on each marked charged path. The photon involution
pairs internal marks and leaves external marks fixed. -/

noncomputable section

namespace UV.SectorPlane.OrderedSewingTopology

variable {m : ℕ}

private def code (T : OrderedSewingTopology m) :
    Equiv.Perm (Fin m) × Equiv.Perm (Fin m) × (Fin m → Bool) :=
  (T.pathOrder,T.mate,T.coulomb)

private theorem code_injective : Function.Injective (code (m := m)) := by
  rintro ⟨a,b,c,h,g,f⟩ ⟨a',b',c',h',g',f'⟩ he
  change (a,b,c) = (a',b',c') at he
  obtain ⟨rfl,rfl,rfl⟩ := Prod.mk.inj he |>.imp_right Prod.mk.inj
  rfl

noncomputable instance : Fintype (OrderedSewingTopology m) := Fintype.ofInjective code code_injective

theorem card_bound (m : ℕ) : Fintype.card (OrderedSewingTopology m) ≤ m.factorial^2 * 2^m := by
  have h := Fintype.card_le_of_injective (code (m := m)) code_injective
  simpa only [Fintype.card_prod,Fintype.card_perm,Fintype.card_fin,Fintype.card_fun,Fintype.card_bool,
    sq,mul_assoc] using h

abbrev Vertex (T : OrderedSewingTopology m) := FermionWick.Cycle T.pathOrder
abbrev External (T : OrderedSewingTopology m) := {i : Fin m // T.mate i = i}
abbrev Edge (T : OrderedSewingTopology m) := {i : Fin m // i < T.mate i}

def vertex (T : OrderedSewingTopology m) (i : Fin m) : T.Vertex := FermionWick.cycleClass T.pathOrder i

theorem every_vertex_marked (T : OrderedSewingTopology m) (v : T.Vertex) : ∃ i, T.vertex i = v :=
  ⟨v.out,Quotient.out_eq _⟩

def src (T : OrderedSewingTopology m) (e : T.Edge) : T.Vertex := T.vertex e.val
def dst (T : OrderedSewingTopology m) (e : T.Edge) : T.Vertex := T.vertex (T.mate e.val)
def kind (T : OrderedSewingTopology m) (e : T.Edge) : OrderedPhotonKind :=
  if T.coulomb e.val then .coulomb else .transverse

/-- In each two-cycle, select the smaller endpoint as edge representative and
retain the endpoint choice. This includes parallel lines and self-contractions. -/
def endpoints (T : OrderedSewingTopology m) : T.External ⊕ (T.Edge × Bool) ≃ Fin m where
  toFun
    | .inl i => i.val
    | .inr (e,true) => e.val
    | .inr (e,false) => T.mate e.val
  invFun i := if h : T.mate i = i then .inl ⟨i,h⟩ else if l : i < T.mate i then .inr (⟨i,l⟩,true)
    else .inr (⟨T.mate i,by rw [T.pair_twice]; exact lt_of_le_of_ne (le_of_not_gt l) h⟩,false)
  left_inv x := by
    rcases x with i|⟨e,b⟩
    · simp [i.property]
    · rcases b with _|_
      · simp [T.pair_twice,ne_of_lt e.property,not_lt.mpr e.property.le]
      · simp [ne_of_gt e.property,e.property]
  right_inv i := by
    by_cases h : T.mate i = i
    · simp [h]
    · by_cases l : i < T.mate i <;> simp [h,l,T.pair_twice]

theorem electric_count (T : OrderedSewingTopology m) :
    m = Fintype.card T.External + 2*Fintype.card T.Edge := by
  have h := Fintype.card_congr T.endpoints
  simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,mul_comm] using h.symm

/-- Bond deletion is expressed on indexed photon edges, so two parallel
photons remain distinguishable. A self-loop already has coincident endpoints. -/
def reached (T : OrderedSewingTopology m) (allowed : T.Edge → Prop) (v w : T.Vertex) : Prop :=
  Relation.ReflTransGen (fun x y => ∃ e, allowed e ∧
    ((T.src e=x ∧ T.dst e=y) ∨ (T.src e=y ∧ T.dst e=x))) v w

def properConnected (T : OrderedSewingTopology m) : Prop :=
  (∀ v w, T.reached (fun _ => True) v w) ∧
    ∀ e, T.reached (fun j => j ≠ e) (T.src e) (T.dst e)

abbrev Surviving (m external : ℕ) := {T : OrderedSewingTopology m //
  Fintype.card T.External = external ∧ T.properConnected}

noncomputable instance (m external : ℕ) : Fintype (Surviving m external) := Fintype.ofFinite _

theorem surviving_card (m external : ℕ) :
    Fintype.card (Surviving m external) ≤ m.factorial^2*2^m :=
  (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans (card_bound m)

/-- Forgetting endpoint labels or taking any further symmetry quotient of
the surviving vacuum or two-point diagrams preserves the finite bound. -/
theorem quotient_card (m external : ℕ) (s : Setoid (Surviving m external)) :
    Nat.card (Quotient s) ≤ m.factorial^2*2^m := by
  classical
  letI : Fintype (Quotient s) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_le_of_surjective (Quotient.mk s) Quotient.mk_surjective).trans (surviving_card m external)

/-- An arbitrary finite marking with cyclic charged-path successors, a Wick
pairing on the internal endpoints, and channel assignments can be encoded
using any labelling by Fin m. Fixed points of the pairing are external. -/
def label {α : Type*} (e : α ≃ Fin m) (next pair : Equiv.Perm α) (scalar : α → Bool)
    (hp : ∀ i, pair (pair i) = i) (hk : ∀ i, scalar (pair i) = scalar i)
    (hx : ∀ i, pair i = i → scalar i = false) : OrderedSewingTopology m where
  pathOrder := e.permCongr next
  mate := e.permCongr pair
  coulomb := scalar ∘ e.symm
  pair_twice := fun i => by simp [hp]
  same_channel := fun i => by simp [hk]
  external_transverse := fun i h => hx _ (e.injective (by simpa using h))

/-- Simultaneously relabel all marked ends, preserving cyclic ordering, edge
pairing and photon kind. The definition also works restricted to a chosen
subset of surviving graphs. -/
def relabelSetoid (m : ℕ) : Setoid (OrderedSewingTopology m) where
  r T R := ∃ e : Equiv.Perm (Fin m), ∀ i,
    e (T.pathOrder i) = R.pathOrder (e i) ∧ e (T.mate i) = R.mate (e i) ∧ T.coulomb i = R.coulomb (e i)
  iseqv := {
    refl := fun _ => ⟨Equiv.refl _, fun _ => ⟨rfl,rfl,rfl⟩⟩
    symm := by
      rintro T R ⟨e,h⟩
      refine ⟨e.symm,fun i => ?_⟩
      obtain ⟨ha,hb,hc⟩ := h (e.symm i)
      simp only [Equiv.apply_symm_apply] at ha hb hc
      exact ⟨e.injective (by simpa using ha.symm),e.injective (by simpa using hb.symm),hc.symm⟩
    trans := by
      rintro T R S ⟨e,h⟩ ⟨f,k⟩
      refine ⟨e.trans f,fun i => ?_⟩
      exact ⟨(congrArg f (h i).1).trans (k _).1,
        (congrArg f (h i).2.1).trans (k _).2.1,(h i).2.2.trans (k _).2.2⟩ }

theorem label_independent {α : Type*} (e f : α ≃ Fin m) (next pair : Equiv.Perm α) (scalar : α → Bool)
    (hp : ∀ i, pair (pair i) = i) (hk : ∀ i, scalar (pair i) = scalar i)
    (hx : ∀ i, pair i = i → scalar i = false) :
    (relabelSetoid m).r (label e next pair scalar hp hk hx) (label f next pair scalar hp hk hx) := by
  refine ⟨e.symm.trans f,fun i => ?_⟩
  simp [label]

theorem unlabelled_surviving_card (m external : ℕ) :
    Nat.card (Quotient ((relabelSetoid m).comap (Subtype.val : Surviving m external → _))) ≤
      m.factorial^2*2^m := quotient_card m external _

end UV.SectorPlane.OrderedSewingTopology
