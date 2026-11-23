import UV.ContinueCompressedModesFockSea
import Mathlib.Data.List.NodupEquivFin

/-! A nonzero normal-ordered Wick matching is a permutation of the source
vertices: it joins the created orbital of each vertex to the destroyed
orbital of its successor, with time direction fixed by its energy band. -/

noncomputable section
open List
namespace UV.FermionWick

variable {ν ι : Type*}

def sourceWord (vs : List ν) (a b : ν→ι) := vs.map (fun i => vertex i (a i) (b i))

theorem slot_mem_source {vs : List ν} {a b : ν→ι} {z : Slot ν ι} (h : z∈slots (sourceWord vs a b)) :
    z.vertex∈vs ∧ z.orbital=(if z.create then a z.vertex else b z.vertex) := by
  obtain ⟨l,hl,hz⟩ := List.mem_flatMap.mp h
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hl
  simp only [vertex,fields,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl <;> exact ⟨hi,rfl⟩

theorem ordered_source {vs : List ν} (t : ν→ℝ) (a b : ν→ι) (h : vs.Pairwise (fun i j => t j<t i)) :
    ordered (fun x y : Slot ν ι => t y.vertex<t x.vertex) (sourceWord vs a b) := by
  induction vs with
  | nil => trivial
  | cons i vs ih =>
    obtain ⟨h₁,h₂⟩ := List.pairwise_cons.mp h
    refine ⟨?_,ih h₂⟩
    intro x hx y hy
    have hh := h₁ y.vertex (slot_mem_source hy).1
    rcases (show x=⟨i,true,a i⟩ ∨ x=⟨i,false,b i⟩ by simpa [fields,vertex] using hx) with rfl|rfl <;> exact hh

def select (created : Bool) (e : Edge (Slot ν ι)) :=
  if e.first.create=created then e.first else e.second

private def selectVertex (created : Bool) (x : Slot ν ι) : Option ν :=
  if x.create=created then some x.vertex else none

private theorem selected_source (pol : Bool) (vs : List ν) (a b : ν→ι) :
    (slots (sourceWord vs a b)).filterMap (selectVertex pol)=vs := by
  induction vs with
  | nil => rfl
  | cons i vs ih =>
    change (⟨i,true,a i⟩::⟨i,false,b i⟩::slots (sourceWord vs a b)).filterMap (selectVertex pol)=_
    cases pol <;> simp [selectVertex,ih]

private theorem selected_edges (pol : Bool) (es : List (Edge (Slot ν ι)))
    (opp : ∀e∈es, e.first.create≠e.second.create) :
    (endpoints es).filterMap (selectVertex pol) = es.map (fun e => (select pol e).vertex) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have h := opp e (List.mem_cons_self ..)
    have hh := ih (fun x hx => opp x (List.mem_cons_of_mem _ hx))
    change (e.first::e.second::endpoints es).filterMap (selectVertex pol)=_
    cases hx : e.first.create <;> cases hy : e.second.create <;> cases pol <;>
      simp_all [selectVertex,select]

private def vertexChart [DecidableEq ν] (es : List (Edge (Slot ν ι))) (vs : List ν)
    (nd : vs.Nodup) (covers : ∀i:ν, i∈vs) (pol : Bool)
    (h : (es.map (fun e => (select pol e).vertex)).Perm vs) : Fin es.length ≃ ν :=
  (finCongr (List.length_map _).symm).trans
    (List.Nodup.getEquivOfForallMemList _ (h.nodup_iff.mpr nd) (fun i => h.mem_iff.mpr (covers i)))

private theorem chart_apply [DecidableEq ν] (es : List (Edge (Slot ν ι))) (vs : List ν)
    (nd : vs.Nodup) (covers : ∀i:ν, i∈vs) (pol : Bool)
    (h : (es.map (fun e => (select pol e).vertex)).Perm vs) (i : Fin es.length) :
    vertexChart es vs nd covers pol h i=(select pol (es.get i)).vertex := by
  simp [vertexChart,List.Nodup.getEquivOfForallMemList]

/-- The exact pairing enforces both orbital conservation and the time/band
ordering used in the loop estimate. It has no one-vertex cycles. -/
theorem matching_permutation [DecidableEq ι] (band : ι→Bool) (E : ι→ℝ) (t : ν→ℝ)
    (vs : List ν) (nd : vs.Nodup) (covers : ∀i:ν, i∈vs) (times : vs.Pairwise (fun i j => t j<t i))
    (a b : ν→ι) (es : List (Edge (Slot ν ι))) (n : ℕ)
    (h : es∈matchings n (sourceWord vs a b)) (hne : amplitude (seaCovariance band E t) es≠0) :
    ∃ σ : Equiv.Perm ν, (∀ e∈es, σ (select true e).vertex=(select false e).vertex) ∧
      ∀i:ν, b (σ i)=a i ∧ (if band (a i) then t i<t (σ i) else t (σ i)<t i) ∧ σ i≠i := by
  classical
  have hp := matching_uses_all _ _ es h
  have fore := matching_edges_ordered _ _ _ (ordered_source t a b times) h
  have cf := nonzero_edge band E t es hne
  have opp (e) (he : e∈es) : e.first.create≠e.second.create := by
    obtain ⟨_,hx,hy⟩ := cf e he
    rwa [hy]
  have perm (pol): (es.map (fun e => (select pol e).vertex)).Perm vs := by
    have h := hp.filterMap (selectVertex pol)
    rwa [selected_edges _ _ opp,selected_source] at h
  let V := fun pol => vertexChart es vs nd covers pol (perm pol)
  let σ : Equiv.Perm ν := (V true).symm.trans (V false)
  have hmap (e) (he:e∈es) : σ (select true e).vertex=(select false e).vertex := by
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp he
    rw [←chart_apply es vs nd covers true (perm true),←chart_apply es vs nd covers false (perm false)]
    change (V false) ((V true).symm ((V true) i))=(V false) i
    rw [Equiv.symm_apply_apply]
  refine ⟨σ,hmap,?_⟩
  intro i
  obtain ⟨r,hr⟩ := (V true).surjective i
  let e := es.get r
  have hem : e∈es := List.get_mem ..
  have h₁ : (select true e).vertex=i := (chart_apply es vs nd covers true (perm true) r).symm.trans hr
  have h₂ : (select false e).vertex=σ i := by rw [←h₁,hmap e hem]
  have hsrc (q : Slot ν ι) (hq : q=e.first ∨ q=e.second) : q.orbital=(if q.create then a q.vertex else b q.vertex) := by
    apply (slot_mem_source (hp.mem_iff.mp (show q∈endpoints es from List.mem_flatMap.mpr ⟨e,hem,by simpa using hq⟩))).2
  have fo := fore e hem
  obtain ⟨hm,hx,hy⟩ := cf e hem
  have hs := hsrc e.first (Or.inl rfl)
  have hs' := hsrc e.second (Or.inr rfl)
  cases h₀ : band e.first.orbital with
  | false =>
    have hF : e.first.create=true := by simpa [h₀] using hx
    have hG : e.second.create=false := hy.trans h₀
    have hf : e.first.vertex=i := by simpa [select,hF] using h₁
    have hg : e.second.vertex=σ i := by simpa [select,hF] using h₂
    have ha : e.first.orbital=a i := by simpa [hF,hf] using hs
    have hb : e.second.orbital=b (σ i) := by simpa [hG,hg] using hs'
    have ht : t (σ i)<t i := by simpa only [hf,hg] using fo
    exact ⟨hb.symm.trans (hm.symm.trans ha),by simpa only [←ha,h₀,Bool.false_eq_true,if_false] using ht,
      fun eq => (ne_of_lt ht) (congrArg t eq)⟩
  | true =>
    have hF : e.first.create=false := by simpa [h₀] using hx
    have hG : e.second.create=true := hy.trans h₀
    have hf : e.first.vertex=σ i := by simpa [select,hF] using h₂
    have hg : e.second.vertex=i := by simpa [select,hF] using h₁
    have ha : e.second.orbital=a i := by simpa [hG,hg] using hs'
    have hb : e.first.orbital=b (σ i) := by simpa [hF,hf] using hs
    have ht : t i<t (σ i) := by simpa only [hf,hg] using fo
    exact ⟨hb.symm.trans (hm.trans ha),by simpa only [←ha,←hm,h₀,if_true] using ht,
      fun eq => (ne_of_lt ht) (congrArg t eq.symm)⟩

end UV.FermionWick
