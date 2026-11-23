import UV.CurvatureWickMatchings

/-! Convert the partner choices of the literal Wick expansion to the
partitioned incidence used in the sector-plane graph estimates. Original
end order is retained on every edge, including probe-probe contractions. -/

noncomputable section

namespace UV.CurvatureWick

open UV.VerifyCurvatureRouting UV.VerifyCurvatureExpansion UV.VerifyCurvatureReindex
open UV.NextCurvatureLaw UV.AdvanceCurvatureWick

def pairEndpoint {α : Type*} (P : List (α × α)) (q : Fin P.length × Fin 2) : α :=
  if q.2 = 0 then (P.get q.1).1 else (P.get q.1).2

structure Realization {r p : ℕ} (P : List (EndPosition r p × EndPosition r p)) where
  internal : ℕ
  external : ℕ
  graph : Incidence r p internal external
  edge : (Fin internal ⊕ Fin external) ≃ Fin P.length
  ends_eq : ∀ e b, graph.ends (e,b) = pairEndpoint P (edge e,b)

/-- Every complete partner list gives a genuine bijection between the two
ends of its pairs and all the distinct interaction/probe occurrences. -/
theorem pair_endpoint_bijective {r p k : ℕ} {P : List (EndPosition r p × EndPosition r p)}
    (hP : P ∈ matchings k (sourcePositions r p)) : Function.Bijective (pairEndpoint P) := by
  classical
  have hperm := matching_endpoints_perm hP
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  constructor
  · intro x
    have hx := hperm.mem_iff.mpr (source_positions_all x)
    obtain ⟨⟨i,j⟩,hp,h⟩ := List.mem_flatMap.mp hx
    obtain ⟨e,he⟩ := List.mem_iff_get.mp hp
    rcases (show x = i ∨ x = j by simpa using h) with rfl | rfl
    · exact ⟨(e,0),congrArg Prod.fst he⟩
    · exact ⟨(e,1),congrArg Prod.snd he⟩
  · simpa only [Fintype.card_prod,Fintype.card_fin,endpoints_length,source_positions_length] using hperm.length_eq

/-- Split the edges by their actual ends. Each exterior edge selects an
actual probe end, so the fixed-mode labels come from this same Wick graph. -/
def realizeMatching {r p k : ℕ} {P : List (EndPosition r p × EndPosition r p)}
    (hP : P ∈ matchings k (sourcePositions r p)) : Realization P := by
  classical
  let pos := Equiv.ofBijective (pairEndpoint P) (pair_endpoint_bijective hP)
  let inside (i : Fin P.length) := ∀ b, isInteraction (pos (i,b)) = true
  let I := {i : Fin P.length // inside i}
  let J := {i : Fin P.length // ¬inside i}
  let edge := (Equiv.sumCongr (Fintype.equivFin I).symm (Fintype.equivFin J).symm).trans (Equiv.sumCompl inside)
  let ends := (Equiv.prodCongr edge (Equiv.refl (Fin 2))).trans pos
  have internal (i : Fin (Fintype.card I)) (b : Fin 2) :
      isInteraction (ends (.inl i,b)) = true := ((Fintype.equivFin I).symm i).property b
  have external (j : Fin (Fintype.card J)) : ∃ b u, ends (.inr j,b) = Sum.inr u := by
    have h := ((Fintype.equivFin J).symm j).property
    change ¬∀ b, isInteraction (ends (.inr j,b)) = true at h
    push_neg at h
    obtain ⟨b,hb⟩ := h
    cases he : ends (.inr j,b) with
    | inr u => exact ⟨b,u,he⟩
    | inl a => simp [he,isInteraction] at hb
  choose side port hp using external
  exact ⟨_,_,⟨ends,internal,port,side,hp⟩,edge,fun _ _ => rfl⟩

/-- Enumeration and routing have identical multiplicity and line weights
for this occurrence list, before any summation over vertex variables. -/
theorem matching_weight_eq_edges {r p : ℕ} {P : List (EndPosition r p × EndPosition r p)}
    (R : Realization P) (C : EndPosition r p → EndPosition r p → ℝ) :
    matchingWeight C P = ∏ e : Fin R.internal ⊕ Fin R.external,
      C (R.graph.ends (e,0)) (R.graph.ends (e,1)) := by
  let w (i : Fin P.length) := C (P.get i).1 (P.get i).2
  have h : (List.ofFn w) = P.map (fun e => C e.1 e.2) := by
    calc
      List.ofFn w = (List.ofFn P.get).map (fun e => C e.1 e.2) := by rw [List.map_ofFn]; rfl
      _ = _ := congrArg (List.map (fun e => C e.1 e.2)) (List.ofFn_get P)
  calc
    matchingWeight C P = ∏ i, w i := by rw [← List.prod_ofFn, h]; rfl
    _ = ∏ e, w (R.edge e) := (Equiv.prod_comp R.edge w).symm
    _ = _ := by simp [R.ends_eq,pairEndpoint,w]

theorem matching_weight_is_configured_term {n r p : ℕ} {P : List (EndPosition r p × EndPosition r p)}
    (R : Realization P) (B : Fin n → Fin n → Fin n → ℝ) (v : Fin r → VertexChoice n)
    (probes : Fin p → ModeSlot n) (ℓ : ℝ) :
    (∏ z, vertexCoefficient B (v z)) *
      matchingWeight (fun x y => occurrenceCovariance ℓ (assignedOccurrence v probes x) (assignedOccurrence v probes y)) P =
      configuredGraphTerm B R.graph probes ℓ v := by
  rw [matching_weight_eq_edges R]
  rfl

end UV.CurvatureWick
