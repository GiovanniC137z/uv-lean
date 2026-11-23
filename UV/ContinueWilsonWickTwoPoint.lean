import UV.ContinueWilsonTransverseCoefficient
import UV.CurvatureWickMatchings

/-! Finite-order two-point diagrams from Wick partners of labelled photon
occurrences. The two external marks are distinguished and never Wick paired.
Parallel photons, repeated owners and internal self-sewings are allowed. -/

noncomputable section

open Filter UV.SectorPlane
open scoped Topology RealInnerProductSpace

namespace UV

/-- The input of Wick's recurrence consists of the internal marks only. -/
def wilsonWickPartnerLists (p : ℕ) : List (List (Fin p × Fin p)) :=
  CurvatureWick.matchings p (List.ofFn (fun i : Fin p => i))

theorem wilson_labelled_wick_expansion {A : Type*} (p : ℕ) (C : A → A → ℝ) (h : Fin p → A) :
    osWickMoment C p (List.ofFn h) =
      ((wilsonWickPartnerLists p).map (CurvatureWick.matchingWeight (fun i j => C (h i) (h j)))).sum := by
  simpa only [List.map_ofFn,Function.comp_id] using
    CurvatureWick.wick_sum_over_matchings C h p (List.ofFn (fun i : Fin p => i))

theorem wilson_wick_uses_each_mark (p : ℕ) (j : Fin (wilsonWickPartnerLists p).length) :
    let P := (wilsonWickPartnerLists p).get j
    (CurvatureWick.endpoints P).Perm (List.ofFn (fun i : Fin p => i)) ∧ P.length*2 = p := by
  have h := CurvatureWick.matching_endpoints_perm (show (wilsonWickPartnerLists p).get j ∈
    CurvatureWick.matchings p (List.ofFn (fun i : Fin p => i)) from List.get_mem _ _)
  exact ⟨h,by simpa only [CurvatureWick.endpoints_length,List.length_ofFn] using h.length_eq⟩

theorem wilson_marked_component_count {p m : ℕ} {owner : Fin p ⊕ Fin 2 → Option (Fin m)}
    (h : Function.Surjective owner) : m+1 ≤ p+2 := by
  simpa only [Fintype.card_option,Fintype.card_fin,Fintype.card_sum] using Fintype.card_le_of_surjective owner h

/-- A charged component in the connected coefficient carries at least one
of the internal or the two distinguished external photon marks. -/
abbrev WilsonMarkedOwners (p : ℕ) :=
  (m : Fin (p+2)) × {owner : Fin p ⊕ Fin 2 → Option (Fin m.val) // Function.Surjective owner}

abbrev WilsonWickChoice (p : ℕ) := WilsonMarkedOwners p × Fin (wilsonWickPartnerLists p).length

def WilsonWickChoice.pairs {p : ℕ} (x : WilsonWickChoice p) := (wilsonWickPartnerLists p).get x.2

def WilsonWickChoice.src {p : ℕ} (x : WilsonWickChoice p) (e : Fin x.pairs.length) : Option (Fin x.1.1.val) :=
  x.1.2.val (.inl (x.pairs.get e).1)

def WilsonWickChoice.dst {p : ℕ} (x : WilsonWickChoice p) (e : Fin x.pairs.length) : Option (Fin x.1.1.val) :=
  x.1.2.val (.inl (x.pairs.get e).2)

/-- Connectivity uses the actual oriented edge list, and ignores self loops
only in the adjacency relation. They remain edges of the amplitude. -/
def wilsonEdgeGraph {A E : Type*} (src dst : E → A) : SimpleGraph A where
  Adj u v := u ≠ v ∧ ∃ e, (src e = u ∧ dst e = v) ∨ (src e = v ∧ dst e = u)
  symm := by
    rintro u v ⟨h,e,he⟩
    exact ⟨h.symm,e,he.symm⟩
  loopless := fun _ h => h.1 rfl

theorem wilson_edge_graph_covered {E : Type*} {m : ℕ} (s t : E → Option (Fin m)) :
    NetworkOrientationCovers (wilsonEdgeGraph s t) s t := fun _ _ h => h.2

def WilsonWickChoice.without {p : ℕ} (x : WilsonWickChoice p) (j : Fin x.pairs.length) :=
  wilsonEdgeGraph (fun e : {e : Fin x.pairs.length // e ≠ j} => x.src e) (fun e => x.dst e)

def WilsonWickChoice.admitted {p : ℕ} (x : WilsonWickChoice p) : Prop :=
  (wilsonEdgeGraph x.src x.dst).Connected ∧ ∀ j, (x.without j).Connected

abbrev WilsonWickTwoPoint (p : ℕ) := {x : WilsonWickChoice p // x.admitted}

noncomputable instance wilsonWickTwoPointFintype (p : ℕ) : Fintype (WilsonWickTwoPoint p) := by
  classical
  unfold WilsonWickTwoPoint WilsonWickChoice WilsonMarkedOwners
  infer_instance

/-- Every admitted Wick partner list supplies its own conservation basis and
its own edge-deletion witnesses. External momenta attach at their owners. -/
def wilsonWickDiagram {p : ℕ} (a : WilsonWickTwoPoint p) : WilsonTwoPointDiagram := by
  let x := a.val
  let B := (wilson_connected_routing_exists (wilsonEdgeGraph x.src x.dst) x.src x.dst a.property.1
    (wilson_edge_graph_covered x.src x.dst)).some
  exact ⟨x.1.1.val,x.pairs.length,x.src,x.dst,wilsonEdgeGraph x.src x.dst,a.property.1,
    wilson_edge_graph_covered x.src x.dst,B,x.1.2.val (.inr 0),x.1.2.val (.inr 1),
    fun j => x.without j.val,fun j => a.property.2 j.val,
    fun _ => wilson_edge_graph_covered _ _⟩

/-- The sum runs over all marked owners and all entries of the positional
Wick recurrence satisfying connectivity and every single-photon deletion.
Each entry carries its specified fixed coefficient. -/
theorem wilson_wick_transverse_coefficient {ι : Type*} [Fintype ι] (p : ℕ) (c : WilsonWickTwoPoint p → ℂ)
    {L lam : ℝ} (hL : 0 < L) (hlam : 0 ≤ lam) (hl : 2*lam < 1) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (u v : UnitVector OSFourSpace) (huv : ⟪u.val,v.val⟫ = 0)
    (e : OSFourSpace → UnitVector OSFourSpace) (he : ∀ k ≠ 0, ⟪k,(e k).val⟫ = 0) :
    let F := fun k : OSFourSpace => ((‖k‖^2 * wilsonTransverseEntry (e k) (e k) k : ℝ) : ℂ) +
      ∑ i : WilsonWickTwoPoint p, c i * (wilsonWickDiagram i).amplitude L lam T k (e k) (e k)
    Tendsto (fun k : OSFourSpace => F k / (‖k‖^2 : ℝ)) (𝓝[≠] 0)
      (𝓝 (1 + ∑ i : WilsonWickTwoPoint p, c i * (wilsonWickDiagram i).coefficient L lam T u v)) ∧
        Tendsto F (𝓝[≠] 0) (𝓝 0) :=
  wilson_finite_transverse_coefficient wilsonWickDiagram c hL hlam hl T u v huv e he

end UV
