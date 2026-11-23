import UV.ContinueMomentumRoutingAttachments
import UV.ContinueWilsonWickTwoPoint

/-! Every connected labelled Wick contraction of internal photon marks
has a momentum routing. Independent external transfer measures are the
full product measures after solving the single overall constraint. -/

noncomputable section

open Classical Finset MeasureTheory MeasureTheory.Measure UV.SectorPlane

namespace UV

variable {V E J ι : Type*} [Fintype V] [Fintype E] [Fintype J] [Fintype ι]
variable {L m : ℝ} {G : MomentumNetwork V E} {P : V → NormalChargedSector L} {n : ℕ}

def momentumWickNetwork {r : V → ℕ} {k : ℕ} (loc : Fin k → (v : V) × Fin (r v)) (j : Fin (wilsonWickPartnerLists k).length) :
    MomentumNetwork V (Fin ((wilsonWickPartnerLists k).get j).length) where
  tail e := (loc (((wilsonWickPartnerLists k).get j).get e).1).1
  head e := (loc (((wilsonWickPartnerLists k).get j).get e).2).1

def momentumWickMarks {r : V → ℕ} {k : ℕ} (loc : Fin k → (v : V) × Fin (r v)) (j : Fin (wilsonWickPartnerLists k).length) :
    MomentumMarks (momentumWickNetwork loc j) r where
  outgoing e := (loc (((wilsonWickPartnerLists k).get j).get e).1).2
  incoming e := (loc (((wilsonWickPartnerLists k).get j).get e).2).2

omit [Fintype V] in
theorem momentum_wick_endpoints {r : V → ℕ} {k : ℕ} (loc : Fin k → (v : V) × Fin (r v)) (j : Fin (wilsonWickPartnerLists k).length) :
    ((CurvatureWick.endpoints ((wilsonWickPartnerLists k).get j)).map loc).Perm (List.ofFn loc) ∧
      ((wilsonWickPartnerLists k).get j).length*2=k := by
  obtain ⟨h,hk⟩ := wilson_wick_uses_each_mark k j
  exact ⟨by simpa using h.map loc,hk⟩

theorem MomentumExteriorAttachments.continuum {ρ : ℝ} (hm : 0 < m) (hL : 0 < L) (hρ : 0 < ρ)
    (R : OSFourSpace →L[ℝ] WilsonBallSpace ι) (hr : 3 ≤ Module.finrank ℝ (LinearMap.range R.toLinearMap))
    (hG : G.Connected univ) (root : V) (B : MomentumExteriorAttachments P J n) (M : MomentumMarks G (fun v => (P v).markCount))
    (pol : E → WilsonPhotonPolarizations) (hP : ∀ v,(P v).schwartzEndpoints) :
    let D := B.marked (A := OSFourSpace) M
    let a := B.scalar (AddMonoidHom.id OSFourSpace)
    let χ := normalPhotonForm L R
    ∃ T : Finset E,G.IsSpanningTree T ∧
      let W := normalTestedPhotonWeight a id χ (fun e : MomentumNetwork.Chords T => pol e.val)
        (fun (e : ↥T) z => (pol e.val).hard ρ χ (G.treeRoute T D.injection z e))
      let d := fun v (z : (Fin n → OSFourSpace) × (MomentumNetwork.Chords T → OSFourSpace)) => (P v).endpointTransfer (D.endpoint z.1 v)
      NormalGraphAbsolute volume ((Measure.pi fun _ : Fin n => (volume : Measure OSFourSpace)).prod
        (Measure.pi fun _ : MomentumNetwork.Chords T => (volume : Measure OSFourSpace))) m P
        (fun _ v z => D.shift T z v) d W := by
  obtain ⟨T,_,hT⟩ := G.spanning_tree hG
  refine ⟨T,hT,?_⟩
  exact ((B.marked M).continuum_tested hm hL hρ R hr T hT root (B.conserved M) (B.external_measurable M)
    (B.endpoint_measurable M) _ _ (B.scalar_measurable (AddMonoidHom.id _) measurable_id)
    (B.test_integrable M (AddMonoidHom.id _) measurable_id volume normal_packet_weight_integrable) pol hP).2

theorem MomentumExteriorAttachments.torus (b : NormalReciprocalBasis) (hm : 0 < m) (hL : 0 < L)
    (R : OSFourSpace →L[ℝ] WilsonBallSpace ι) (hr : 3 ≤ Module.finrank ℝ (LinearMap.range R.toLinearMap))
    (hG : G.Connected univ) (root : V) (B : MomentumExteriorAttachments P J n) (M : MomentumMarks G (fun v => (P v).markCount))
    (pol : E → WilsonPhotonPolarizations) (hP : ∀ v,(P v).schwartzEndpoints) :
    let D := B.marked (A := NormalReciprocalLattice b) M
    let a := B.scalar (NormalReciprocalLattice b).subtype.toAddMonoidHom
    let χ := normalPhotonForm L R
    ∃ T : Finset E,G.IsSpanningTree T ∧
      let W := normalTestedPhotonWeight a (fun k : NormalReciprocalLattice b => (k:OSFourSpace)) χ
        (fun e : MomentumNetwork.Chords T => pol e.val)
        (fun (e : ↥T) z => (pol e.val).maxwell χ (G.treeRoute (A := NormalReciprocalLattice b) T D.injection z e : OSFourSpace))
      let d := fun v (z : (Fin n → NormalReciprocalLattice b) × (MomentumNetwork.Chords T → NormalReciprocalLattice b)) =>
        ((P v).endpointTransfer (A := NormalReciprocalLattice b) (D.endpoint z.1 v) : OSFourSpace)
      NormalGraphAbsolute (normalLatticeMeasure b) ((Measure.pi fun _ : Fin n => (Measure.count : Measure (NormalReciprocalLattice b))).prod
        (Measure.pi fun _ : MomentumNetwork.Chords T => (Measure.count : Measure (NormalReciprocalLattice b)))) m P
        (fun _ v z i => (D.shift T z v i : OSFourSpace)) d W := by
  obtain ⟨T,_,hT⟩ := G.spanning_tree hG
  refine ⟨T,hT,?_⟩
  let j := (NormalReciprocalLattice b).subtype.toAddMonoidHom
  exact ((B.marked M).torus_tested b hm hL R hr T hT root (B.conserved M) (B.external_measurable M)
    (B.endpoint_measurable M) _ _ (B.scalar_measurable j measurable_subtype_coe)
    (B.test_integrable M j measurable_subtype_coe Measure.count (momentum_lattice_weight_count b)) pol hP).2

end UV
