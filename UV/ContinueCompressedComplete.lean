import UV.ContinueCompressedExterior
import UV.ContinueMomentumRoutingAttachments

/-! Labelled connected diagrams with all external Schwartz probes integrated.
The shared routing data record only the number of charged segments and
whether a component has endpoints. The integrands below use the affine
three-compression propagators and the unrestricted normal mode sum. -/

noncomputable section
open Classical Finset MeasureTheory MeasureTheory.Measure Set UV.SectorPlane
namespace UV

/-- Reuse the incidence and external-test construction on the same oriented
paths and cycles. Normal coordinates do not enter this combinatorial map. -/
def CompressedPiece.routingShape : CompressedPiece → NormalChargedSector 0
  | .loop n u => .winding n 0 u
  | .path n u φ ψ => .line (n+1) u φ ψ ⟨0,le_rfl,le_rfl⟩ ⟨0,le_rfl,le_rfl⟩

theorem CompressedPiece.routing_segments (P : CompressedPiece) : P.routingShape.segments = P.length := by cases P <;> rfl

theorem CompressedPiece.routing_weight (P : CompressedPiece) (k : OSFourSpace) : P.routingShape.externalWeight k = P.transferWeight k := by cases P <;> rfl

private theorem compressed_shape_endpoint_measurable {Y A : Type*} [MeasurableSpace Y] [AddCommGroup A] [MeasurableSpace A]
    (P : CompressedPiece) (f : Y → A) (hf : Measurable f) : Measurable (fun y => P.routingShape.endpointTransfer (f y)) := by
  cases P <;> first | exact measurable_const | exact hf

variable {V E J ι : Type*} [Fintype V] [Fintype E] [Fintype J] [Fintype ι] {P : V → CompressedPiece} {G : MomentumNetwork V E}
  {m L : ℝ} {n : ℕ}

set_option maxHeartbeats 800000 in
theorem compressed_complete_continuum {ρ : ℝ} (hm : 0 < m) (hL : 0 < L) (hρ : 0 < ρ)
    (S : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (θ : ℝ)
    (hG : G.Connected univ) (root : V) (B : MomentumExteriorAttachments (fun v => (P v).routingShape) J n) (M : MomentumMarks G (fun v => (P v).routingShape.markCount))
    (pol : E → WilsonPhotonPolarizations) (hP : ∀ v,(P v).schwartzEndpoints) :
    let D := B.marked (A := OSFourSpace) M
    let a := B.scalar (AddMonoidHom.id OSFourSpace)
    let χ := normalPhotonForm L (compressedPhotonReadout S)
    ∃ T : Finset E,G.IsSpanningTree T ∧
      (∀ z : (Fin n → OSFourSpace) × (MomentumNetwork.Chords T → OSFourSpace), G.boundary univ (G.route T (D.injection z.1) z.2) = D.injection z.1) ∧
      let W := normalTestedPhotonWeight a id χ (fun e : MomentumNetwork.Chords T => pol e.val)
        (fun (e : ↥T) z => (pol e.val).hard ρ χ (G.treeRoute T D.injection z e))
      let d := fun v (z : (Fin n → OSFourSpace) × (MomentumNetwork.Chords T → OSFourSpace)) => (P v).routingShape.endpointTransfer (D.endpoint z.1 v)
      CompressedGraphAbsolute volume ((Measure.pi fun _ : Fin n => (volume : Measure OSFourSpace)).prod
        (Measure.pi fun _ : MomentumNetwork.Chords T => (volume : Measure OSFourSpace))) m L θ S P
        (fun _ v z i => D.shift T z v (Fin.cast (P v).routing_segments.symm i)) d W := by
  dsimp only
  obtain ⟨T,_,hT⟩ := G.spanning_tree hG
  refine ⟨T,hT,fun z => G.route_conserved hT root _ (B.conserved M z.1) z.2,?_⟩
  let D := B.marked (A := OSFourSpace) M
  let j := (AddMonoidHom.id OSFourSpace)
  have hu := D.injection_measurable (B.external_measurable M) (B.endpoint_measurable M)
  have hs := D.shift_measurable T (B.external_measurable M) (B.endpoint_measurable M)
  have hd (v : V) : Measurable (fun y : Fin n → OSFourSpace => j ((P v).routingShape.endpointTransfer (D.endpoint y v))) :=
    measurable_id.comp (compressed_shape_endpoint_measurable (P v) _ (B.endpoint_measurable M v))
  have he := B.test_integrable M j measurable_id volume normal_packet_weight_integrable
  simp only [NormalMarkedGraph.externalWeight,CompressedPiece.routing_weight] at he
  exact compressed_continuum_external hm hL hρ S θ (Measure.pi fun _ : Fin n => (volume : Measure (OSFourSpace))) (B.scalar j)
    (B.scalar_measurable j measurable_id) (fun e : MomentumNetwork.Chords T => pol e.val) (fun e : ↥T => pol e.val)
    (G.treeRoute T D.injection) (G.treeRoute_measurable T D.injection hu) P hP
    (fun _ v z i => j (D.shift T z v (Fin.cast (P v).routing_segments.symm i))) (fun _ v i => measurable_id.comp (hs v (Fin.cast (P v).routing_segments.symm i)))
    (fun v y => j ((P v).routingShape.endpointTransfer (D.endpoint y v))) hd he

set_option maxHeartbeats 800000 in
theorem compressed_complete_torus (b : NormalReciprocalBasis) (hm : 0 < m) (hL : 0 < L)
    (S : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (θ : ℝ)
    (hG : G.Connected univ) (root : V) (B : MomentumExteriorAttachments (fun v => (P v).routingShape) J n) (M : MomentumMarks G (fun v => (P v).routingShape.markCount))
    (pol : E → WilsonPhotonPolarizations) (hP : ∀ v,(P v).schwartzEndpoints) :
    let D := B.marked (A := NormalReciprocalLattice b) M
    let a := B.scalar (NormalReciprocalLattice b).subtype.toAddMonoidHom
    let χ := normalPhotonForm L (compressedPhotonReadout S)
    ∃ T : Finset E,G.IsSpanningTree T ∧
      (∀ z : (Fin n → NormalReciprocalLattice b) × (MomentumNetwork.Chords T → NormalReciprocalLattice b), G.boundary univ (G.route T (D.injection z.1) z.2) = D.injection z.1) ∧
      let W := normalTestedPhotonWeight a (fun k : NormalReciprocalLattice b => (k:OSFourSpace)) χ
        (fun e : MomentumNetwork.Chords T => pol e.val)
        (fun (e : ↥T) z => (pol e.val).maxwell χ (G.treeRoute (A := NormalReciprocalLattice b) T D.injection z e : OSFourSpace))
      let d := fun v (z : (Fin n → NormalReciprocalLattice b) × (MomentumNetwork.Chords T → NormalReciprocalLattice b)) =>
        ((P v).routingShape.endpointTransfer (A := NormalReciprocalLattice b) (D.endpoint z.1 v) : OSFourSpace)
      CompressedGraphAbsolute (normalLatticeMeasure b) ((Measure.pi fun _ : Fin n => (Measure.count : Measure (NormalReciprocalLattice b))).prod
        (Measure.pi fun _ : MomentumNetwork.Chords T => (Measure.count : Measure (NormalReciprocalLattice b)))) m L θ S P
        (fun _ v z i => (D.shift T z v (Fin.cast (P v).routing_segments.symm i) : OSFourSpace)) d W := by
  dsimp only
  obtain ⟨T,_,hT⟩ := G.spanning_tree hG
  refine ⟨T,hT,fun z => G.route_conserved hT root _ (B.conserved M z.1) z.2,?_⟩
  let D := B.marked (A := NormalReciprocalLattice b) M
  let j := (NormalReciprocalLattice b).subtype.toAddMonoidHom
  have hu := D.injection_measurable (B.external_measurable M) (B.endpoint_measurable M)
  have hs := D.shift_measurable T (B.external_measurable M) (B.endpoint_measurable M)
  have hd (v : V) : Measurable (fun y : Fin n → NormalReciprocalLattice b => j ((P v).routingShape.endpointTransfer (D.endpoint y v))) :=
    measurable_subtype_coe.comp (compressed_shape_endpoint_measurable (P v) _ (B.endpoint_measurable M v))
  have he := B.test_integrable M j measurable_subtype_coe Measure.count (momentum_lattice_weight_count b)
  simp only [NormalMarkedGraph.externalWeight,CompressedPiece.routing_weight] at he
  exact compressed_torus_external b hm hL S θ (Measure.pi fun _ : Fin n => (Measure.count : Measure (NormalReciprocalLattice b))) (B.scalar j)
    (B.scalar_measurable j measurable_subtype_coe) (fun e : MomentumNetwork.Chords T => pol e.val) (fun e : ↥T => pol e.val)
    (G.treeRoute T D.injection) (G.treeRoute_measurable T D.injection hu) P hP
    (fun _ v z i => j (D.shift T z v (Fin.cast (P v).routing_segments.symm i))) (fun _ v i => measurable_subtype_coe.comp (hs v (Fin.cast (P v).routing_segments.symm i)))
    (fun v y => j ((P v).routingShape.endpointTransfer (D.endpoint y v))) hd he

end UV
