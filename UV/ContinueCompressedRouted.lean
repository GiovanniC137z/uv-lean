import UV.ContinueMomentumRoutingGraph
import UV.ContinueCompressedGraphBounds

/-! Actual marked momentum routes for connected graphs of the three-compression
operator. Each photon end contributes its signed momentum at its charged
insertion. The running translations close each cycle and give the prescribed
transfer on an open path. -/

noncomputable section
open Classical Finset MeasureTheory MeasureTheory.Measure UV.SectorPlane
namespace UV
variable {V E A Y ι : Type*} [Fintype V] [Fintype E] [AddCommGroup A] (G : MomentumNetwork V E)

def CompressedPiece.markCount : CompressedPiece → ℕ
  | .loop n .. | .path n .. => n+1

/-- Running momentum on the propagator before its mark. Open paths have
one final propagator from the last mark to the outgoing endpoint. -/
def CompressedPiece.segmentPosition (P : CompressedPiece) : Fin P.length → Fin (P.markCount+1) := by
  cases P with
  | loop n => exact Fin.castSucc
  | path n => exact id

def CompressedPiece.endpointTransfer (P : CompressedPiece) (d : A) : A :=
  match P with
  | .path .. => d
  | _ => 0

/-- The external data at charged marks exclude the internal photon
edges, which are supplied exactly once at each of their labelled ends. -/
structure CompressedMarkedGraph (G : MomentumNetwork V E) (P : V → CompressedPiece) (Y A : Type*) where
  marks : MomentumMarks G (fun v => (P v).markCount)
  external : Y → (v : V) → Fin (P v).markCount → A
  endpoint : Y → V → A

variable {G} {P : V → CompressedPiece} (D : CompressedMarkedGraph G P Y A)

def CompressedMarkedGraph.injection (y : Y) : V → A := momentumMarkedSources (D.external y) (fun v => (P v).endpointTransfer (D.endpoint y v))

def CompressedMarkedGraph.shift (T : Finset E) (z : Y × (MomentumNetwork.Chords T → A)) (v : V) (i : Fin (P v).length) : A :=
  D.marks.translation G (G.route T (D.injection z.1) z.2) (D.external z.1) v ((P v).segmentPosition i)

theorem CompressedMarkedGraph.endpoint_equation {T : Finset E} (hT : G.IsSpanningTree T) (root : V)
    (hs : ∀ y, ∑ v, D.injection y v = 0) (z : Y × (MomentumNetwork.Chords T → A)) (v : V) (k : A) :
    k+D.marks.translation G (G.route T (D.injection z.1) z.2) (D.external z.1) v (Fin.last (P v).markCount) =
      k+(P v).endpointTransfer (D.endpoint z.1 v) :=
  D.marks.routed_endpoint G hT root (D.external z.1) _ (hs z.1) z.2 v k

variable [MeasurableSpace Y]

omit [Fintype V] [Fintype E] in
theorem CompressedMarkedGraph.injection_measurable [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableSub₂ A]
    (hx : ∀ v j, Measurable (fun y => D.external y v j)) (hd : ∀ v, Measurable (D.endpoint · v)) (v : V) :
    Measurable (D.injection · v) := by
  apply (Finset.measurable_sum _ (fun i _ => hx v i)).sub
  change Measurable (fun y => (P v).endpointTransfer (D.endpoint y v))
  cases P v <;> first | exact measurable_const | exact hd v

theorem CompressedMarkedGraph.shift_measurable [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableSub₂ A]
    (T : Finset E) (hx : ∀ v j, Measurable (fun y => D.external y v j)) (hd : ∀ v, Measurable (D.endpoint · v))
    (v : V) (j : Fin (P v).length) : Measurable (fun z => D.shift T z v j) :=
  D.marks.translation_measurable G (fun e => G.route_measurable T
    (fun v => (D.injection_measurable hx hd v).comp measurable_fst) (fun f => (measurable_pi_apply f).comp measurable_snd) e)
    (fun v i => (hx v i).comp measurable_fst) v _

private theorem compressed_marked_endpoint_measurable {P : CompressedPiece} [MeasurableSpace A]
    (f : Y → A) (hf : Measurable f) : Measurable (fun y => P.endpointTransfer (f y)) := by
  cases P <;> first | exact measurable_const | exact hf

variable [Fintype ι] {L : ℝ}

/-- The charged shifts and every dependent photon momentum are computed
from the marked graph; only the labelled chords are independently integrated. -/
theorem CompressedMarkedGraph.continuum {m ρ : ℝ} (hm : 0 < m) (hL : 0 < L) (hρ : 0 < ρ)
    (S : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (θ : ℝ)
    (T : Finset E) (hT : G.IsSpanningTree T) (root : V) (D : CompressedMarkedGraph G P Y OSFourSpace)
    (hc : ∀ y, ∑ v, D.injection y v = 0) (hx : ∀ v j, Measurable (fun y => D.external y v j))
    (hd : ∀ v, Measurable (D.endpoint · v)) (μ : Measure Y) [SFinite μ] (a : Y → ℂ) (hma : Measurable a) (ha : Integrable a μ)
    (pol : E → WilsonPhotonPolarizations) :
    let χ := normalPhotonForm L (compressedPhotonReadout S)
    let W := normalTestedPhotonWeight a id χ (fun e : MomentumNetwork.Chords T => pol e.val)
      (fun (e : ↥T) z => (pol e.val).hard ρ χ (G.treeRoute T D.injection z e))
    let d := fun v (z : Y × (MomentumNetwork.Chords T → OSFourSpace)) => (P v).endpointTransfer (D.endpoint z.1 v)
    (∀ z : Y × (MomentumNetwork.Chords T → OSFourSpace), G.boundary univ (G.route T (D.injection z.1) z.2) = D.injection z.1) ∧
    CompressedGraphAbsolute volume (μ.prod (Measure.pi fun _ : MomentumNetwork.Chords T => (volume : Measure OSFourSpace))) m L θ S P
      (fun _ v z => D.shift T z v) d W := by
  refine ⟨fun z => G.route_conserved hT root _ (hc z.1) z.2,?_⟩
  exact compressed_continuum_graph hm hL hρ S θ μ a hma ha _ _ _ (G.treeRoute_measurable T _ (D.injection_measurable hx hd))
    P _ (fun _ => D.shift_measurable T hx hd) _ (fun v => (compressed_marked_endpoint_measurable (P := P v) _ (hd v)).comp measurable_fst)

theorem CompressedMarkedGraph.torus (b : NormalReciprocalBasis) {m : ℝ} (hm : 0 < m) (hL : 0 < L)
    (S : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (θ : ℝ)
    (T : Finset E) (hT : G.IsSpanningTree T) (root : V) (D : CompressedMarkedGraph G P Y (NormalReciprocalLattice b))
    (hc : ∀ y, ∑ v, D.injection y v = 0) (hx : ∀ v j, Measurable (fun y => D.external y v j))
    (hd : ∀ v, Measurable (D.endpoint · v)) (μ : Measure Y) [SFinite μ] (a : Y → ℂ) (hma : Measurable a) (ha : Integrable a μ)
    (pol : E → WilsonPhotonPolarizations) (hP : ∀ v, (P v).schwartzEndpoints) :
    let χ := normalPhotonForm L (compressedPhotonReadout S)
    let W := normalTestedPhotonWeight a (fun k : NormalReciprocalLattice b => (k:OSFourSpace)) χ (fun e : MomentumNetwork.Chords T => pol e.val)
      (fun (e : ↥T) z => (pol e.val).maxwell χ (G.treeRoute (A := NormalReciprocalLattice b) T D.injection z e : OSFourSpace))
    let d := fun v (z : Y × (MomentumNetwork.Chords T → NormalReciprocalLattice b)) =>
      ((P v).endpointTransfer (A := NormalReciprocalLattice b) (D.endpoint z.1 v) : OSFourSpace)
    (∀ z : Y × (MomentumNetwork.Chords T → NormalReciprocalLattice b), G.boundary univ (G.route T (D.injection z.1) z.2) = D.injection z.1) ∧
    CompressedGraphAbsolute (normalLatticeMeasure b) (μ.prod (Measure.pi fun _ : MomentumNetwork.Chords T => (Measure.count : Measure (NormalReciprocalLattice b))))
      m L θ S P (fun _ v z j => (D.shift T z v j : OSFourSpace)) d W := by
  refine ⟨fun z => G.route_conserved hT root _ (hc z.1) z.2,?_⟩
  exact compressed_torus_graph b hm hL S θ μ a hma ha _ _ _ (G.treeRoute_measurable T _ (D.injection_measurable hx hd))
    P hP _ (fun _ v j => measurable_subtype_coe.comp (D.shift_measurable T hx hd v j)) _
    (fun v => measurable_subtype_coe.comp ((compressed_marked_endpoint_measurable (P := P v) _ (hd v)).comp measurable_fst))

end UV
