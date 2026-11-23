import UV.ContinueMomentumRoutingMarks

/-! Labelled contracted photon graphs for the protected normal-circle
comparison. Kirchhoff routing and the ordered charged translations are
constructed before the continuum or reciprocal-lattice estimate. -/

noncomputable section

open Classical Finset MeasureTheory MeasureTheory.Measure UV.SectorPlane

namespace UV

variable {V E A Y ι : Type*} [Fintype V] [Fintype E] [AddCommGroup A] (G : MomentumNetwork V E)

def MomentumNetwork.treeRoute (T : Finset E) (b : Y → V → A) (z : Y × (MomentumNetwork.Chords T → A)) (e : ↥T) : A :=
  G.route T (b z.1) z.2 e.val

theorem MomentumNetwork.treeRoute_measurable [MeasurableSpace Y] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableSub₂ A]
    (T : Finset E) (b : Y → V → A) (hb : ∀ v, Measurable (b · v)) (e : ↥T) :
    Measurable (G.treeRoute T b · e) :=
  G.route_measurable T (fun v => (hb v).comp measurable_fst) (fun f => (measurable_pi_apply f).comp measurable_snd) e.val

variable {L : ℝ}

def NormalChargedSector.markCount : NormalChargedSector L → ℕ
  | .winding n .. => n+1
  | .zero r .. => r
  | .line r .. => r

/-- Running momentum on the propagator before its mark. Open paths have
one final propagator from the last mark to the outgoing endpoint. -/
def NormalChargedSector.segmentPosition (P : NormalChargedSector L) : Fin P.segments → Fin (P.markCount+1) := by
  cases P with
  | winding n => exact Fin.castSucc
  | zero r => exact Fin.castSucc
  | line r => exact id

def NormalChargedSector.endpointTransfer (P : NormalChargedSector L) (d : A) : A :=
  match P with
  | .line .. => d
  | _ => 0

/-- The external data at charged marks exclude the internal photon
edges, which are supplied exactly once at each of their labelled ends. -/
structure NormalMarkedGraph (G : MomentumNetwork V E) (P : V → NormalChargedSector L) (Y A : Type*) where
  marks : MomentumMarks G (fun v => (P v).markCount)
  external : Y → (v : V) → Fin (P v).markCount → A
  endpoint : Y → V → A

variable {G} {P : V → NormalChargedSector L} (D : NormalMarkedGraph G P Y A)

def NormalMarkedGraph.injection (y : Y) : V → A := momentumMarkedSources (D.external y) (fun v => (P v).endpointTransfer (D.endpoint y v))

def NormalMarkedGraph.shift (T : Finset E) (z : Y × (MomentumNetwork.Chords T → A)) (v : V) (i : Fin (P v).segments) : A :=
  D.marks.translation G (G.route T (D.injection z.1) z.2) (D.external z.1) v ((P v).segmentPosition i)

theorem NormalMarkedGraph.endpoint_equation {T : Finset E} (hT : G.IsSpanningTree T) (root : V)
    (hs : ∀ y, ∑ v, D.injection y v = 0) (z : Y × (MomentumNetwork.Chords T → A)) (v : V) (k : A) :
    k+D.marks.translation G (G.route T (D.injection z.1) z.2) (D.external z.1) v (Fin.last (P v).markCount) =
      k+(P v).endpointTransfer (D.endpoint z.1 v) :=
  D.marks.routed_endpoint G hT root (D.external z.1) _ (hs z.1) z.2 v k

variable [MeasurableSpace Y]

omit [Fintype V] [Fintype E] in
theorem NormalMarkedGraph.injection_measurable [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableSub₂ A]
    (hx : ∀ v j, Measurable (fun y => D.external y v j)) (hd : ∀ v, Measurable (D.endpoint · v)) (v : V) :
    Measurable (D.injection · v) := by
  apply (Finset.measurable_sum _ (fun i _ => hx v i)).sub
  change Measurable (fun y => (P v).endpointTransfer (D.endpoint y v))
  cases P v <;> first | exact measurable_const | exact hd v

theorem NormalMarkedGraph.shift_measurable [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableSub₂ A]
    (T : Finset E) (hx : ∀ v j, Measurable (fun y => D.external y v j)) (hd : ∀ v, Measurable (D.endpoint · v))
    (v : V) (j : Fin (P v).segments) : Measurable (fun z => D.shift T z v j) :=
  D.marks.translation_measurable G (fun e => G.route_measurable T
    (fun v => (D.injection_measurable hx hd v).comp measurable_fst) (fun f => (measurable_pi_apply f).comp measurable_snd) e)
    (fun v i => (hx v i).comp measurable_fst) v _

private theorem normal_marked_endpoint_measurable {P : NormalChargedSector L} [MeasurableSpace A]
    (f : Y → A) (hf : Measurable f) : Measurable (fun y => P.endpointTransfer (f y)) := by
  cases P <;> first | exact measurable_const | exact hf

variable [Fintype ι]

/-- The charged shifts and every dependent photon momentum are computed
from the marked graph; only the labelled chords are independently integrated. -/
theorem NormalMarkedGraph.continuum {m ρ : ℝ} (hm : 0 < m) (hL : 0 < L) (hρ : 0 < ρ)
    (R : OSFourSpace →L[ℝ] WilsonBallSpace ι) (hr : 3 ≤ Module.finrank ℝ (LinearMap.range R.toLinearMap))
    (T : Finset E) (hT : G.IsSpanningTree T) (root : V) (D : NormalMarkedGraph G P Y OSFourSpace)
    (hc : ∀ y, ∑ v, D.injection y v = 0) (hx : ∀ v j, Measurable (fun y => D.external y v j))
    (hd : ∀ v, Measurable (D.endpoint · v)) (μ : Measure Y) [SFinite μ] (a : Y → ℂ) (hma : Measurable a) (ha : Integrable a μ)
    (pol : E → WilsonPhotonPolarizations) :
    let χ := normalPhotonForm L R
    let W := normalTestedPhotonWeight a id χ (fun e : MomentumNetwork.Chords T => pol e.val)
      (fun (e : ↥T) z => (pol e.val).hard ρ χ (G.treeRoute T D.injection z e))
    let d := fun v (z : Y × (MomentumNetwork.Chords T → OSFourSpace)) => (P v).endpointTransfer (D.endpoint z.1 v)
    (∀ z : Y × (MomentumNetwork.Chords T → OSFourSpace), G.boundary univ (G.route T (D.injection z.1) z.2) = D.injection z.1) ∧
    NormalGraphAbsolute volume (μ.prod (Measure.pi fun _ : MomentumNetwork.Chords T => (volume : Measure OSFourSpace))) m P
      (fun _ v z => D.shift T z v) d W := by
  refine ⟨fun z => G.route_conserved hT root _ (hc z.1) z.2,?_⟩
  exact normal_rank_continuum_graph hm hL hρ R hr μ a hma ha _ _ _ (G.treeRoute_measurable T _ (D.injection_measurable hx hd))
    P _ (fun _ => D.shift_measurable T hx hd) _ (fun v => (normal_marked_endpoint_measurable (P := P v) _ (hd v)).comp measurable_fst)

theorem NormalMarkedGraph.torus (b : NormalReciprocalBasis) {m : ℝ} (hm : 0 < m) (hL : 0 < L)
    (R : OSFourSpace →L[ℝ] WilsonBallSpace ι) (hr : 3 ≤ Module.finrank ℝ (LinearMap.range R.toLinearMap))
    (T : Finset E) (hT : G.IsSpanningTree T) (root : V) (D : NormalMarkedGraph G P Y (NormalReciprocalLattice b))
    (hc : ∀ y, ∑ v, D.injection y v = 0) (hx : ∀ v j, Measurable (fun y => D.external y v j))
    (hd : ∀ v, Measurable (D.endpoint · v)) (μ : Measure Y) [SFinite μ] (a : Y → ℂ) (hma : Measurable a) (ha : Integrable a μ)
    (pol : E → WilsonPhotonPolarizations) (hP : ∀ v, (P v).schwartzEndpoints) :
    let χ := normalPhotonForm L R
    let W := normalTestedPhotonWeight a (fun k : NormalReciprocalLattice b => (k:OSFourSpace)) χ (fun e : MomentumNetwork.Chords T => pol e.val)
      (fun (e : ↥T) z => (pol e.val).maxwell χ (G.treeRoute (A := NormalReciprocalLattice b) T D.injection z e : OSFourSpace))
    let d := fun v (z : Y × (MomentumNetwork.Chords T → NormalReciprocalLattice b)) =>
      ((P v).endpointTransfer (A := NormalReciprocalLattice b) (D.endpoint z.1 v) : OSFourSpace)
    (∀ z : Y × (MomentumNetwork.Chords T → NormalReciprocalLattice b), G.boundary univ (G.route T (D.injection z.1) z.2) = D.injection z.1) ∧
    NormalGraphAbsolute (normalLatticeMeasure b) (μ.prod (Measure.pi fun _ : MomentumNetwork.Chords T => (Measure.count : Measure (NormalReciprocalLattice b))))
      m P (fun _ v z j => (D.shift T z v j : OSFourSpace)) d W := by
  refine ⟨fun z => G.route_conserved hT root _ (hc z.1) z.2,?_⟩
  exact normal_rank_torus_graph b hm hL R hr μ a hma ha _ _ _ (G.treeRoute_measurable T _ (D.injection_measurable hx hd))
    P hP _ (fun _ v j => measurable_subtype_coe.comp (D.shift_measurable T hx hd v j)) _
    (fun v => measurable_subtype_coe.comp ((normal_marked_endpoint_measurable (P := P v) _ (hd v)).comp measurable_fst))

end UV
