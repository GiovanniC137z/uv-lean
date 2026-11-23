import UV.ContinueMomentumRoutingExternal

/-! Kirchhoff-routed protected graphs with jointly tested external
fermion and photon momenta. Closed sectors have external weight one. -/

noncomputable section

open Classical Finset MeasureTheory MeasureTheory.Measure UV.SectorPlane

namespace UV

variable {V E Y A ι : Type*} [Fintype V] [Fintype E] [MeasurableSpace Y]
variable {L m : ℝ} {G : MomentumNetwork V E} {P : V → NormalChargedSector L}

def NormalMarkedGraph.externalWeight [AddCommGroup A] (D : NormalMarkedGraph G P Y A) (ι : A → OSFourSpace) (y : Y) :=
  ∏ v,(P v).externalWeight (ι ((P v).endpointTransfer (D.endpoint y v)))

omit [Fintype E] [MeasurableSpace Y] in
theorem NormalMarkedGraph.externalWeight_pos [AddCommGroup A] (D : NormalMarkedGraph G P Y A) (ι : A → OSFourSpace) (y : Y) :
    0 < D.externalWeight ι y := Finset.prod_pos fun v _ => (P v).externalWeight_pos _

private theorem momentum_endpoint_measurable [AddCommGroup A] [MeasurableSpace A] (P : NormalChargedSector L)
    {f : Y → A} (h : Measurable f) : Measurable (fun y => P.endpointTransfer (f y)) := by
  cases P <;> first | exact measurable_const | exact h

omit [Fintype E] in
theorem NormalMarkedGraph.externalWeight_measurable [AddCommGroup A] [MeasurableSpace A]
    (D : NormalMarkedGraph G P Y A) (ι : A → OSFourSpace) (hι : Measurable ι) (hd : ∀ v, Measurable (D.endpoint · v)) :
    Measurable (D.externalWeight ι) :=
  Finset.measurable_prod _ (fun v _ => (P v).externalWeight_measurable.comp (hι.comp (momentum_endpoint_measurable (P v) (hd v))))

theorem NormalMarkedGraph.tested [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableSub₂ A]
    (hm : 0 < m) (hL : 0 < L) (σ : Measure OSFourSpace) [SigmaFinite σ] (hσ : Integrable normalPacketWeight σ)
    (hP : ∀ v,(P v).schwartzEndpoints) (hU : ∀ v,(P v).uniformBudget m σ) (j : A → OSFourSpace) (hj : Measurable j)
    (T : Finset E) (hT : G.IsSpanningTree T) (root : V) (D : NormalMarkedGraph G P Y A)
    (hc : ∀ y, ∑ v,D.injection y v = 0) (hx : ∀ v i, Measurable (fun y => D.external y v i)) (hd : ∀ v,Measurable (D.endpoint · v))
    (μ : Measure Y) (ν : Measure (Y × (MomentumNetwork.Chords T → A))) [SFinite ν] (a : Y → ℂ) (hma : Measurable a)
    (ha : Integrable (fun y => ‖a y‖*D.externalWeight j y) μ) (K : Y × (MomentumNetwork.Chords T → A) → ℂ)
    (hK : ∀ f : Y → ℂ, Measurable f → Integrable f μ →
      Measurable (fun z : Y × (MomentumNetwork.Chords T → A) => f z.1*K z) ∧
        Integrable (fun z : Y × (MomentumNetwork.Chords T → A) => f z.1*K z) ν) :
    (∀ z : Y × (MomentumNetwork.Chords T → A), G.boundary univ (G.route T (D.injection z.1) z.2) = D.injection z.1) ∧
    NormalGraphAbsolute σ ν m P (fun _ v z i => j (D.shift T z v i))
      (fun v z => j ((P v).endpointTransfer (D.endpoint z.1 v))) (fun z => a z.1*K z) := by
  obtain ⟨hW,hJ⟩ := momentum_external_photons μ ν a hma (D.externalWeight j)
    (D.externalWeight_measurable j hj hd) (D.externalWeight_pos j) ha K hK
  refine ⟨fun z => G.route_conserved hT root _ (hc z.1) z.2,?_⟩
  exact momentum_sector_tested_graph hm hL σ hσ P hP hU _
    (fun _ v i => hj.comp (D.shift_measurable T hx hd v i)) _
    (fun v => hj.comp ((momentum_endpoint_measurable (P v) (hd v)).comp measurable_fst)) ν _ hW hJ

variable [Fintype ι]

theorem NormalMarkedGraph.continuum_tested {ρ : ℝ} (hm : 0 < m) (hL : 0 < L) (hρ : 0 < ρ)
    (R : OSFourSpace →L[ℝ] WilsonBallSpace ι) (hr : 3 ≤ Module.finrank ℝ (LinearMap.range R.toLinearMap))
    (T : Finset E) (hT : G.IsSpanningTree T) (root : V) (D : NormalMarkedGraph G P Y OSFourSpace)
    (hc : ∀ y, ∑ v,D.injection y v = 0) (hx : ∀ v i, Measurable (fun y => D.external y v i))
    (hd : ∀ v, Measurable (D.endpoint · v)) (μ : Measure Y) [SFinite μ] (a : Y → ℂ) (hma : Measurable a)
    (ha : Integrable (fun y => ‖a y‖*D.externalWeight id y) μ)
    (pol : E → WilsonPhotonPolarizations) (hP : ∀ v,(P v).schwartzEndpoints) :
    let χ := normalPhotonForm L R
    let W := normalTestedPhotonWeight a id χ (fun e : MomentumNetwork.Chords T => pol e.val)
      (fun (e : ↥T) z => (pol e.val).hard ρ χ (G.treeRoute T D.injection z e))
    let d := fun v (z : Y × (MomentumNetwork.Chords T → OSFourSpace)) => (P v).endpointTransfer (D.endpoint z.1 v)
    (∀ z : Y × (MomentumNetwork.Chords T → OSFourSpace), G.boundary univ (G.route T (D.injection z.1) z.2) = D.injection z.1) ∧
    NormalGraphAbsolute volume (μ.prod (Measure.pi fun _ : MomentumNetwork.Chords T => (volume : Measure OSFourSpace))) m P
      (fun _ v z => D.shift T z v) d W := by
  apply D.tested hm hL volume normal_packet_weight_integrable hP (fun v => (P v).volume_uniformBudget hm hL) id measurable_id
    T hT root hc hx hd μ _ a hma ha
  intro f hf hif
  exact normal_continuum_tested_photons hL hρ R hr μ f hf hif _ _ _ (G.treeRoute_measurable T _ (D.injection_measurable hx hd))

theorem NormalMarkedGraph.torus_tested (b : NormalReciprocalBasis) (hm : 0 < m) (hL : 0 < L)
    (R : OSFourSpace →L[ℝ] WilsonBallSpace ι) (hr : 3 ≤ Module.finrank ℝ (LinearMap.range R.toLinearMap))
    (T : Finset E) (hT : G.IsSpanningTree T) (root : V) (D : NormalMarkedGraph G P Y (NormalReciprocalLattice b))
    (hc : ∀ y, ∑ v,D.injection y v = 0) (hx : ∀ v i, Measurable (fun y => D.external y v i))
    (hd : ∀ v, Measurable (D.endpoint · v)) (μ : Measure Y) [SFinite μ] (a : Y → ℂ) (hma : Measurable a)
    (ha : Integrable (fun y => ‖a y‖*D.externalWeight (fun k : NormalReciprocalLattice b => (k:OSFourSpace)) y) μ)
    (pol : E → WilsonPhotonPolarizations) (hP : ∀ v,(P v).schwartzEndpoints) :
    let χ := normalPhotonForm L R
    let W := normalTestedPhotonWeight a (fun k : NormalReciprocalLattice b => (k:OSFourSpace)) χ (fun e : MomentumNetwork.Chords T => pol e.val)
      (fun (e : ↥T) z => (pol e.val).maxwell χ (G.treeRoute (A := NormalReciprocalLattice b) T D.injection z e : OSFourSpace))
    let d := fun v (z : Y × (MomentumNetwork.Chords T → NormalReciprocalLattice b)) =>
      ((P v).endpointTransfer (A := NormalReciprocalLattice b) (D.endpoint z.1 v) : OSFourSpace)
    (∀ z : Y × (MomentumNetwork.Chords T → NormalReciprocalLattice b), G.boundary univ (G.route T (D.injection z.1) z.2) = D.injection z.1) ∧
    NormalGraphAbsolute (normalLatticeMeasure b) (μ.prod (Measure.pi fun _ : MomentumNetwork.Chords T => (Measure.count : Measure (NormalReciprocalLattice b))))
      m P (fun _ v z i => (D.shift T z v i : OSFourSpace)) d W := by
  apply D.tested hm hL (normalLatticeMeasure b) (momentum_lattice_weight b) hP (fun v => (P v).lattice_uniformBudget b hm hL (hP v))
    _ measurable_subtype_coe T hT root hc hx hd μ _ a hma ha
  intro f hf hif
  exact normal_torus_tested_photons b hL R hr μ f hf hif _ _ _ (G.treeRoute_measurable T _ (D.injection_measurable hx hd))

end UV
