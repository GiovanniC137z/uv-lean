import UV.ContinueMomentumRoutingSource

/-! Restore the external shell at every transverse mark and identify
the two unit polarizations of an internal Maxwell edge with its two
charged marks. The zero-frequency representation is available only at
six or more insertions. -/

noncomputable section

open Classical Finset MeasureTheory MeasureTheory.Measure UV.SectorPlane

namespace UV

variable {V E J A ι : Type*} [Fintype V] [Fintype E] [Fintype J] [Fintype ι]
variable {L m : ℝ} {G : MomentumNetwork V E} {P : V → NormalChargedSector L} {n : ℕ}

def NormalChargedSector.markDirections (P : NormalChargedSector L) : Fin P.markCount → UnitVector OSFourSpace :=
  match P with
  | .winding _ _ u | .zero _ _ u | .line _ u .. => u

def MomentumMarks.protectedPolarizations (M : MomentumMarks G (fun v => (P v).markCount)) (e : E) : WilsonPhotonPolarizations where
  incoming := (P (G.head e)).markDirections (M.incoming e)
  outgoing := (P (G.tail e)).markDirections (M.outgoing e)

def MomentumExteriorAttachments.photonShell [AddCommGroup A] (B : MomentumExteriorAttachments P J n)
    (j : A →+ OSFourSpace) (L : ℝ) (R : OSFourSpace →L[ℝ] WilsonBallSpace ι) (x : Fin n → A) : ℂ :=
  ∏ i,normalPhotonForm L R (j (B.transfers x (.inl i)))

omit [Fintype V] [Fintype E] in
theorem MomentumExteriorAttachments.shell_le_one [AddCommGroup A] (B : MomentumExteriorAttachments P J n)
    (j : A →+ OSFourSpace) (L : ℝ) (R : OSFourSpace →L[ℝ] WilsonBallSpace ι) (x : Fin n → A) : ‖B.photonShell j L R x‖ ≤ 1 := by
  rw [photonShell,norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => normal_shell_characteristic_le_one _)

omit [Fintype V] [Fintype E] in
theorem MomentumExteriorAttachments.shell_measurable [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableSub₂ A]
    (B : MomentumExteriorAttachments P J n) (j : A →+ OSFourSpace) (hj : Measurable j) (L : ℝ) (R : OSFourSpace →L[ℝ] WilsonBallSpace ι) :
    Measurable (B.photonShell j L R) := Finset.measurable_prod _ fun i _ =>
      (normal_photon_form_continuous L R).measurable.comp (hj.comp (B.transfer_measurable (.inl i)))

omit [Fintype E] in
theorem MomentumExteriorAttachments.dressed_test_integrable [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableSub₂ A] [MeasurableNeg A]
    (B : MomentumExteriorAttachments P J n) (M : MomentumMarks G (fun v => (P v).markCount)) (j : A →+ OSFourSpace)
    (hj : Measurable j) (σ : Measure A) [SigmaFinite σ] (hσ : Integrable (fun k => normalPacketWeight (j k)) σ)
    (L : ℝ) (R : OSFourSpace →L[ℝ] WilsonBallSpace ι) :
    Integrable (fun x : Fin n → A => ‖B.scalar j x * B.photonShell j L R x‖*(B.marked M).externalWeight j x) (Measure.pi fun _ => σ) := by
  let d := (B.marked M).externalWeight j
  have he : Measurable d := (B.marked M).externalWeight_measurable _ hj (B.endpoint_measurable M)
  apply (B.test_integrable M j hj σ hσ).mono' (((B.scalar_measurable j hj).mul (B.shell_measurable j hj L R)).norm.mul he).aestronglyMeasurable
  apply Filter.Eventually.of_forall fun x => ?_
  have hp := ((B.marked M).externalWeight_pos j x).le
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hp),norm_mul]
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) (B.shell_le_one j L R x)) hp

inductive MomentumProtectedComponent (L : ℝ)
  | loop (n : ℕ) (θ : ℝ) (u : Fin (n+1) → UnitVector OSFourSpace)
  | line (r : ℕ) (u : Fin r → UnitVector OSFourSpace) (φ ψ : WilsonPacket) (z z' : Set.Icc 0 L)

/-- At forbidden zero windings the winding representation already has
amplitude zero. At all admitted zero windings the continuous normal
frequency supplies the zero-winding term. -/
def MomentumProtectedComponent.sector (zeroWinding : Bool) : MomentumProtectedComponent L → NormalChargedSector L
  | .loop n θ u => if h : 5 < n+1 ∧ zeroWinding = true then .zero (n+1) h.1 u else .winding n θ u
  | .line r u φ ψ z z' => .line r u φ ψ z z'

theorem momentum_protected_short_zero {n : ℕ} (hn : n+1 ≤ 5) (θ : ℝ) (u : Fin (n+1) → UnitVector OSFourSpace)
    (Δ : OSFourSpace) (s : Fin (n+1) → OSFourSpace) :
    let P := MomentumProtectedComponent.loop (L := L) n θ u
    P.sector true = NormalChargedSector.winding n θ u ∧
      ∀ t, (NormalChargedSector.winding n θ u : NormalChargedSector L).amplitude m 0 Δ s t = 0 := by
  exact ⟨by simp [MomentumProtectedComponent.sector,show ¬5<n+1 by omega],fun _ => by simp [NormalChargedSector.amplitude]⟩

theorem momentum_protected_long_zero {n : ℕ} (hn : 5 < n+1) (θ : ℝ) (u : Fin (n+1) → UnitVector OSFourSpace) :
    (MomentumProtectedComponent.loop (L := L) n θ u).sector true = .zero (n+1) hn u := by
  simp [MomentumProtectedComponent.sector,hn]

theorem momentum_protected_nonzero (n : ℕ) (θ : ℝ) (u : Fin (n+1) → UnitVector OSFourSpace) :
    (MomentumProtectedComponent.loop (L := L) n θ u).sector false = .winding n θ u := by
  simp [MomentumProtectedComponent.sector]

theorem MomentumExteriorAttachments.dressed_continuum {ρ : ℝ} (hm : 0 < m) (hL : 0 < L) (hρ : 0 < ρ)
    (R : OSFourSpace →L[ℝ] WilsonBallSpace ι) (hr : 3 ≤ Module.finrank ℝ (LinearMap.range R.toLinearMap))
    (hG : G.Connected univ) (root : V) (B : MomentumExteriorAttachments P J n) (M : MomentumMarks G (fun v => (P v).markCount))
    (hP : ∀ v,(P v).schwartzEndpoints) :
    let D := B.marked (A := OSFourSpace) M
    let pol := M.protectedPolarizations
    let a := fun x => B.scalar (AddMonoidHom.id OSFourSpace) x*B.photonShell (AddMonoidHom.id _) L R x
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
    (B.endpoint_measurable M) _ _ ((B.scalar_measurable (AddMonoidHom.id _) measurable_id).mul (B.shell_measurable _ measurable_id L R))
    (B.dressed_test_integrable M (AddMonoidHom.id _) measurable_id volume normal_packet_weight_integrable L R) M.protectedPolarizations hP).2

theorem MomentumExteriorAttachments.dressed_torus (b : NormalReciprocalBasis) (hm : 0 < m) (hL : 0 < L)
    (R : OSFourSpace →L[ℝ] WilsonBallSpace ι) (hr : 3 ≤ Module.finrank ℝ (LinearMap.range R.toLinearMap))
    (hG : G.Connected univ) (root : V) (B : MomentumExteriorAttachments P J n) (M : MomentumMarks G (fun v => (P v).markCount))
    (hP : ∀ v,(P v).schwartzEndpoints) :
    let D := B.marked (A := NormalReciprocalLattice b) M
    let pol := M.protectedPolarizations
    let a := fun x => B.scalar (NormalReciprocalLattice b).subtype.toAddMonoidHom x*B.photonShell (NormalReciprocalLattice b).subtype.toAddMonoidHom L R x
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
    (B.endpoint_measurable M) _ _ ((B.scalar_measurable j measurable_subtype_coe).mul (B.shell_measurable j measurable_subtype_coe L R))
    (B.dressed_test_integrable M j measurable_subtype_coe Measure.count (momentum_lattice_weight_count b) L R) M.protectedPolarizations hP).2


def momentumVacuum [AddCommGroup A] (M : MomentumMarks G (fun v => (P v).markCount)) : NormalMarkedGraph G P Unit A where
  marks := M
  external _ _ _ := 0
  endpoint _ _ := 0

omit [Fintype E] in
theorem momentum_vacuum_conserved [AddCommGroup A] (M : MomentumMarks G (fun v => (P v).markCount)) (x : Unit) :
    ∑ v,(momentumVacuum (A := A) M).injection x v = 0 := by
  simp [NormalMarkedGraph.injection,momentumMarkedSources,momentumVacuum,momentum_open_endpoint]

theorem momentum_vacuum_continuum {ρ : ℝ} (hm : 0 < m) (hL : 0 < L) (hρ : 0 < ρ)
    (R : OSFourSpace →L[ℝ] WilsonBallSpace ι) (hr : 3 ≤ Module.finrank ℝ (LinearMap.range R.toLinearMap))
    (hG : G.Connected univ) (root : V) (M : MomentumMarks G (fun v => (P v).markCount))
    :
    let D := momentumVacuum (A := OSFourSpace) M
    let pol := M.protectedPolarizations
    let a := fun _ : Unit => (1:ℂ)
    let χ := normalPhotonForm L R
    ∃ T : Finset E,G.IsSpanningTree T ∧
      let W := normalTestedPhotonWeight a id χ (fun e : MomentumNetwork.Chords T => pol e.val)
        (fun (e : ↥T) z => (pol e.val).hard ρ χ (G.treeRoute T D.injection z e))
      let d := fun v (z : Unit × (MomentumNetwork.Chords T → OSFourSpace)) => (P v).endpointTransfer (D.endpoint z.1 v)
      NormalGraphAbsolute volume ((Measure.dirac ()).prod
        (Measure.pi fun _ : MomentumNetwork.Chords T => (volume : Measure OSFourSpace))) m P
        (fun _ v z => D.shift T z v) d W := by
  obtain ⟨T,_,hT⟩ := G.spanning_tree hG
  refine ⟨T,hT,?_⟩
  exact ((momentumVacuum M).continuum hm hL hρ R hr T hT root (momentum_vacuum_conserved M) (fun _ _ => measurable_const)
    (fun _ => measurable_const) (Measure.dirac ()) _ measurable_const (integrable_const _) M.protectedPolarizations).2

theorem momentum_vacuum_torus (b : NormalReciprocalBasis) (hm : 0 < m) (hL : 0 < L)
    (R : OSFourSpace →L[ℝ] WilsonBallSpace ι) (hr : 3 ≤ Module.finrank ℝ (LinearMap.range R.toLinearMap))
    (hG : G.Connected univ) (root : V) (M : MomentumMarks G (fun v => (P v).markCount))
    (hP : ∀ v,(P v).schwartzEndpoints) :
    let D := momentumVacuum (A := NormalReciprocalLattice b) M
    let pol := M.protectedPolarizations
    let a := fun _ : Unit => (1:ℂ)
    let χ := normalPhotonForm L R
    ∃ T : Finset E,G.IsSpanningTree T ∧
      let W := normalTestedPhotonWeight a (fun k : NormalReciprocalLattice b => (k:OSFourSpace)) χ
        (fun e : MomentumNetwork.Chords T => pol e.val)
        (fun (e : ↥T) z => (pol e.val).maxwell χ (G.treeRoute (A := NormalReciprocalLattice b) T D.injection z e : OSFourSpace))
      let d := fun v (z : Unit × (MomentumNetwork.Chords T → NormalReciprocalLattice b)) =>
        ((P v).endpointTransfer (A := NormalReciprocalLattice b) (D.endpoint z.1 v) : OSFourSpace)
      NormalGraphAbsolute (normalLatticeMeasure b) ((Measure.dirac ()).prod
        (Measure.pi fun _ : MomentumNetwork.Chords T => (Measure.count : Measure (NormalReciprocalLattice b)))) m P
        (fun _ v z i => (D.shift T z v i : OSFourSpace)) d W := by
  obtain ⟨T,_,hT⟩ := G.spanning_tree hG
  refine ⟨T,hT,?_⟩
  exact ((momentumVacuum M).torus b hm hL R hr T hT root (momentum_vacuum_conserved M) (fun _ _ => measurable_const)
    (fun _ => measurable_const) (Measure.dirac ()) _ measurable_const (integrable_const _) M.protectedPolarizations hP).2

end UV
