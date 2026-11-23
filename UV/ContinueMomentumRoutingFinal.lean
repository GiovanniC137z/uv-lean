import UV.ContinueMomentumRoutingWinding

/-! The continuum and full-torus signed estimates for the first-order
transverse comparison. Tree momenta and the normal-winding choices
are solved internally before taking the joint absolute sum. -/

noncomputable section

open Classical Finset MeasureTheory MeasureTheory.Measure UV.SectorPlane

namespace UV

variable {V E J A Y ι : Type*} [Fintype V] [Fintype E] [Fintype J] [Fintype ι]
variable [AddCommGroup A] [MeasurableSpace A] [MeasurableSpace Y]
variable {L m : ℝ} {G : MomentumNetwork V E} {n : ℕ}

abbrev MomentumProtectedComponent.family (S : V → MomentumProtectedComponent L) (b : V → Bool) (v : V) := (S v).sector (b v)

def momentumSelectedAbsolute {U : (V → Bool) → Type*} [∀ b,MeasurableSpace (U b)] (S : V → MomentumProtectedComponent L)
    (σ : Measure OSFourSpace) (μ : ∀ b,Measure (U b)) (m : ℝ)
    (s : (b : V → Bool) → (V → ℤ) → (v : V) → U b → Fin ((MomentumProtectedComponent.family S b v).segments) → OSFourSpace)
    (d : (b : V → Bool) → V → U b → OSFourSpace) (W : (b : V → Bool) → U b → ℂ) (c : ℂ) : Prop :=
  let pick := fun (w : V → ℤ) v => decide (w v = 0)
  let F := fun w => normalGraphTerm m (MomentumProtectedComponent.family S (pick w)) (s (pick w)) (d (pick w)) (W (pick w)) w
  let ν := fun w => normalGraphMeasure σ (MomentumProtectedComponent.family S (pick w)) (μ (pick w))
  let H := fun w t => (c*momentumPhysicalPhase S w)*F w t
  (∀ w,Integrable (H w) (ν w)) ∧ Summable (fun w => ∫ t,‖H w t‖ ∂ν w)

def momentumProtectedGraph (S : V → MomentumProtectedComponent L) (σ : Measure OSFourSpace) (μ : Measure Y) (ν : Measure A)
    (j : A →+ OSFourSpace) (χ : OSFourSpace → ℂ) (H : WilsonPhotonPolarizations → OSFourSpace → ℝ)
    (D : ∀ b,NormalMarkedGraph G (MomentumProtectedComponent.family S b) Y A) (a : (V → Bool) → Y → ℂ)
    (T : (V → Bool) → Finset E) (m : ℝ) (c : ℂ) : Prop :=
  let pol := fun b => (D b).marks.protectedPolarizations
  let W := fun b => normalTestedPhotonWeight (a b) j χ (fun e : MomentumNetwork.Chords (T b) => pol b e.val)
    (fun (e : ↥(T b)) z => H (pol b e.val) (j (G.treeRoute (T b) (D b).injection z e)))
  let d := fun b v (z : Y × (MomentumNetwork.Chords (T b) → A)) => j ((MomentumProtectedComponent.family S b v).endpointTransfer ((D b).endpoint z.1 v))
  momentumSelectedAbsolute S σ (fun b => μ.prod (Measure.pi fun _ : MomentumNetwork.Chords (T b) => ν)) m
    (fun b _ v z i => j ((D b).shift (T b) z v i)) d W c

theorem momentum_protected_continuum {ρ : ℝ} (hm : 0 < m) (hL : 0 < L) (hρ : 0 < ρ)
    (R : OSFourSpace →L[ℝ] WilsonBallSpace ι) (hr : 3 ≤ Module.finrank ℝ (LinearMap.range R.toLinearMap)) (hG : G.Connected univ) (root : V)
    (S : V → MomentumProtectedComponent L) (B : ∀ b,MomentumExteriorAttachments (MomentumProtectedComponent.family S b) J n)
    (M : ∀ b,MomentumMarks G (fun v => (MomentumProtectedComponent.family S b v).markCount))
    (hP : ∀ b v,(MomentumProtectedComponent.family S b v).schwartzEndpoints) (c : ℂ) :
    let j := AddMonoidHom.id OSFourSpace
    let χ := normalPhotonForm L R
    ∃ T : (V → Bool) → Finset E,(∀ b,G.IsSpanningTree (T b)) ∧
      momentumProtectedGraph S volume (Measure.pi fun _ : Fin n => (volume : Measure OSFourSpace)) volume j χ (fun e => e.hard ρ χ)
        (fun b => (B b).marked (M b)) (fun b x => (B b).scalar j x*(B b).photonShell j L R x) T m c := by
  choose T hT h using fun b => (B b).dressed_continuum hm hL hρ R hr hG root (M b) (hP b)
  exact ⟨T,hT,momentum_selected_physical_graph S volume _ _ _ _ h c⟩

theorem momentum_protected_torus (lattice : NormalReciprocalBasis) (hm : 0 < m) (hL : 0 < L)
    (R : OSFourSpace →L[ℝ] WilsonBallSpace ι) (hr : 3 ≤ Module.finrank ℝ (LinearMap.range R.toLinearMap)) (hG : G.Connected univ) (root : V)
    (S : V → MomentumProtectedComponent L) (B : ∀ b,MomentumExteriorAttachments (MomentumProtectedComponent.family S b) J n)
    (M : ∀ b,MomentumMarks G (fun v => (MomentumProtectedComponent.family S b v).markCount))
    (hP : ∀ b v,(MomentumProtectedComponent.family S b v).schwartzEndpoints) (c : ℂ) :
    let j := (NormalReciprocalLattice lattice).subtype.toAddMonoidHom
    let χ := normalPhotonForm L R
    ∃ T : (V → Bool) → Finset E,(∀ b,G.IsSpanningTree (T b)) ∧
      momentumProtectedGraph S (normalLatticeMeasure lattice) (Measure.pi fun _ : Fin n => (Measure.count : Measure (NormalReciprocalLattice lattice))) Measure.count j χ
        (fun e => e.maxwell χ) (fun b => (B b).marked (M b)) (fun b x => (B b).scalar j x*(B b).photonShell j L R x) T m c := by
  choose T hT h using fun b => (B b).dressed_torus lattice hm hL R hr hG root (M b) (hP b)
  exact ⟨T,hT,momentum_selected_physical_graph S (normalLatticeMeasure lattice) _ _ _ _ h c⟩

theorem momentum_protected_vacuum_continuum {ρ : ℝ} (hm : 0 < m) (hL : 0 < L) (hρ : 0 < ρ)
    (R : OSFourSpace →L[ℝ] WilsonBallSpace ι) (hr : 3 ≤ Module.finrank ℝ (LinearMap.range R.toLinearMap)) (hG : G.Connected univ) (root : V)
    (S : V → MomentumProtectedComponent L) (M : ∀ b,MomentumMarks G (fun v => (MomentumProtectedComponent.family S b v).markCount)) (c : ℂ) :
    let χ := normalPhotonForm L R
    ∃ T : (V → Bool) → Finset E,(∀ b,G.IsSpanningTree (T b)) ∧
      momentumProtectedGraph S volume (Measure.dirac ()) volume (AddMonoidHom.id _) χ (fun e => e.hard ρ χ)
        (fun b => momentumVacuum (M b)) (fun _ _ => 1) T m c := by
  choose T hT h using fun b => momentum_vacuum_continuum hm hL hρ R hr hG root (M b)
  exact ⟨T,hT,momentum_selected_physical_graph S volume _ _ _ _ h c⟩

theorem momentum_protected_vacuum_torus (lattice : NormalReciprocalBasis) (hm : 0 < m) (hL : 0 < L)
    (R : OSFourSpace →L[ℝ] WilsonBallSpace ι) (hr : 3 ≤ Module.finrank ℝ (LinearMap.range R.toLinearMap)) (hG : G.Connected univ) (root : V)
    (S : V → MomentumProtectedComponent L) (M : ∀ b,MomentumMarks G (fun v => (MomentumProtectedComponent.family S b v).markCount))
    (hP : ∀ b v,(MomentumProtectedComponent.family S b v).schwartzEndpoints) (c : ℂ) :
    let χ := normalPhotonForm L R
    ∃ T : (V → Bool) → Finset E,(∀ b,G.IsSpanningTree (T b)) ∧
      momentumProtectedGraph S (normalLatticeMeasure lattice) (Measure.dirac ()) Measure.count (NormalReciprocalLattice lattice).subtype.toAddMonoidHom χ (fun e => e.maxwell χ)
        (fun b => momentumVacuum (M b)) (fun _ _ => 1) T m c := by
  choose T hT h using fun b => momentum_vacuum_torus lattice hm hL R hr hG root (M b) (hP b)
  exact ⟨T,hT,momentum_selected_physical_graph S (normalLatticeMeasure lattice) _ _ _ _ h c⟩

end UV
