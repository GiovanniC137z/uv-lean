import UV.ContinueCompressedWeighted
import UV.ContinueMomentumRoutingExternal

/-! Joint photon and charged integrals with freely varying conserved external
transfers. The external norm includes a Schwartz transfer weight for each
open charged path; a connected routing may eliminate any one external leg. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure UV.SectorPlane
namespace UV
variable {ι C D Y V : Type*} [Fintype ι] [Fintype C] [Fintype D] [MeasurableSpace Y] [Fintype V]

theorem compressed_continuum_external {m L ρ : ℝ} (hm : 0 < m) (hL : 0 < L) (hρ : 0 < ρ)
    (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (θ : ℝ) (μ : Measure Y) [SFinite μ] (A : Y → ℂ)
    (hmA : Measurable A) (chord : C → WilsonPhotonPolarizations) (tree : D → WilsonPhotonPolarizations)
    (route : Y × (C → OSFourSpace) → D → OSFourSpace) (hr : ∀ e, Measurable (route · e)) (P : V → CompressedPiece) (hP : ∀ v, (P v).schwartzEndpoints)
    (s : (V → ℤ) → (v : V) → Y × (C → OSFourSpace) → Fin (P v).length → OSFourSpace) (hs : ∀ j v i, Measurable (s j v · i))
    (Δ : V → Y → OSFourSpace) (hΔ : ∀ v, Measurable (Δ v))
    (hext : Integrable (fun y => ‖A y‖*∏ v,(P v).transferWeight (Δ v y)) μ) :
    let χ := normalPhotonForm L (compressedPhotonReadout T)
    let W := normalTestedPhotonWeight A id χ chord (fun e z => (tree e).hard ρ χ (route z e))
    CompressedGraphAbsolute volume (μ.prod (Measure.pi fun _ : C => (volume : Measure OSFourSpace))) m L θ T P s (fun v z => Δ v z.1) W := by
  let e := fun y => ∏ v,(P v).transferWeight (Δ v y)
  have he : Measurable e := Finset.measurable_prod _ (fun v _ => (P v).transferWeight_continuous.measurable.comp (hΔ v))
  let χ := normalPhotonForm L (compressedPhotonReadout T)
  let K := fun (z : Y × (C → OSFourSpace)) => (((∏ i,(chord i).maxwell χ (z.2 i)) * ∏ d, (tree d).hard ρ χ (route z d) : ℝ) : ℂ)
  have hp := momentum_external_photons μ (μ.prod (Measure.pi fun _ : C => (volume : Measure OSFourSpace))) A hmA e he
    (fun y => Finset.prod_pos fun v _ => (P v).transferWeight_pos _) hext K (fun f hmf hif => by
    exact normal_continuum_tested_photons hL hρ (compressedPhotonReadout T) (by rw [compressed_photon_rank]; decide) μ f hmf hif chord tree route hr)
  exact compressed_weighted_graph hm hL T θ volume (fun _ u => compressed_loop_volume_budget hm hL T u) normal_packet_weight_integrable P hP s hs _ (fun v => (hΔ v).comp measurable_fst)
    _ _ hp.1 hp.2

theorem compressed_torus_external (b : NormalReciprocalBasis) {m L : ℝ} (hm : 0 < m) (hL : 0 < L)
    (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (θ : ℝ) (μ : Measure Y) [SFinite μ] (A : Y → ℂ)
    (hmA : Measurable A) (chord : C → WilsonPhotonPolarizations) (tree : D → WilsonPhotonPolarizations)
    (route : Y × (C → NormalReciprocalLattice b) → D → NormalReciprocalLattice b) (hr : ∀ e, Measurable (route · e))
    (P : V → CompressedPiece) (hP : ∀ v, (P v).schwartzEndpoints)
    (s : (V → ℤ) → (v : V) → Y × (C → NormalReciprocalLattice b) → Fin (P v).length → OSFourSpace) (hs : ∀ j v i, Measurable (s j v · i))
    (Δ : V → Y → OSFourSpace) (hΔ : ∀ v, Measurable (Δ v))
    (hext : Integrable (fun y => ‖A y‖*∏ v,(P v).transferWeight (Δ v y)) μ) :
    let χ := normalPhotonForm L (compressedPhotonReadout T)
    let W := normalTestedPhotonWeight A (fun k : NormalReciprocalLattice b => (k:OSFourSpace)) χ chord
      (fun e z => (tree e).maxwell χ (route z e))
    CompressedGraphAbsolute (normalLatticeMeasure b) (μ.prod (Measure.pi fun _ : C => (Measure.count : Measure (NormalReciprocalLattice b))))
      m L θ T P s (fun v z => Δ v z.1) W := by
  let e := fun y => ∏ v,(P v).transferWeight (Δ v y)
  have he : Measurable e := Finset.measurable_prod _ (fun v _ => (P v).transferWeight_continuous.measurable.comp (hΔ v))
  let χ := normalPhotonForm L (compressedPhotonReadout T)
  let K := fun (z : Y × (C → NormalReciprocalLattice b)) => (((∏ i,(chord i).maxwell χ ((z.2 i : OSFourSpace))) * ∏ d, (tree d).maxwell χ (route z d) : ℝ) : ℂ)
  have hp := momentum_external_photons μ (μ.prod (Measure.pi fun _ : C => (Measure.count : Measure (NormalReciprocalLattice b)))) A hmA e he
    (fun y => Finset.prod_pos fun v _ => (P v).transferWeight_pos _) hext K (fun f hmf hif => by
    exact normal_torus_tested_photons b hL (compressedPhotonReadout T) (by rw [compressed_photon_rank]; decide) μ f hmf hif chord tree route hr)
  exact compressed_weighted_graph hm hL T θ (normalLatticeMeasure b) (fun _ u => compressed_loop_lattice_budget b hm hL T u) (momentum_lattice_weight b) P hP s hs _ (fun v => (hΔ v).comp measurable_fst)
    _ _ hp.1 hp.2

end UV
