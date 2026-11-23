import UV.ContinueCompressedGraph
import UV.ContinueCompressedModesShell

/-! The transverse photon readout is the restriction of the same five-
dimensional isometry used on the charged legs. The hard continuum and
full reciprocal lattice estimates retain independent circle modes. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure UV.SectorPlane
namespace UV

def compressedCarrierInclusion : OSFourSpace →ₗᵢ[ℝ] NormalBall 5 where
  toFun := normalBallJoin 0
  map_add' x y := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [normalBallJoin]
  map_smul' c x := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [normalBallJoin]
  norm_map' x := by
    change ‖normalBallJoin 0 x‖ = ‖x‖
    have h := normal_ball_join_norm 0 x
    nlinarith [norm_nonneg x,norm_nonneg (normalBallJoin 0 x)]

variable {ι C D Y V : Type*} [Fintype ι] [Fintype C] [Fintype D] [MeasurableSpace Y] [Fintype V]

def compressedPhotonReadout (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) := (T.comp compressedCarrierInclusion).toContinuousLinearMap

theorem compressed_photon_rank (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) :
    Module.finrank ℝ (LinearMap.range (compressedPhotonReadout T).toLinearMap) = 4 :=
  (LinearMap.finrank_range_of_inj (T.comp compressedCarrierInclusion).injective).trans (finrank_euclideanSpace_fin ..)

theorem compressed_photon_actual (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (L : ℝ) (Q : OSFourSpace) :
    normalPhotonForm L (compressedPhotonReadout T) Q = (normalLegForm L T 0 Q : ℂ) :=
  (normal_shell_characteristic_real _).symm

theorem compressed_continuum_graph {m L ρ : ℝ} (hm : 0 < m) (hL : 0 < L) (hρ : 0 < ρ)
    (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (θ : ℝ) (μ : Measure Y) [SFinite μ] (A : Y → ℂ)
    (hmA : Measurable A) (hiA : Integrable A μ) (chord : C → WilsonPhotonPolarizations) (tree : D → WilsonPhotonPolarizations)
    (route : Y × (C → OSFourSpace) → D → OSFourSpace) (hr : ∀ e, Measurable (route · e)) (P : V → CompressedPiece)
    (s : (V → ℤ) → (v : V) → Y × (C → OSFourSpace) → Fin (P v).length → OSFourSpace) (hs : ∀ j v i, Measurable (s j v · i))
    (Δ : V → Y × (C → OSFourSpace) → OSFourSpace) (hΔ : ∀ v, Measurable (Δ v)) :
    let χ := normalPhotonForm L (compressedPhotonReadout T)
    let W := normalTestedPhotonWeight A id χ chord (fun e z => (tree e).hard ρ χ (route z e))
    CompressedGraphAbsolute volume (μ.prod (Measure.pi fun _ : C => (volume : Measure OSFourSpace))) m L θ T P s Δ W := by
  have hp := normal_continuum_tested_photons hL hρ (compressedPhotonReadout T) (by rw [compressed_photon_rank]; decide) μ A hmA hiA chord tree route hr
  exact compressed_graph_integral hm hL T θ volume (fun _ u => compressed_loop_volume_budget hm hL T u) P
    (fun v => (P v).volume_endpoints) s hs Δ hΔ _ _ hp.1 hp.2

theorem compressed_torus_graph (b : NormalReciprocalBasis) {m L : ℝ} (hm : 0 < m) (hL : 0 < L)
    (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (θ : ℝ) (μ : Measure Y) [SFinite μ] (A : Y → ℂ)
    (hmA : Measurable A) (hiA : Integrable A μ) (chord : C → WilsonPhotonPolarizations) (tree : D → WilsonPhotonPolarizations)
    (route : Y × (C → NormalReciprocalLattice b) → D → NormalReciprocalLattice b) (hr : ∀ e, Measurable (route · e))
    (P : V → CompressedPiece) (hP : ∀ v, (P v).schwartzEndpoints)
    (s : (V → ℤ) → (v : V) → Y × (C → NormalReciprocalLattice b) → Fin (P v).length → OSFourSpace) (hs : ∀ j v i, Measurable (s j v · i))
    (Δ : V → Y × (C → NormalReciprocalLattice b) → OSFourSpace) (hΔ : ∀ v, Measurable (Δ v)) :
    let χ := normalPhotonForm L (compressedPhotonReadout T)
    let W := normalTestedPhotonWeight A (fun k : NormalReciprocalLattice b => (k:OSFourSpace)) χ chord
      (fun e z => (tree e).maxwell χ (route z e))
    CompressedGraphAbsolute (normalLatticeMeasure b) (μ.prod (Measure.pi fun _ : C => (Measure.count : Measure (NormalReciprocalLattice b))))
      m L θ T P s Δ W := by
  have hp := normal_torus_tested_photons b hL (compressedPhotonReadout T) (by rw [compressed_photon_rank]; decide) μ A hmA hiA chord tree route hr
  exact compressed_graph_integral hm hL T θ (normalLatticeMeasure b) (fun _ u => compressed_loop_lattice_budget b hm hL T u) P
    (fun v => (P v).lattice_endpoints b (hP v)) s hs Δ hΔ _ _ hp.1 hp.2

end UV
