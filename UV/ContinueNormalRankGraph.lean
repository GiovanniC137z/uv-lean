import UV.ContinueNormalRoutedPhotons

/-! The joint graph estimate for the compressed normal-circle operator
in every linear readout of rank at least three. All loop, chord and
external integrations appear before taking the absolute winding sum. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter UV.SectorPlane

namespace UV

variable {V Y M C D ι : Type*} [Fintype V] [MeasurableSpace Y] [MeasurableSpace M]
  [Fintype C] [Fintype D] [Fintype ι]

def normalGraphTerm {Z : Type*} {L : ℝ} (m : ℝ) (P : V → NormalChargedSector L)
    (s : (V → ℤ) → (v : V) → Z → Fin (P v).segments → OSFourSpace)
    (Δ : V → Z → OSFourSpace) (W : Z → ℂ) (w : V → ℤ) :=
  wilsonJointFactors W (fun v q => (P v).amplitude m (w v) (Δ v q) (s w v q))

def normalGraphMeasure {Z : Type*} [MeasurableSpace Z] {L : ℝ} (σ : Measure OSFourSpace)
    (P : V → NormalChargedSector L) (μ : Measure Z) :=
  μ.prod (Measure.pi (fun v => (P v).measure σ))

def NormalGraphAbsolute {Z : Type*} [MeasurableSpace Z] {L : ℝ} (σ : Measure OSFourSpace) (μ : Measure Z)
    (m : ℝ) (P : V → NormalChargedSector L) (s : (V → ℤ) → (v : V) → Z → Fin (P v).segments → OSFourSpace)
    (Δ : V → Z → OSFourSpace) (W : Z → ℂ) : Prop :=
  let G := normalGraphTerm m P s Δ W
  let ν := normalGraphMeasure σ P μ
  (∀ w, Integrable (G w) ν) ∧ Summable (fun w => ∫ t, ‖G w t‖ ∂ν)

/-- Continuum photon chords are massless. Dependent photon momenta use
the specified positive infrared scale. External tests are integrated jointly. -/
theorem normal_rank_continuum_graph {m L ρ : ℝ} (hm : 0 < m) (hL : 0 < L) (hρ : 0 < ρ)
    (T : OSFourSpace →L[ℝ] WilsonBallSpace ι) (hr : 3 ≤ Module.finrank ℝ (LinearMap.range T.toLinearMap))
    (μ : Measure Y) [SFinite μ] (A : Y → ℂ) (hmA : Measurable A) (hiA : Integrable A μ)
    (chord : C → WilsonPhotonPolarizations) (tree : D → WilsonPhotonPolarizations)
    (route : Y × (C → OSFourSpace) → D → OSFourSpace) (hroute : ∀ e, Measurable (route · e))
    (P : V → NormalChargedSector L) (s : (V → ℤ) → (v : V) → Y × (C → OSFourSpace) → Fin (P v).segments → OSFourSpace)
    (hs : ∀ w v j, Measurable (s w v · j)) (Δ : V → Y × (C → OSFourSpace) → OSFourSpace) (hΔ : ∀ v, Measurable (Δ v)) :
    let χ := normalPhotonForm L T
    let W := normalTestedPhotonWeight A id χ chord (fun e z => (tree e).hard ρ χ (route z e))
    NormalGraphAbsolute volume (μ.prod (Measure.pi fun _ : C => (volume : Measure OSFourSpace))) m P s Δ W := by
  have h := normal_continuum_tested_photons hL hρ T hr μ A hmA hiA chord tree route hroute
  simpa only [NormalGraphAbsolute,normalGraphMeasure,normalGraphTerm,NormalChargedSector.measure_volume] using
    normal_protected_graph_integral hm hL P s hs Δ hΔ _ h.1 h.2

/-- Every nonzero reciprocal photon mode is retained in both chords and
tree edges. The zero mode has been fixed in the transverse covariance. -/
theorem normal_rank_torus_graph (b : NormalReciprocalBasis) {m L : ℝ} (hm : 0 < m) (hL : 0 < L)
    (T : OSFourSpace →L[ℝ] WilsonBallSpace ι) (hr : 3 ≤ Module.finrank ℝ (LinearMap.range T.toLinearMap))
    (μ : Measure Y) [SFinite μ] (A : Y → ℂ) (hmA : Measurable A) (hiA : Integrable A μ)
    (chord : C → WilsonPhotonPolarizations) (tree : D → WilsonPhotonPolarizations)
    (route : Y × (C → NormalReciprocalLattice b) → D → NormalReciprocalLattice b) (hroute : ∀ e, Measurable (route · e))
    (P : V → NormalChargedSector L) (hP : ∀ v, (P v).schwartzEndpoints)
    (s : (V → ℤ) → (v : V) → Y × (C → NormalReciprocalLattice b) → Fin (P v).segments → OSFourSpace)
    (hs : ∀ w v j, Measurable (s w v · j)) (Δ : V → Y × (C → NormalReciprocalLattice b) → OSFourSpace)
    (hΔ : ∀ v, Measurable (Δ v)) :
    let χ := normalPhotonForm L T
    let W := normalTestedPhotonWeight A (fun k : NormalReciprocalLattice b => (k:OSFourSpace)) χ chord
      (fun e z => (tree e).maxwell χ (route z e))
    NormalGraphAbsolute (normalLatticeMeasure b) (μ.prod (Measure.pi fun _ : C => (Measure.count : Measure (NormalReciprocalLattice b))))
      m P s Δ W := by
  have h := normal_torus_tested_photons b hL T hr μ A hmA hiA chord tree route hroute
  exact normal_lattice_protected_graph_integral b hm hL P hP s hs Δ hΔ _ h.1 h.2

/-- Picking a winding representation for each component can vary with the
entire winding assignment. A finite partition preserves absolute summability
even when its displacement and frequency integrals live in different spaces. -/
theorem normal_finite_winding_partition {I K : Type*} [Fintype I] (g : I → K → ℝ)
    (hn : ∀ i k, 0 ≤ g i k) (hs : ∀ i, Summable (g i)) (pick : K → I) :
    Summable (fun k => g (pick k) k) := by
  classical
  apply Summable.of_nonneg_of_le (fun k => hn _ k) _ (summable_sum (s := Finset.univ) (fun i _ => hs i))
  intro k
  exact Finset.single_le_sum (fun i _ => hn i k) (Finset.mem_univ (pick k))

/-- The zero/nonzero mask of the independent windings selects the actual
sector for each closed component. Open components may use the same line
in both choices. Any unit-modulus holonomy multiplier can be reinstated. -/
theorem normal_graph_all_windings {Z : Type*} [MeasurableSpace Z] {L : ℝ} (σ : Measure OSFourSpace) (μ : Measure Z)
    (m : ℝ) (P : (V → Bool) → V → NormalChargedSector L)
    (s : (b : V → Bool) → (V → ℤ) → (v : V) → Z → Fin (P b v).segments → OSFourSpace)
    (Δ : V → Z → OSFourSpace) (W : Z → ℂ) (h : ∀ b, NormalGraphAbsolute σ μ m (P b) (s b) Δ W)
    (phase : (b : V → Bool) → (w : V → ℤ) → Z × ((v : V) → (P b v).Variables) → ℂ)
    (hm : ∀ b w, Measurable (phase b w)) (hp : ∀ b w t, ‖phase b w t‖ ≤ 1) :
    let mask := fun (w : V → ℤ) (v : V) => decide (w v = 0)
    let G := fun w t => phase (mask w) w t * normalGraphTerm m (P (mask w)) (s (mask w)) Δ W w t
    let ν := fun w => normalGraphMeasure σ (P (mask w)) μ
    (∀ w, Integrable (G w) (ν w)) ∧ Summable (fun w => ∫ t, ‖G w t‖ ∂ν w) := by
  classical
  let mask := fun (w : V → ℤ) (v : V) => decide (w v = 0)
  let f := fun (b : V → Bool) => normalGraphTerm m (P b) (s b) Δ W
  let ν := fun b => normalGraphMeasure σ (P b) μ
  have hle (w) (t) : ‖phase (mask w) w t*f (mask w) w t‖ ≤ ‖f (mask w) w t‖ := by
    rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hp _ w t)
  have hi (w) := ((h (mask w)).1 w).norm.mono' ((hm _ w).aestronglyMeasurable.mul ((h (mask w)).1 w).aestronglyMeasurable)
    (Eventually.of_forall (hle w))
  refine ⟨hi,Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun w =>
    integral_mono (hi w).norm ((h (mask w)).1 w).norm (hle w)) ?_⟩
  exact normal_finite_winding_partition (fun b w => ∫ t, ‖f b w t‖ ∂ν b) (fun _ _ => integral_nonneg fun _ => norm_nonneg _)
    (fun b => (h b).2) mask

end UV
