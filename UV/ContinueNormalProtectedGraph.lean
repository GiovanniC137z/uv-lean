import UV.ContinueNormalChargedSector
import UV.ContinueWilsonCurrentRotation

/-! Joint absolute convergence of the continuum charged and transverse
photon integrations in the compressed normal-circle comparison. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter UV.SectorPlane
open scoped Matrix.Norms.L2Operator

namespace UV

variable {V Z : Type*} [Fintype V] [MeasurableSpace Z]

/-- The loop momenta are integrated independently, while every transfer
may depend on the same outer variables and the entire winding assignment. -/
theorem normal_measured_graph_integral {m L : ℝ} (σ : Measure OSFourSpace) [SigmaFinite σ]
    (P : V → NormalChargedSector L)
    (hbP : ∀ v, ∃ g : ℤ → ℝ, (∀ w, 0 ≤ g w) ∧ Summable g ∧ ∀ w Δ s,
      Integrable ((P v).amplitude m w Δ s) ((P v).measure σ) ∧
      (∫ t, ‖(P v).amplitude m w Δ s t‖ ∂(P v).measure σ) ≤ g w)
    (s : (V → ℤ) → (v : V) → Z → Fin (P v).segments → OSFourSpace)
    (hs : ∀ w v j, Measurable (s w v · j)) (Δ : V → Z → OSFourSpace) (hΔ : ∀ v, Measurable (Δ v))
    (μ : Measure Z) [SFinite μ] {W : Z → ℂ} (hW : Measurable W) (hiW : Integrable W μ) :
    let ν := Measure.pi (fun v => (P v).measure σ)
    let F := fun w : V → ℤ => wilsonJointFactors W (fun v q => (P v).amplitude m (w v) (Δ v q) (s w v q))
    (∀ w, Integrable (F w) (μ.prod ν)) ∧ Summable (fun w => ∫ t, ‖F w t‖ ∂μ.prod ν) := by
  classical
  choose g hg hsum hb using hbP
  have h (w : V → ℤ) := wilson_joint_factors_measure (fun v => (P v).measure σ) μ hW hiW
    (fun v => (P v).amplitude_measurable m (w v) (hs w v) (hΔ v))
    (fun v q => (hb v (w v) (Δ v q) (s w v q)).1)
    (fun v => g v (w v)) (fun v q => (hb v (w v) (Δ v q) (s w v q)).2)
  exact ⟨fun w => (h w).1,Summable.of_nonneg_of_le (fun w => integral_nonneg fun _ => norm_nonneg _)
    (fun w => (h w).2) ((wilson_summable_product hg hsum).mul_left _)⟩

theorem normal_protected_graph_integral {m L : ℝ} (hm : 0 < m) (hL : 0 < L)
    (P : V → NormalChargedSector L)
    (s : (V → ℤ) → (v : V) → Z → Fin (P v).segments → OSFourSpace)
    (hs : ∀ w v j, Measurable (s w v · j)) (Δ : V → Z → OSFourSpace) (hΔ : ∀ v, Measurable (Δ v))
    (μ : Measure Z) [SFinite μ] {W : Z → ℂ} (hW : Measurable W) (hiW : Integrable W μ) :
    let ν := Measure.pi (fun v => (volume : Measure (P v).Variables))
    let F := fun w : V → ℤ => wilsonJointFactors W (fun v q => (P v).amplitude m (w v) (Δ v q) (s w v q))
    (∀ w, Integrable (F w) (μ.prod ν)) ∧ Summable (fun w => ∫ t, ‖F w t‖ ∂μ.prod ν) := by
  simpa only [NormalChargedSector.measure_volume] using normal_measured_graph_integral volume P
    (fun v => by simpa only [(P v).measure_volume] using (P v).amplitude_budget hm hL) s hs Δ hΔ μ hW hiW

/-- A finite set of independent A4 Maxwell photon chords and IR-controlled
dependent edges can connect any of the three kinds of charged component.
The readout here is isometric on the four-dimensional carrier. -/
theorem normal_hard_protected_graph {C D ι : Type*} [Fintype C] [Fintype D] [Fintype ι]
    {m L ρ : ℝ} (hm : 0 < m) (hL : 0 < L) (hρ : 0 < ρ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (chord : C → WilsonPhotonPolarizations) (tree : D → WilsonPhotonPolarizations)
    (route : (C → OSFourSpace) → D → OSFourSpace) (hr : ∀ i, Measurable (route · i))
    (P : V → NormalChargedSector L) (s : (V → ℤ) → (v : V) → (C → OSFourSpace) → Fin (P v).segments → OSFourSpace)
    (hs : ∀ w v j, Measurable (s w v · j)) (Δ : V → (C → OSFourSpace) → OSFourSpace) (hΔ : ∀ v, Measurable (Δ v)) :
    let μ := Measure.pi (fun _ : C => (volume : Measure OSFourSpace))
    let ν := Measure.pi (fun v => (volume : Measure (P v).Variables))
    let W := fun q => (wilsonHardPhotonProduct ρ (wilsonShellPhotonForm L T) chord tree route q : ℂ)
    let F := fun w : V → ℤ => wilsonJointFactors W (fun v q => (P v).amplitude m (w v) (Δ v q) (s w v q))
    (∀ w, Integrable (F w) (μ.prod ν)) ∧ Summable (fun w => ∫ t, ‖F w t‖ ∂μ.prod ν) :=
  normal_protected_graph_integral hm hL P s hs Δ hΔ _
    (Complex.continuous_ofReal.measurable.comp (wilson_hard_product_measurable ρ (wilson_shell_form_continuous L T) chord tree hr))
    ((wilson_hard_product_integrable hL hρ T chord tree hr).ofReal (𝕜 := ℂ))

/-- In a fixed sector's oriented chart the Fourier transform retains the
gamma-five normal frequency. Its norm depends on the carrier length. -/
theorem SectorPlane.Plane.normal_cover_transform_norm {E : Type*} [Norm E] (diamond : Plane E)
    {m : ℝ} (hm : 0 < m) (p : OSFourSpace) (ξ : ℝ) :
    ‖∫ d : ℝ, Complex.exp (-Complex.I*(ξ:ℂ)*d) • normalDiracCover normalCoverGamma5 m (diamond.osOrientedChart p) d‖ =
      (Real.sqrt (m^2+‖p‖^2+ξ^2))⁻¹ := by
  rw [normal_frequency_is_cover_transform hm (diamond.osOrientedChart p) ξ,normal_dirac_frequency_norm hm]
  simp only [normalFiveDenom,diamond.osOrientedChart.norm_map]

/-- The unit polarizations and routed transfers are read in the same
sector chart; the integrated carrier variable is in that chart. -/
theorem SectorPlane.Plane.normal_winding_chart_absolute {E : Type*} [Norm E] (diamond : Plane E)
    {n : ℕ} {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ : ℝ)
    (u : Fin (n+1) → UnitVector OSFourSpace) (s : ℤ → Fin (n+1) → OSFourSpace) :
    let F := fun (w : ℤ) (t : (Fin n → ℝ) × OSFourSpace) =>
      normalWindingTrace m L θ w (fun j => wilsonRotateUnit diamond.osOrientedChart (u j))
        (fun j => t.2+diamond.osOrientedChart (s w j)) t.1
    (∀ w ≠ 0, Integrable (F w)) ∧ Summable (fun w : ℤ => if w = 0 then 0 else ∫ t, ‖F w t‖) :=
  normal_nonzero_windings_absolute hm hL θ _ _

end UV
