import UV.ContinueNormalMaxwellModes
import UV.ContinueNormalLatticeGraph

/-! Actual routed A4 Maxwell factors with an external test density.
Chord momenta are independent and each dependent edge may use all chords
and all external variables. On a torus only the harmonic mode is fixed. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter UV.SectorPlane

namespace UV

variable {Y M C D : Type*} [MeasurableSpace Y] [MeasurableSpace M] [Fintype C] [Fintype D]

def normalTestedPhotonWeight (A : Y → ℂ) (p : M → OSFourSpace) (χ : OSFourSpace → ℂ)
    (chord : C → WilsonPhotonPolarizations) (H : D → Y × (C → M) → ℝ) (z : Y × (C → M)) : ℂ :=
  A z.1 * (((∏ i, (chord i).maxwell χ (p (z.2 i))) * ∏ e, H e z : ℝ) : ℂ)

theorem normal_tested_photon_weight (μ : Measure Y) [SFinite μ] (σ : Measure M) [SigmaFinite σ]
    (A : Y → ℂ) (hmA : Measurable A) (hiA : Integrable A μ) (p : M → OSFourSpace) (hp : Measurable p)
    (χ : OSFourSpace → ℂ) (hχ : Continuous χ) (hi : Integrable (fun k => wilsonPhotonDensity χ (p k)) σ)
    (chord : C → WilsonPhotonPolarizations) (H : D → Y × (C → M) → ℝ) (hm : ∀ e, Measurable (H e))
    (B : ℝ) (hb : ∀ e z, ‖H e z‖ ≤ B) :
    let F := normalTestedPhotonWeight A p χ chord H
    Measurable F ∧ Integrable F (μ.prod (Measure.pi fun _ : C => σ)) := by
  let X := fun q : C → M => ∏ i, wilsonPhotonDensity χ (p (q i))
  have hX : Integrable X (Measure.pi fun _ : C => σ) := Integrable.fintype_prod fun _ => hi
  have hF : Measurable (normalTestedPhotonWeight A p χ chord H) :=
    (hmA.comp measurable_fst).mul (Complex.continuous_ofReal.measurable.comp
      ((Finset.measurable_prod _ (fun i _ => ((chord i).maxwell_measurable hχ).comp
        (hp.comp ((measurable_pi_apply i).comp measurable_snd)))).mul (Finset.measurable_prod _ (fun e _ => hm e))))
  refine ⟨hF,(hiA.norm.mul_prod (hX.mul_const (B^Fintype.card D))).mono' hF.aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)⟩
  simp only [normalTestedPhotonWeight,norm_mul,Complex.norm_real,norm_prod,X]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply mul_le_mul (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => (chord i).maxwell_bound χ _))
    _ (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (Finset.prod_nonneg (fun _ _ => wilson_photon_density_nonneg _ _))
  simpa only [Finset.prod_const,Finset.card_univ] using Finset.prod_le_prod (s := (Finset.univ : Finset D))
    (fun _ _ => norm_nonneg _) (fun e _ => hb e z)

theorem normal_continuum_tested_photons {ι : Type*} [Fintype ι] {L ρ : ℝ} (hL : 0 < L) (hρ : 0 < ρ)
    (T : OSFourSpace →L[ℝ] WilsonBallSpace ι) (hr : 3 ≤ Module.finrank ℝ (LinearMap.range T.toLinearMap))
    (μ : Measure Y) [SFinite μ] (A : Y → ℂ) (hmA : Measurable A) (hiA : Integrable A μ)
    (chord : C → WilsonPhotonPolarizations) (tree : D → WilsonPhotonPolarizations)
    (route : Y × (C → OSFourSpace) → D → OSFourSpace) (hroute : ∀ e, Measurable (route · e)) :
    let χ := normalPhotonForm L T
    let F := normalTestedPhotonWeight A id χ chord (fun e z => (tree e).hard ρ χ (route z e))
    Measurable F ∧ Integrable F (μ.prod (Measure.pi fun _ : C => (volume : Measure OSFourSpace))) :=
  normal_tested_photon_weight μ volume A hmA hiA id measurable_id _ (normal_photon_form_continuous L T)
    (normal_continuum_maxwell_integrable hL T hr) chord _
    (fun e => ((tree e).hard_measurable ρ (normal_photon_form_continuous L T)).comp (hroute e))
    _ (fun e z => (tree e).hard_bound hρ (fun p => normal_shell_characteristic_le_one (L • T p)) (route z e))

theorem normal_torus_tested_photons {ι : Type*} [Fintype ι] (b : NormalReciprocalBasis) {L : ℝ} (hL : 0 < L)
    (T : OSFourSpace →L[ℝ] WilsonBallSpace ι) (hr : 3 ≤ Module.finrank ℝ (LinearMap.range T.toLinearMap))
    (μ : Measure Y) [SFinite μ] (A : Y → ℂ) (hmA : Measurable A) (hiA : Integrable A μ)
    (chord : C → WilsonPhotonPolarizations) (tree : D → WilsonPhotonPolarizations)
    (route : Y × (C → NormalReciprocalLattice b) → D → NormalReciprocalLattice b) (hroute : ∀ e, Measurable (route · e)) :
    let χ := normalPhotonForm L T
    let F := normalTestedPhotonWeight A (fun k : NormalReciprocalLattice b => (k:OSFourSpace)) χ chord
      (fun e z => (tree e).maxwell χ (route z e))
    Measurable F ∧ Integrable F (μ.prod (Measure.pi fun _ : C => (Measure.count : Measure (NormalReciprocalLattice b)))) := by
  let χ := normalPhotonForm L T
  have hmχ := normal_photon_form_continuous L T
  have hm : Measurable (wilsonPhotonDensity χ) := (hmχ.measurable.norm.pow_const 2).div (measurable_norm.pow_const 2)
  have hI := (integrable_map_measure hm.aestronglyMeasurable measurable_subtype_coe.aemeasurable).mp
    (normal_lattice_maxwell_integrable b hL T hr)
  obtain ⟨ρ,hρ,hgap⟩ := normal_lattice_mode_gap b
  have hb (e : D) (k : NormalReciprocalLattice b) : ‖(tree e).maxwell χ k‖ ≤ (ρ^2)⁻¹ := by
    by_cases hk : k = 0
    · subst k
      simp [WilsonPhotonPolarizations.maxwell,wilsonPhotonDensity,sq_nonneg]
    · have h := (tree e).hard_bound hρ (fun p => normal_shell_characteristic_le_one (L • T p)) (k:OSFourSpace)
      simpa only [WilsonPhotonPolarizations.hard,if_pos (hgap k hk)] using h
  exact normal_tested_photon_weight μ Measure.count A hmA hiA _ measurable_subtype_coe χ hmχ hI chord _
    (fun e => ((tree e).maxwell_measurable hmχ).comp (measurable_subtype_coe.comp (hroute e)))
    _ (fun e z => hb e (route z e))

end UV
