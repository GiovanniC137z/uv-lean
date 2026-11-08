import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import UV.Convergence

/-! Scale integration for the simultaneous sector envelopes in thm:forest.
Sector parametrizations and their Jacobians must still identify the graph with
these integrals. No isolated scaling test constructs that identification. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace UV

theorem sector_power_integrable {ω : ℝ} (hω : ω < 0) :
    IntegrableOn (fun R : ℝ => R ^ (ω - 1)) (Ioi 1) :=
  integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one

theorem sector_power_integral {ω : ℝ} (hω : ω < 0) :
    (∫ R : ℝ in Ioi 1, R ^ (ω - 1)) = -1 / ω := by
  simpa using integral_Ioi_rpow_of_lt (a := ω - 1) (by linarith) zero_lt_one

theorem sector_gaussian_integrable {a : ℝ} (ha : 0 < a) (s : ℝ) :
    IntegrableOn (fun R : ℝ => R ^ s * Real.exp (-a * R ^ 2)) (Ioi 1) := by
  have hm := (integrableOn_rpow_mul_exp_neg_mul_sq ha
    (show -1 < max s 0 by have := le_max_right s 0; linarith)).mono_set
    (show Ioi (1 : ℝ) ⊆ Ioi 0 from Ioi_subset_Ioi zero_le_one)
  refine hm.mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with R hR
  have hpos : 0 ≤ R := le_of_lt (lt_trans zero_lt_one hR)
  rw [Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (le_of_lt hR) (le_max_left s 0))
    (Real.exp_nonneg _)

def sectorScale (gaussian : Bool) (ω a R : ℝ) : ℝ :=
  if gaussian then R ^ (ω - 1) * Real.exp (-a * R ^ 2) else R ^ (ω - 1)

theorem sector_scale_integrable (gaussian : Bool) (ω a : ℝ)
    (h : if gaussian then 0 < a else ω < 0) :
    IntegrableOn (sectorScale gaussian ω a) (Ioi 1) := by
  cases gaussian with
  | false => exact sector_power_integrable h
  | true => exact sector_gaussian_integrable h _

/-- Finite simultaneous mixed power/Gaussian scale envelope, with the angular
    and infrared variables retained in a finite measure. -/
theorem mixed_sector_envelope_integrable {ι A : Type*} [Fintype ι]
    [MeasurableSpace A] {ν : Measure A} [IsFiniteMeasure ν]
    (gaussian : ι → Bool) (ω a : ι → ℝ) (C : ℝ)
    (h : ∀ i, if gaussian i then 0 < a i else ω i < 0) :
    Integrable (fun x : (ι → ℝ) × A =>
      C * ∏ i, sectorScale (gaussian i) (ω i) (a i) (x.1 i))
      ((Measure.pi (fun _ : ι => volume.restrict (Ioi (1 : ℝ)))).prod ν) := by
  have hp := Integrable.fintype_prod (fun i => sector_scale_integrable
    (gaussian i) (ω i) (a i) (h i))
  simpa only [mul_one] using (hp.mul_prod (integrable_const (μ := ν) (1 : ℝ))).const_mul C

theorem mixed_sector_graph_integrable {ι A : Type*} [Fintype ι]
    [MeasurableSpace A] {ν : Measure A} [IsFiniteMeasure ν]
    (gaussian : ι → Bool) (ω a : ι → ℝ) (C : ℝ)
    (h : ∀ i, if gaussian i then 0 < a i else ω i < 0)
    {f : (ι → ℝ) × A → ℂ}
    (hf : AEStronglyMeasurable f
      ((Measure.pi (fun _ : ι => volume.restrict (Ioi (1 : ℝ)))).prod ν))
    (hb : ∀ᵐ x ∂((Measure.pi (fun _ : ι => volume.restrict (Ioi (1 : ℝ)))).prod ν),
      ‖f x‖ ≤ C * ∏ i, sectorScale (gaussian i) (ω i) (a i) (x.1 i)) :
    Integrable f ((Measure.pi (fun _ : ι => volume.restrict (Ioi (1 : ℝ)))).prod ν) :=
  (mixed_sector_envelope_integrable gaussian ω a C h).mono' hf hb

/-- Transfer integrable parametrized sectors to the original graph measure.
    The measure domination is the precise covering/Jacobian obligation. -/
theorem integrable_of_finite_sector_cover {H X : Type*} [Fintype H]
    [MeasurableSpace X] {T : H → Type*} [∀ h, MeasurableSpace (T h)]
    (μ μIR : Measure X) (ν : ∀ h, Measure (T h)) (σ : ∀ h, T h → X)
    (f : X → ℂ) (hf : StronglyMeasurable f)
    (hσ : ∀ h, Measurable (σ h)) (hIR : Integrable f μIR)
    (hsector : ∀ h, Integrable (f ∘ σ h) (ν h))
    (hcover : μ ≤ μIR + ∑ h, Measure.map (σ h) (ν h)) : Integrable f μ := by
  have hs : Integrable f (∑ h, Measure.map (σ h) (ν h)) := by
    apply integrable_finset_sum_measure.mpr
    intro h _
    exact (integrable_map_measure hf.aestronglyMeasurable (hσ h).aemeasurable).mpr
      (hsector h)
  exact (hIR.add_measure hs).mono_measure hcover

/-- Conditional forest convergence in a measure-theoretic sector realization.
    Every sector has its own number of scales and finite angular/IR measure;
    negative residual degrees and Gaussian-controlled scales may be mixed. -/
theorem conditional_forest_convergence {H X : Type*} [Fintype H]
    [MeasurableSpace X] {A : H → Type*} [∀ h, MeasurableSpace (A h)]
    (r : H → ℕ) (ν : ∀ h, Measure (A h)) [∀ h, IsFiniteMeasure (ν h)]
    (μ μIR : Measure X)
    (σ : ∀ h, ((Fin (r h) → ℝ) × A h) → X)
    (gaussian : ∀ h, Fin (r h) → Bool) (ω a : ∀ h, Fin (r h) → ℝ)
    (C : H → ℝ) (f : X → ℂ) (hf : StronglyMeasurable f)
    (hσ : ∀ h, Measurable (σ h)) (hIR : Integrable f μIR)
    (hscale : ∀ h i, if gaussian h i then 0 < a h i else ω h i < 0)
    (henvelope : ∀ h, ∀ᵐ x ∂((Measure.pi (fun _ : Fin (r h) =>
      volume.restrict (Ioi (1 : ℝ)))).prod (ν h)),
      ‖f (σ h x)‖ ≤ C h * ∏ i, sectorScale (gaussian h i) (ω h i) (a h i) (x.1 i))
    (hcover : μ ≤ μIR + ∑ h, Measure.map (σ h)
      ((Measure.pi (fun _ : Fin (r h) => volume.restrict (Ioi (1 : ℝ)))).prod (ν h))) :
    Integrable f μ := by
  apply integrable_of_finite_sector_cover μ μIR _ σ f hf hσ hIR _ hcover
  intro h
  exact mixed_sector_graph_integrable (gaussian h) (ω h) (a h) (C h) (hscale h)
    (hf.comp_measurable (hσ h)).aestronglyMeasurable (henvelope h)

/-- General change-of-variables version: scale-dependent Jacobians belong in
    the pushed-forward measure and multiply the transformed integrand. -/
theorem integrable_of_weighted_finite_sector_cover {H X : Type*} [Fintype H]
    [MeasurableSpace X] {T : H → Type*} [∀ h, MeasurableSpace (T h)]
    (μ μIR : Measure X) (ν : ∀ h, Measure (T h)) (σ : ∀ h, T h → X)
    (J : ∀ h, T h → ℝ≥0) (f : X → ℂ) (hf : StronglyMeasurable f)
    (hσ : ∀ h, Measurable (σ h)) (hJ : ∀ h, Measurable (J h))
    (hIR : Integrable f μIR)
    (hsector : ∀ h, Integrable (fun x => J h x • f (σ h x)) (ν h))
    (hcover : μ ≤ μIR + ∑ h, Measure.map (σ h)
      ((ν h).withDensity (fun x => (J h x : ℝ≥0∞)))) : Integrable f μ := by
  apply integrable_of_finite_sector_cover μ μIR _ σ f hf hσ hIR _ hcover
  intro h
  exact (integrable_withDensity_iff_integrable_smul (hJ h)).mpr (hsector h)

/-- The mixed scale criterion with the actual Jacobian-weighted envelope.
    In particular, radial factors such as R^(n-1) are retained. -/
theorem conditional_forest_convergence_weighted {H X : Type*} [Fintype H]
    [MeasurableSpace X] {A : H → Type*} [∀ h, MeasurableSpace (A h)]
    (r : H → ℕ) (ν : ∀ h, Measure (A h)) [∀ h, IsFiniteMeasure (ν h)]
    (μ μIR : Measure X) (σ : ∀ h, ((Fin (r h) → ℝ) × A h) → X)
    (J : ∀ h, ((Fin (r h) → ℝ) × A h) → ℝ≥0)
    (gaussian : ∀ h, Fin (r h) → Bool) (ω a : ∀ h, Fin (r h) → ℝ)
    (C : H → ℝ) (f : X → ℂ) (hf : StronglyMeasurable f)
    (hσ : ∀ h, Measurable (σ h)) (hJ : ∀ h, Measurable (J h))
    (hIR : Integrable f μIR)
    (hscale : ∀ h i, if gaussian h i then 0 < a h i else ω h i < 0)
    (henvelope : ∀ h, ∀ᵐ x ∂((Measure.pi (fun _ : Fin (r h) =>
      volume.restrict (Ioi (1 : ℝ)))).prod (ν h)),
      ‖J h x • f (σ h x)‖ ≤ C h * ∏ i,
        sectorScale (gaussian h i) (ω h i) (a h i) (x.1 i))
    (hcover : μ ≤ μIR + ∑ h, Measure.map (σ h)
      (Measure.withDensity
        ((Measure.pi (fun _ : Fin (r h) => volume.restrict (Ioi (1 : ℝ)))).prod (ν h))
        (fun x => (J h x : ℝ≥0∞)))) : Integrable f μ := by
  apply integrable_of_weighted_finite_sector_cover μ μIR _ σ J f hf hσ hJ hIR _ hcover
  intro h
  apply mixed_sector_graph_integrable (gaussian h) (ω h) (a h) (C h) (hscale h)
  · exact (hJ h).aestronglyMeasurable.smul
      (hf.comp_measurable (hσ h)).aestronglyMeasurable
  · exact henvelope h

end UV
