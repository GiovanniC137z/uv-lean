import UV.ResumeSpectrumBulk
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The actual positive boundary spectral probability measure of the normal
comparison, identified with its literal Green function by real integration. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace UV.RevisionSpectrum

def resumeBulkBoundaryMeasure (β b M₂ : ℝ) : Measure ℝ :=
  ENNReal.ofReal (bulkResidue β b M₂) • Measure.dirac (bulkPole β b M₂) +
    (volume.restrict (Ioi M₂)).withDensity
      (fun s => ENNReal.ofReal (bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s)))

theorem resumeBulkBoundaryMeasure_mass {β b M₂ : ℝ} (hβ : 0<β) (hb : b<M₂) :
    resumeBulkBoundaryMeasure β b M₂ univ = 1 := by
  have hρ (s : ℝ) : 0≤bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s) := by
    unfold bulkBoundaryDensity
    positivity
  have hcont : ((volume.restrict (Ioi M₂)).withDensity
      (fun s => ENNReal.ofReal (bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s)))) univ =
      ENNReal.ofReal (∫ s : ℝ in Ioi M₂,
        bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s)) := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal (bulkBoundary_mass hβ hb).1
      (Eventually.of_forall hρ)).symm
  unfold resumeBulkBoundaryMeasure
  rw [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, hcont,
    ← ENNReal.ofReal_add (bulkResidue_positive hβ hb).le
      (integral_nonneg fun _ => hρ _), (bulkBoundary_mass hβ hb).2]
  norm_num

theorem resumeBulkBoundaryMeasure_probability {β b M₂ : ℝ} (hβ : 0<β) (hb : b<M₂) :
    IsProbabilityMeasure (resumeBulkBoundaryMeasure β b M₂) :=
  ⟨resumeBulkBoundaryMeasure_mass hβ hb⟩

theorem resumeBulkBoundaryMeasure_nonnegative_support {β b M₂ : ℝ}
    (hβ : 0<β) (hb₀ : 0<b) (hb : b<M₂) :
    ∀ᵐ s ∂resumeBulkBoundaryMeasure β b M₂, 0≤s := by
  have hp : 0≤bulkPole β b M₂ := (hb₀.trans (bulkPole_unique hβ hb).1).le
  have hM : 0<M₂ := hb₀.trans hb
  unfold resumeBulkBoundaryMeasure
  rw [ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure ((ae_dirac_iff measurableSet_Ici).mpr hp) _
  · apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hM.le.trans hs.le

theorem resumeBulkBoundaryMeasure_stieltjes_integrable {β b M₂ x : ℝ}
    (hβ : 0<β) (hb₀ : 0<b) (hb : b<M₂) (hx : 0<x) :
    Integrable (fun s : ℝ => (x+s)⁻¹) (resumeBulkBoundaryMeasure β b M₂) := by
  have hρ (s : ℝ) : 0≤bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s) := by
    unfold bulkBoundaryDensity
    positivity
  have ha : Integrable (fun s : ℝ => (x+s)⁻¹)
      (ENNReal.ofReal (bulkResidue β b M₂) • Measure.dirac (bulkPole β b M₂)) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hc : Integrable (fun s : ℝ => (x+s)⁻¹)
      ((volume.restrict (Ioi M₂)).withDensity
        (fun s => ENNReal.ofReal (bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s)))) := by
    rw [integrable_withDensity_iff_integrable_smul' (by unfold bulkBoundaryDensity; fun_prop)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simpa only [ENNReal.toReal_ofReal (hρ _), smul_eq_mul, ← div_eq_mul_inv] using
      (resume_bulk_boundary_stieltjes hβ hb₀ hb hx).1
  exact ha.add_measure hc

/-- The positive measure is constructed explicitly; its Stieltjes transform
is the actual boundary resolvent, not an assumed spectral representation. -/
theorem resumeBulkBoundaryMeasure_stieltjes {β b M₂ x : ℝ}
    (hβ : 0<β) (hb₀ : 0<b) (hb : b<M₂) (hx : 0<x) :
    (∫ s : ℝ, (x+s)⁻¹ ∂resumeBulkBoundaryMeasure β b M₂) =
      (x+b+β*Real.sqrt (x+M₂))⁻¹ := by
  have hρ (s : ℝ) : 0≤bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s) := by
    unfold bulkBoundaryDensity
    positivity
  have ha : Integrable (fun s : ℝ => (x+s)⁻¹)
      (ENNReal.ofReal (bulkResidue β b M₂) • Measure.dirac (bulkPole β b M₂)) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hc : Integrable (fun s : ℝ => (x+s)⁻¹)
      ((volume.restrict (Ioi M₂)).withDensity
        (fun s => ENNReal.ofReal (bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s)))) := by
    rw [integrable_withDensity_iff_integrable_smul' (by unfold bulkBoundaryDensity; fun_prop)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simpa only [ENNReal.toReal_ofReal (hρ _), smul_eq_mul, ← div_eq_mul_inv] using
      (resume_bulk_boundary_stieltjes hβ hb₀ hb hx).1
  unfold resumeBulkBoundaryMeasure
  rw [integral_add_measure ha hc, integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (bulkResidue_positive hβ hb).le,
    integral_withDensity_eq_integral_toReal_smul (by unfold bulkBoundaryDensity; fun_prop)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hρ _), smul_eq_mul, ← div_eq_mul_inv]
  exact (resume_bulk_boundary_stieltjes hβ hb₀ hb hx).2

/-- Exact boundary part of update-positive-bulk-spectrum. The separate
layer-source trace-domain theorem is deliberately not included. -/
theorem resume_positive_bulk_boundary_spectrum {β b M₂ : ℝ}
    (hβ : 0<β) (hb₀ : 0<b) (hb : b<M₂) :
    IsProbabilityMeasure (resumeBulkBoundaryMeasure β b M₂) ∧
    (∀ᵐ s ∂resumeBulkBoundaryMeasure β b M₂, 0≤s) ∧
    ∀ x : ℝ, 0<x →
      Integrable (fun s : ℝ => (x+s)⁻¹) (resumeBulkBoundaryMeasure β b M₂) ∧
      (∫ s : ℝ, (x+s)⁻¹ ∂resumeBulkBoundaryMeasure β b M₂) =
        (x+b+β*Real.sqrt (x+M₂))⁻¹ :=
  ⟨resumeBulkBoundaryMeasure_probability hβ hb,
    resumeBulkBoundaryMeasure_nonnegative_support hβ hb₀ hb, fun _ hx =>
    ⟨resumeBulkBoundaryMeasure_stieltjes_integrable hβ hb₀ hb hx,
      resumeBulkBoundaryMeasure_stieltjes hβ hb₀ hb hx⟩⟩

end UV.RevisionSpectrum
