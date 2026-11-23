import UV.ContinueClosingPositiveSpectral
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.Analysis.Matrix.Order

/-! A common finite scalar measure for arbitrary finite-slot complex
matrix measures and positivity of their density. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology MatrixOrder ComplexOrder ENNReal

namespace UV.SectorPlane

variable {ι : Type*} [Fintype ι]

def closingControlMeasure (M : Matrix ι ι (ComplexMeasure ℝ)) : Measure ℝ :=
  ∑ a : ι × ι, ((M a.1 a.2).re.totalVariation + (M a.1 a.2).im.totalVariation)

instance (M : Matrix ι ι (ComplexMeasure ℝ)) : IsFiniteMeasure (closingControlMeasure M) := by
  unfold closingControlMeasure SignedMeasure.totalVariation
  infer_instance

def closingMatrixDensity (M : Matrix ι ι (ComplexMeasure ℝ)) (x : ℝ) : Matrix ι ι ℂ :=
  fun i j => (M i j).rnDeriv (closingControlMeasure M) x

theorem closing_density_entry_integrable (M : Matrix ι ι (ComplexMeasure ℝ)) (i j : ι) :
    Integrable (fun x => closingMatrixDensity M x i j) (closingControlMeasure M) :=
  (M i j).integrable_rnDeriv _

theorem closing_control_dominates (M : Matrix ι ι (ComplexMeasure ℝ)) (i j : ι) :
    (M i j).re.totalVariation + (M i j).im.totalVariation ≤ closingControlMeasure M := by
  classical
  let F := fun a : ι × ι => (M a.1 a.2).re.totalVariation + (M a.1 a.2).im.totalVariation
  intro s
  change F (i,j) s ≤ (∑ a, F a) s
  rw [Measure.finset_sum_apply]
  exact Finset.single_le_sum (f := fun a => F a s) (fun _ _ => zero_le _) (Finset.mem_univ (i,j))

private theorem closed_signed_density (μ : Measure ℝ) [IsFiniteMeasure μ]
    (d : SignedMeasure ℝ) (hd : d.totalVariation ≤ μ) {s : Set ℝ} (hs : MeasurableSet s) :
    (∫ x in s, d.rnDeriv μ x ∂μ) = d s := by
  have hac : d ≪ᵥ μ.toENNRealVectorMeasure := by
    apply VectorMeasure.AbsolutelyContinuous.mk
    intro u hu hnull
    rw [Measure.toENNRealVectorMeasure_apply_measurable hu] at hnull
    exact d.null_of_totalVariation_zero (le_antisymm ((hd u).trans hnull.le) bot_le)
  rw [← withDensityᵥ_apply (d.integrable_rnDeriv μ) hs, d.withDensityᵥ_rnDeriv_eq μ hac]

private theorem closed_complex_density (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c : ComplexMeasure ℝ) (hle : c.re.totalVariation + c.im.totalVariation ≤ μ)
    {s : Set ℝ} (hs : MeasurableSet s) : (∫ x in s, c.rnDeriv μ x ∂μ) = c s := by
  apply Complex.ext
  · calc
      _ = ∫ x in s, (c.rnDeriv μ x).re ∂μ := (integral_re (c.integrable_rnDeriv μ).integrableOn).symm
      _ = c.re s := closed_signed_density μ c.re ((le_add_of_nonneg_right (show 0 ≤ c.im.totalVariation from bot_le)).trans hle) hs
      _ = _ := rfl
  · calc
      _ = ∫ x in s, (c.rnDeriv μ x).im ∂μ := (integral_im (c.integrable_rnDeriv μ).integrableOn).symm
      _ = c.im s := closed_signed_density μ c.im ((le_add_of_nonneg_left (show 0 ≤ c.re.totalVariation from bot_le)).trans hle) hs
      _ = _ := rfl

/-- Entrywise Radon–Nikodym reconstruction uses the total variations of
the real and imaginary parts, including singular spectral laws. -/
theorem closing_density_entry_integral (M : Matrix ι ι (ComplexMeasure ℝ)) (i j : ι)
    {s : Set ℝ} (hs : MeasurableSet s) :
    (∫ x in s, closingMatrixDensity M x i j ∂closingControlMeasure M) = M i j s :=
  closed_complex_density _ _ (closing_control_dominates M i j) hs

end UV.SectorPlane
