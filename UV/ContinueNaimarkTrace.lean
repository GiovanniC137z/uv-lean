import UV.ContinueNaimarkColumns
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The trace measure and the unbounded-energy second-moment condition
for a positive finite-slot matrix law. -/

noncomputable section
open MeasureTheory Set Filter Matrix
open scoped ENNReal Matrix
namespace UV.SectorPlane

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def closingDiagonalLaw (M : Matrix ι ι (ComplexMeasure ℝ)) (j : ι) : Measure ℝ :=
  (closingControlMeasure M).withDensity (fun x => ENNReal.ofReal (closingMatrixDensity M x j j).re)

def closingTraceLaw (M : Matrix ι ι (ComplexMeasure ℝ)) : Measure ℝ :=
  ∑ j, closingDiagonalLaw M j

private theorem closing_density_diagonal_nonneg (M : Matrix ι ι (ComplexMeasure ℝ))
    (hM : ClosingPositiveMatrixMeasure M) (j : ι) :
    ∀ᵐ x ∂closingControlMeasure M, 0 ≤ (closingMatrixDensity M x j j).re := by
  filter_upwards [closing_factor_column_norm M hM j] with x hx
  rw [←hx]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

omit [DecidableEq ι] in
private theorem closing_density_diagonal_measurable (M : Matrix ι ι (ComplexMeasure ℝ)) (j : ι) :
    Measurable (fun x => (closingMatrixDensity M x j j).re) :=
  Complex.continuous_re.measurable.comp ((measurable_pi_apply j).comp
    ((measurable_pi_apply j).comp (closing_matrix_density_measurable M)))

theorem closing_diagonal_law_apply (M : Matrix ι ι (ComplexMeasure ℝ)) (hM : ClosingPositiveMatrixMeasure M)
    (j : ι) {s : Set ℝ} (hs : MeasurableSet s) :
    closingDiagonalLaw M j s = ENNReal.ofReal (M j j s).re := by
  rw [closingDiagonalLaw, withDensity_apply _ hs]
  have h : IntegrableOn (fun x => (closingMatrixDensity M x j j).re) s (closingControlMeasure M) :=
    (closing_density_entry_integrable M j j).re.integrableOn
  rw [← ofReal_integral_eq_lintegral_ofReal h (ae_restrict_of_ae (closing_density_diagonal_nonneg M hM j))]
  congr 1
  calc
    _ = (∫ x in s, closingMatrixDensity M x j j ∂closingControlMeasure M).re :=
      integral_re (closing_density_entry_integrable M j j).integrableOn
    _ = _ := congrArg Complex.re (closing_density_entry_integral M j j hs)

theorem closing_trace_law_apply (M : Matrix ι ι (ComplexMeasure ℝ)) (hM : ClosingPositiveMatrixMeasure M)
    {s : Set ℝ} (hs : MeasurableSet s) :
    closingTraceLaw M s = ∑ j, ENNReal.ofReal (M j j s).re := by
  simp only [closingTraceLaw, Measure.finset_sum_apply, closing_diagonal_law_apply M hM _ hs]

theorem closing_density_second_integrable (M : Matrix ι ι (ComplexMeasure ℝ))
    (hM : ClosingPositiveMatrixMeasure M) (h₂ : Integrable (fun x : ℝ => x^2) (closingTraceLaw M)) (j : ι) :
    Integrable (fun x : ℝ => x^2 * (closingMatrixDensity M x j j).re) (closingControlMeasure M) := by
  have hd : Integrable (fun x : ℝ => x^2) (closingDiagonalLaw M j) :=
    (integrable_finset_sum_measure.mp h₂) j (Finset.mem_univ j)
  have h := (integrable_withDensity_iff_integrable_smul'
    (closing_density_diagonal_measurable M j).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) (g := fun x : ℝ => x^2)).mp hd
  apply h.congr
  filter_upwards [closing_density_diagonal_nonneg M hM j] with x hx
  simp [ENNReal.toReal_ofReal hx, mul_comm]

end UV.SectorPlane
