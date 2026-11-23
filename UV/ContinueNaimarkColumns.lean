import UV.ContinueNaimarkSquareRoot
import UV.ContinueOpeningCoordinateMoment
import Mathlib.MeasureTheory.Integral.Prod

/-! Square-root columns as actual square-integrable functions on signed
energy times a finite multiplicity index. -/

noncomputable section
open MeasureTheory Set Filter Matrix
open scoped ComplexOrder ENNReal InnerProductSpace ComplexConjugate Matrix

namespace UV.SectorPlane

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

def closingNaimarkMeasure (M : Matrix ι ι (ComplexMeasure ℝ)) : Measure (ι × ℝ) :=
  Measure.count.prod (closingControlMeasure M)

def closingColumnValue (M : Matrix ι ι (ComplexMeasure ℝ)) (j : ι) (p : ι × ℝ) : ℂ :=
  closingNaimarkFactor M p.2 p.1 j

theorem closing_column_measurable (M : Matrix ι ι (ComplexMeasure ℝ)) (j : ι) :
    Measurable (closingColumnValue M j) := by
  apply measurable_from_prod_countable_right
  intro i
  exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (closing_naimark_factor_measurable M))

abbrev ClosingPositiveMatrixMeasure (M : Matrix ι ι (ComplexMeasure ℝ)) : Prop :=
  ∀ s : Set ℝ, MeasurableSet s → Matrix.PosSemidef (fun i j => M i j s)

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
theorem closing_factor_column_norm (M : Matrix ι ι (ComplexMeasure ℝ))
    (hM : ClosingPositiveMatrixMeasure M) (j : ι) :
    ∀ᵐ x ∂closingControlMeasure M,
      ∑ i, ‖closingNaimarkFactor M x i j‖^2 = (closingMatrixDensity M x j j).re := by
  filter_upwards [closing_naimark_factor_gram M hM] with x hx
  have h := congrArg (fun A : Matrix ι ι ℂ => (A j j).re) hx
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.sq_norm] using h

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
theorem closing_column_slice_memLp (M : Matrix ι ι (ComplexMeasure ℝ)) (hM : ClosingPositiveMatrixMeasure M)
    (i j : ι) : MemLp (fun x => closingNaimarkFactor M x i j) 2 (closingControlMeasure M) := by
  let f := fun x => closingNaimarkFactor M x i j
  have hm : Measurable f := (measurable_pi_apply j).comp
    ((measurable_pi_apply i).comp (closing_naimark_factor_measurable M))
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply (closing_density_entry_integrable M j j).re.mono' (hm.norm.pow_const 2).aestronglyMeasurable
  filter_upwards [closing_factor_column_norm M hM j] with x hx
  change ‖‖f x‖^2‖ ≤ (closingMatrixDensity M x j j).re
  rw [← hx, Real.norm_of_nonneg (sq_nonneg _)]
  exact Finset.single_le_sum (f := fun k => ‖closingNaimarkFactor M x k j‖^2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

theorem closing_column_memLp (M : Matrix ι ι (ComplexMeasure ℝ))
    (hM : ClosingPositiveMatrixMeasure M) (j : ι) :
    MemLp (closingColumnValue M j) 2 (closingNaimarkMeasure M) := by
  have hm := closing_column_measurable M j
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  exact (integrable_prod_iff (hm.norm.pow_const 2).aestronglyMeasurable).mpr
    ⟨ae_of_all _ fun i => (memLp_two_iff_integrable_sq_norm
      (closing_column_slice_memLp M hM i j).1).mp (closing_column_slice_memLp M hM i j),
      Integrable.of_finite⟩

def closingNaimarkColumn (M : Matrix ι ι (ComplexMeasure ℝ)) (hM : ClosingPositiveMatrixMeasure M)
    (j : ι) : Lp ℂ 2 (closingNaimarkMeasure M) := (closing_column_memLp M hM j).toLp _

theorem closing_naimark_column_ae (M : Matrix ι ι (ComplexMeasure ℝ))
    (hM : ClosingPositiveMatrixMeasure M) (j : ι) :
    (closingNaimarkColumn M hM j : ι × ℝ → ℂ) =ᵐ[closingNaimarkMeasure M] closingColumnValue M j :=
  (closing_column_memLp M hM j).coeFn_toLp

end UV.SectorPlane
