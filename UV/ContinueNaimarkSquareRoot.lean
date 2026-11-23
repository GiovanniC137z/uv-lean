import UV.ContinueNaimarkPositive

/-! A Borel matrix square root of the positive density. Squaring on
the closed cone is a continuous injection of Polish spaces, so its
inverse on that cone is measurable. -/

noncomputable section
open MeasureTheory Matrix Set
open scoped Topology MatrixOrder ComplexOrder ComplexConjugate

namespace UV.SectorPlane

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private abbrev PositiveMatrices (ι : Type*) [Fintype ι] := {A : Matrix ι ι ℂ // A.PosSemidef}

private theorem closing_sqrt_measurable : Measurable (fun A : PositiveMatrices ι => CFC.sqrt A.val) := by
  letI : PolishSpace (Matrix ι ι ℂ) := inferInstanceAs (PolishSpace (ι → ι → ℂ))
  letI : PolishSpace (PositiveMatrices ι) := closing_matrix_positive_closed.polishSpace
  let f : PositiveMatrices ι → Matrix ι ι ℂ := fun A => A.val * A.val
  have hf : MeasurableEmbedding f := by
    apply (continuous_subtype_val.mul continuous_subtype_val).measurableEmbedding
    intro A B h
    apply Subtype.ext
    simpa only [CFC.sqrt_mul_self _ A.property.nonneg, CFC.sqrt_mul_self _ B.property.nonneg]
      using congrArg CFC.sqrt h
  let g : PositiveMatrices ι → PositiveMatrices ι := fun A => ⟨CFC.sqrt A.val, (CFC.sqrt_nonneg _).posSemidef⟩
  have hid : f ∘ g = Subtype.val := by
    funext A
    exact CFC.sqrt_mul_sqrt_self _ A.property.nonneg
  have hg : Measurable g := hf.measurable_comp_iff.mp (hid ▸ measurable_subtype_coe)
  exact measurable_subtype_coe.comp hg

open Classical in
def closingPositiveDensity (M : Matrix ι ι (ComplexMeasure ℝ)) (x : ℝ) : PositiveMatrices ι :=
  ⟨if (closingMatrixDensity M x).PosSemidef then closingMatrixDensity M x else 0,
    by split <;> first | assumption | exact Matrix.PosSemidef.zero⟩

/-- A measurable square-root amplitude on all energies, with the null
nonpositive set represented by zero. -/
def closingNaimarkFactor (M : Matrix ι ι (ComplexMeasure ℝ)) (x : ℝ) : Matrix ι ι ℂ :=
  CFC.sqrt (closingPositiveDensity M x).val

theorem closing_naimark_factor_measurable (M : Matrix ι ι (ComplexMeasure ℝ)) :
    Measurable (closingNaimarkFactor M) := by
  classical
  apply closing_sqrt_measurable.comp
  apply Measurable.subtype_mk
  have hset := closing_matrix_positive_closed.measurableSet.preimage (closing_matrix_density_measurable M)
  exact (closing_matrix_density_measurable M).piecewise hset (measurable_const (a := (0 : Matrix ι ι ℂ)))

theorem closing_naimark_factor_gram (M : Matrix ι ι (ComplexMeasure ℝ))
    (hM : ∀ s : Set ℝ, MeasurableSet s → Matrix.PosSemidef ((fun i j => M i j s) : Matrix ι ι ℂ)) :
    ∀ᵐ x ∂closingControlMeasure M,
      (closingNaimarkFactor M x)ᴴ * closingNaimarkFactor M x = closingMatrixDensity M x := by
  classical
  filter_upwards [closing_matrix_density_positive M hM] with x hx
  have h : (closingPositiveDensity M x).val = closingMatrixDensity M x := by simp [closingPositiveDensity,hx]
  rw [closingNaimarkFactor, h, (CFC.sqrt_nonneg _).posSemidef.isHermitian.eq, CFC.sqrt_mul_sqrt_self _ hx.nonneg]

end UV.SectorPlane
