import UV.ContinueNaimarkDensity
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! A setwise positive finite matrix measure has an almost everywhere
positive matrix density. The proof differentiates all its entries along
the same real energy intervals. -/

noncomputable section
open MeasureTheory Set Filter Matrix Metric
open scoped Topology MatrixOrder ComplexOrder ENNReal Matrix

namespace UV.SectorPlane

instance closingMatrixMeasurableSpace {ι : Type*} : MeasurableSpace (Matrix ι ι ℂ) :=
  inferInstanceAs (MeasurableSpace (ι → ι → ℂ))

instance closingMatrixBorelSpace {ι : Type*} [Fintype ι] : BorelSpace (Matrix ι ι ℂ) :=
  inferInstanceAs (BorelSpace (ι → ι → ℂ))

variable {ι : Type*} [Fintype ι]

theorem closing_matrix_positive_closed : IsClosed {A : Matrix ι ι ℂ | A.PosSemidef} := by
  have h₁ : IsClosed {A : Matrix ι ι ℂ | A.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have h₂ (v : ι → ℂ) : IsClosed {A : Matrix ι ι ℂ | 0 ≤ star v ⬝ᵥ (A *ᵥ v)} :=
    isClosed_le continuous_const (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))
  change IsClosed {A : Matrix ι ι ℂ | A.IsHermitian ∧ ∀ v, 0 ≤ star v ⬝ᵥ (A *ᵥ v)}
  simp only [setOf_and, setOf_forall]
  exact h₁.inter (isClosed_iInter h₂)

theorem closing_matrix_density_measurable (M : Matrix ι ι (ComplexMeasure ℝ)) :
    Measurable (closingMatrixDensity M) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have hre := ((M i j).re.measurable_rnDeriv (closingControlMeasure M)).complex_ofReal
  have him := ((M i j).im.measurable_rnDeriv (closingControlMeasure M)).complex_ofReal
  convert hre.add (him.mul_const Complex.I) using 1
  exact funext fun x => (Complex.re_add_im (closingMatrixDensity M x i j)).symm

theorem closing_matrix_density_positive (M : Matrix ι ι (ComplexMeasure ℝ))
    (hM : ∀ s : Set ℝ, MeasurableSet s → Matrix.PosSemidef ((fun i j => M i j s) : Matrix ι ι ℂ)) :
    ∀ᵐ x ∂closingControlMeasure M, (closingMatrixDensity M x).PosSemidef := by
  let μ := closingControlMeasure M
  let F := closingMatrixDensity M
  have he (i j : ι) := (Besicovitch.vitaliFamily μ).ae_tendsto_average
    (closing_density_entry_integrable M i j).locallyIntegrable
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (he i))] with x hx
  let A (r : ℝ) : Matrix ι ι ℂ := fun i j => ⨍ t in closedBall x r, F t i j ∂μ
  have hA : Tendsto A (𝓝[>] 0) (𝓝 (F x)) := tendsto_pi_nhds.mpr
    fun i => tendsto_pi_nhds.mpr fun j => (hx i j).comp (Besicovitch.tendsto_filterAt μ x)
  apply closing_matrix_positive_closed.mem_of_tendsto hA
  apply Eventually.of_forall
  intro r
  let s := closedBall x r
  have hs : MeasurableSet s := isClosed_closedBall.measurableSet
  have hEq : A r = (μ.real s)⁻¹ • ((fun i j => M i j s) : Matrix ι ι ℂ) := by
    ext i j
    exact (setAverage_eq μ _ _).trans (congrArg ((μ.real s)⁻¹ • ·) (closing_density_entry_integral M i j hs))
  rw [hEq]
  exact (hM s hs).smul (inv_nonneg.mpr ENNReal.toReal_nonneg)

end UV.SectorPlane
