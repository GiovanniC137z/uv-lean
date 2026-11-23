import UV.ContinuationBoundaryPairing
import UV.UnboundedSourceBorel

/-! Actual normalized positive finite-slot measures from compression
of a spectral resolution on the signed real energy line. -/

noncomputable section

open MeasureTheory Set ContinuousLinearMap
open scoped InnerProductSpace ENNReal

namespace UV.SectorPlane

variable {H S : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]

def closingDisplacementPVM (P : SourcePVM H) : UV.ContinuationBoundary.DisplacementPVM ℝ H :=
  ⟨P.projection, P.empty, P.univ, P.selfAdjoint, P.inter, P.countable⟩

/-- The setwise compression is positive because it is a square of
the orthogonal spectral projection applied to the isometric slot. -/
def closingSpectralCompression (P : SourcePVM H) (J : S →ₗᵢ[ℂ] H) (U : Set ℝ) : S →L[ℂ] S :=
  J.toContinuousLinearMap.adjoint.comp ((P.projection U).comp J.toContinuousLinearMap)

theorem closing_projection_inner_self (P : SourcePVM H) {U : Set ℝ}
    (hU : MeasurableSet U) (x : H) :
    ⟪x, P.projection U x⟫_ℂ = ((‖P.projection U x‖ ^ 2 : ℝ) : ℂ) := by
  have hp : (P.projection U).adjoint = P.projection U := (P.selfAdjoint U hU).star_eq
  calc
    _ = ⟪x, (P.projection U).adjoint ((P.projection U) x)⟫_ℂ := by
      rw [hp, ← ContinuousLinearMap.mul_apply, sourcePVM_idempotent P hU]
    _ = _ := by
      rw [ContinuousLinearMap.adjoint_inner_right]
      simpa only [Complex.ofReal_pow] using (inner_self_eq_norm_sq_to_K (P.projection U x))

theorem closing_spectral_compression_positive (P : SourcePVM H) (J : S →ₗᵢ[ℂ] H)
    {U : Set ℝ} (hU : MeasurableSet U) (v : S) :
    ⟪v, closingSpectralCompression P J U v⟫_ℂ =
      ((‖P.projection U (J v)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [closingSpectralCompression, coe_comp', Function.comp_apply, adjoint_inner_right]
  exact closing_projection_inner_self P hU (J v)

theorem closing_spectral_compression_univ (P : SourcePVM H) (J : S →ₗᵢ[ℂ] H) :
    closingSpectralCompression P J univ = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro x
  simp only [closingSpectralCompression, coe_comp', Function.comp_apply, adjoint_inner_right,
    P.univ, ContinuousLinearMap.one_apply]
  exact J.inner_map_map x v

section Slots

variable {ι : Type*} [Fintype ι]

/-- Each entry is an actual countably additive complex measure. -/
def closingMatrixSpectralMeasure (P : SourcePVM H) (J : S →ₗᵢ[ℂ] H)
    (b : OrthonormalBasis ι ℂ S) : Matrix ι ι (ComplexMeasure ℝ) :=
  fun i j => UV.ContinuationBoundary.overlapMeasure (closingDisplacementPVM P) (J (b i)) (J (b j))

theorem closing_matrix_measure_apply (P : SourcePVM H) (J : S →ₗᵢ[ℂ] H)
    (b : OrthonormalBasis ι ℂ S) {U : Set ℝ} (hU : MeasurableSet U) (i j : ι) :
    closingMatrixSpectralMeasure P J b i j U =
      ⟪b i, closingSpectralCompression P J U (b j)⟫_ℂ := by
  simp only [closingMatrixSpectralMeasure, UV.ContinuationBoundary.overlapMeasure_apply _ _ _ hU,
    closingSpectralCompression, coe_comp', Function.comp_apply, adjoint_inner_right]
  rfl

theorem closing_matrix_measure_univ [DecidableEq ι] (P : SourcePVM H) (J : S →ₗᵢ[ℂ] H)
    (b : OrthonormalBasis ι ℂ S) :
    (fun i j => closingMatrixSpectralMeasure P J b i j univ : Matrix ι ι ℂ) = (1 : Matrix ι ι ℂ) := by
  ext i j
  change closingMatrixSpectralMeasure P J b i j univ = (1 : Matrix ι ι ℂ) i j
  rw [closing_matrix_measure_apply P J b MeasurableSet.univ,
    closing_spectral_compression_univ, ContinuousLinearMap.one_apply]
  simpa only [Matrix.one_apply] using (orthonormal_iff_ite.mp b.orthonormal) i j

end Slots

def closingSignedDiagonal (P : SourcePVM H) (x : H) : SignedMeasure ℝ :=
  (UV.ContinuationBoundary.overlapMeasure (closingDisplacementPVM P) x x).re

theorem closing_signed_diagonal_apply (P : SourcePVM H) (x : H) {U : Set ℝ}
    (hU : MeasurableSet U) : closingSignedDiagonal P x U = ‖P.projection U x‖ ^ 2 := by
  change (UV.ContinuationBoundary.overlapMeasure (closingDisplacementPVM P) x x U).re = _
  rw [UV.ContinuationBoundary.overlapMeasure_apply _ _ _ hU]
  change (⟪x, P.projection U x⟫_ℂ).re = _
  rw [closing_projection_inner_self P hU, Complex.ofReal_re]

open VectorMeasure in
private theorem closing_signed_diagonal_nonneg (P : SourcePVM H) (x : H) :
    0 ≤[univ] closingSignedDiagonal P x := by
  apply (le_restrict_univ_iff_le _ _).2
  intro U hU
  rw [VectorMeasure.zero_apply, closing_signed_diagonal_apply P x hU]
  positivity

/-- The positive scalar energy measure of an honest Hilbert vector. -/
def closingSpectralDiagonal (P : SourcePVM H) (x : H) : Measure ℝ :=
  (closingSignedDiagonal P x).toMeasureOfZeroLE univ MeasurableSet.univ
    (closing_signed_diagonal_nonneg P x)

theorem closing_spectral_diagonal_apply (P : SourcePVM H) (x : H) {U : Set ℝ}
    (hU : MeasurableSet U) : closingSpectralDiagonal P x U = ENNReal.ofReal (‖P.projection U x‖ ^ 2) := by
  have hf : closingSpectralDiagonal P x U ≠ ∞ := by
    unfold closingSpectralDiagonal
    rw [SignedMeasure.toMeasureOfZeroLE_apply _ _ _ hU]
    exact ENNReal.coe_ne_top
  rw [← ENNReal.ofReal_toReal hf]
  congr 1
  change (closingSpectralDiagonal P x).real U = _
  unfold closingSpectralDiagonal
  rw [SignedMeasure.toMeasureOfZeroLE_real_apply _ _ _ hU, univ_inter,
    closing_signed_diagonal_apply P x hU]

theorem closing_spectral_diagonal_mass (P : SourcePVM H) (x : H) :
    closingSpectralDiagonal P x univ = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [closing_spectral_diagonal_apply _ _ MeasurableSet.univ, P.univ, ContinuousLinearMap.one_apply]

instance (P : SourcePVM H) (x : H) : IsFiniteMeasure (closingSpectralDiagonal P x) :=
  ⟨by rw [closing_spectral_diagonal_mass]; exact ENNReal.ofReal_lt_top⟩

end UV.SectorPlane
