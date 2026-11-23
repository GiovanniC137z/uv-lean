import UV.ContinueNaimarkCompression

/-! Naimark dilation of a normalized finite-slot positive matrix measure
on the signed real energy axis. -/

noncomputable section
open MeasureTheory Set Matrix
open scoped InnerProductSpace
namespace UV.SectorPlane

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [NormedAddCommGroup S] [InnerProductSpace ℂ S]

abbrev ClosingNormalizedMatrixMeasure (M : Matrix ι ι (ComplexMeasure ℝ)) : Prop :=
  (fun i j => M i j univ) = (1 : Matrix ι ι ℂ)

def closingNaimarkLift (M : Matrix ι ι (ComplexMeasure ℝ)) (hM : ClosingPositiveMatrixMeasure M)
    (hn : ClosingNormalizedMatrixMeasure M) (b : OrthonormalBasis ι ℂ S) :
    S →ₗᵢ[ℂ] Lp ℂ 2 (closingNaimarkMeasure M) := by
  let L := b.toBasis.constr ℂ (closingNaimarkColumn M hM)
  apply L.isometryOfOrthonormal (v := b.toBasis) b.orthonormal
  have he : L ∘ b.toBasis = closingNaimarkColumn M hM := funext (b.toBasis.constr_basis ℂ _)
  rw [he]
  exact closing_columns_orthonormal M hM hn

theorem closing_naimark_lift_basis (M : Matrix ι ι (ComplexMeasure ℝ)) (hM : ClosingPositiveMatrixMeasure M)
    (hn : ClosingNormalizedMatrixMeasure M) (b : OrthonormalBasis ι ℂ S) (i : ι) :
    closingNaimarkLift M hM hn b (b i) = closingNaimarkColumn M hM i :=
  b.toBasis.constr_basis ℂ _ i

variable [CompleteSpace S]

/-- Equality of complex measures themselves on every entry. No discrete
support, scalar form of the weights, or density with respect to Lebesgue
measure is needed. -/
theorem closing_naimark_matrix_measure (M : Matrix ι ι (ComplexMeasure ℝ))
    (hM : ClosingPositiveMatrixMeasure M) (hn : ClosingNormalizedMatrixMeasure M)
    (b : OrthonormalBasis ι ℂ S) :
    closingMatrixSpectralMeasure (closingNaimarkPVM M) (closingNaimarkLift M hM hn b) b = M := by
  ext i j s hs : 3
  change closingMatrixSpectralMeasure _ _ _ i j s = M i j s
  rw [closing_matrix_measure_apply _ _ _ hs]
  simp only [closingSpectralCompression, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, LinearIsometry.coe_toContinuousLinearMap,
    closing_naimark_lift_basis]
  exact closing_column_projected_pairing M hM i j hs

end UV.SectorPlane
