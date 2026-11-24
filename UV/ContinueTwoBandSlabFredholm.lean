import UV.ContinueTwoBandFredholm
import UV.ContinueTwoBandFourierNuclear
import UV.ContinueTwoBandFourierContraction

/-! The finite-section limit for the measured onsite/Wilson product on
the source slab. Both directions carry the same spatial readout. -/

noncomputable section
open MeasureTheory Matrix Filter
open scoped Topology Matrix.Norms.L2Operator
namespace UV.SectorPlane

theorem twoBand_slab_determinant_trace_series (T : ℝ)
    {A : TwoBandPoint → Spatial →L[ℝ] ℝ} (hA : Continuous A)
    {φ : TwoBandPoint → ℝ} (hφ : Continuous φ) {m g : ℝ} (hg : |g| < m) (q : ℝ)
    {σ L₁ L₂ L₃ : ℝ} (hσ : 0 < σ) (h₁ : 0 < L₁) (h₂ : 0 < L₂) (h₃ : 0 < L₃)
    {I : Type*} [DecidableEq I] (b : HilbertBasis I ℂ (Lp ℂ 2 (twoBandSlabMeasure T L₁ L₂ L₃))) :
    let hm := (abs_nonneg g).trans hg.le
    let U := twoBandSlabOperator true T hA hφ hm q g hσ h₁ h₂ h₃
    let V := twoBandSlabOperator false T hA hφ hm q g hσ h₁ h₂ h₃
    let C := fun n : ℕ => schurCycleTrace b V U n / (n+1)
    Summable (fun n => ‖C n‖) ∧
      Tendsto (fun s : Finset I => (1-schurSection b s V * schurSection b s U).det)
        atTop (𝓝 (Complex.exp (-(∑' n, C n)))) := by
  intro hm U V C
  have hm' := (abs_nonneg g).trans_lt hg
  have hV := twoBand_slab_operator_contraction false T hA hφ hm' q g hσ h₁ h₂ h₃
  have hU := twoBand_slab_operator_contraction true T hA hφ hm' q g hσ h₁ h₂ h₃
  have hpos : 0 ≤ |g|/m := div_nonneg (abs_nonneg _) hm
  have hlt : |g|/m < 1 := (div_lt_one hm').mpr hg
  apply twoBand_hilbert_schmidt_det_limit b V U
    (SlabKernel.square_adjoint_columns b V (twoBand_slab_operator_hilbert_schmidt false T hA hφ hm q g hσ h₁ h₂ h₃ b))
    (twoBand_slab_operator_hilbert_schmidt true T hA hφ hm q g hσ h₁ h₂ h₃ b)
  exact (mul_le_mul hV hU (norm_nonneg _) hpos).trans_lt (mul_lt_one_of_nonneg_of_lt_one_left hpos hlt hlt.le)

end UV.SectorPlane
