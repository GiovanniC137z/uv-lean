import UV.ContinueTwoBandFourierOperator
import UV.ContinueTwoBandFourierRankOne

/-! The trace-class rank-one expansion on the symmetric slab. -/

noncomputable section
open MeasureTheory

namespace UV.SectorPlane

/-- The two one-sided slab blocks form a genuine nuclear product on
complex L². The sum of rank-one trace norms converges and its operator
sum is the full uncut Schur product. -/
theorem twoBand_slab_schur_product_nuclear (T : ℝ)
    {A : TwoBandPoint → Spatial →L[ℝ] ℝ} (hA : Continuous A)
    {φ : TwoBandPoint → ℝ} (hφ : Continuous φ) {m : ℝ} (hm : 0 ≤ m) (q g : ℝ)
    {σ L₁ L₂ L₃ : ℝ} (hσ : 0 < σ) (h₁ : 0 < L₁) (h₂ : 0 < L₂) (h₃ : 0 < L₃)
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 (twoBandSlabMeasure T L₁ L₂ L₃))) :
    let Apos := twoBandSlabOperator true T hA hφ hm q g hσ h₁ h₂ h₃
    let Aneg := twoBandSlabOperator false T hA hφ hm q g hσ h₁ h₂ h₃
    Summable (fun i => ‖Apos.adjoint (b i)‖*‖Aneg (b i)‖) ∧
      HasSum (fun i => (innerSL ℂ (Apos.adjoint (b i))).smulRight (Aneg (b i))) (Aneg.comp Apos) :=
  SlabKernel.nuclear_product b _ _ (twoBand_slab_operator_hilbert_schmidt true T hA hφ hm q g hσ h₁ h₂ h₃ b)
    (twoBand_slab_operator_hilbert_schmidt false T hA hφ hm q g hσ h₁ h₂ h₃ b)

end UV.SectorPlane
