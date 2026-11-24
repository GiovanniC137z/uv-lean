import UV.ContinueTwoBandFourierSlab
import UV.ContinueTwoBandFourierKernel

/-! Both one-sided kernels define Hilbert–Schmidt slab operators. -/

noncomputable section
open MeasureTheory

namespace UV.SectorPlane

def twoBandBoundedSlabHop (upper : Bool) {A : TwoBandPoint → Spatial →L[ℝ] ℝ} (hA : Continuous A)
    {φ : TwoBandPoint → ℝ} (hφ : Continuous φ) {m : ℝ} (hm : 0 ≤ m) (q g : ℝ)
    {σ L₁ L₂ L₃ : ℝ} (hσ : 0 < σ) (h₁ : 0 < L₁) (h₂ : 0 < L₂) (h₃ : 0 < L₃) :
    SlabKernel.Bounded TwoBandPoint where
  val := twoBandSlabHopKernel upper A φ m q g σ L₁ L₂ L₃
  measurable := twoBand_slab_hop_measurable upper hA hφ m q g hσ h₁ h₂ h₃
  bound := (twoBand_slab_hop_bound upper A φ hm q g hσ h₁ h₂ h₃).choose
  nonneg := (twoBand_slab_hop_bound upper A φ hm q g hσ h₁ h₂ h₃).choose_spec.1
  bounded := (twoBand_slab_hop_bound upper A φ hm q g hσ h₁ h₂ h₃).choose_spec.2

def twoBandSlabOperator (upper : Bool) (T : ℝ)
    {A : TwoBandPoint → Spatial →L[ℝ] ℝ} (hA : Continuous A)
    {φ : TwoBandPoint → ℝ} (hφ : Continuous φ) {m : ℝ} (hm : 0 ≤ m) (q g : ℝ)
    {σ L₁ L₂ L₃ : ℝ} (hσ : 0 < σ) (h₁ : 0 < L₁) (h₂ : 0 < L₂) (h₃ : 0 < L₃) :=
  SlabKernel.operator (twoBandSlabMeasure T L₁ L₂ L₃) (twoBandBoundedSlabHop upper hA hφ hm q g hσ h₁ h₂ h₃)

theorem twoBand_slab_operator_hilbert_schmidt (upper : Bool) (T : ℝ)
    {A : TwoBandPoint → Spatial →L[ℝ] ℝ} (hA : Continuous A)
    {φ : TwoBandPoint → ℝ} (hφ : Continuous φ) {m : ℝ} (hm : 0 ≤ m) (q g : ℝ)
    {σ L₁ L₂ L₃ : ℝ} (hσ : 0 < σ) (h₁ : 0 < L₁) (h₂ : 0 < L₂) (h₃ : 0 < L₃)
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 (twoBandSlabMeasure T L₁ L₂ L₃))) :
    Summable (fun i => ‖twoBandSlabOperator upper T hA hφ hm q g hσ h₁ h₂ h₃ (b i)‖^2) :=
  SlabKernel.operator_square_columns _ _ b

end UV.SectorPlane
