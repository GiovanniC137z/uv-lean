import UV.ContinueSourceReviewSchurResolvent
import UV.UnboundedSource

/-! The explicit pointwise Cauchy kernel of the real multiplication
dilation at every nonreal frequency on the locked sector plane. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace UV.SectorPlane

variable {X : Type*} [MeasurableSpace X]

theorem closing_multiplier_resolvent_ae (μ : Measure X) (w : X → ℝ) (z : ℂ) (hz : z.im ≠ 0)
    (R : ClosingUnboundedResolvent (UV.sourceL2Multiplier μ (fun x => (w x:ℂ))) z) (ψ : Lp ℂ 2 μ) :
    (R.map ψ : X → ℂ) =ᵐ[μ] fun x => (z + (w x:ℂ))⁻¹ * ψ x := by
  let K := UV.sourceL2Multiplier μ (fun x => (w x:ℂ))
  let v : K.domain := ⟨R.map ψ,R.inDomain ψ⟩
  filter_upwards [UV.sourceL2Multiplier_coe μ (fun x => (w x:ℂ)) v,
    Lp.coeFn_add (z • R.map ψ) (K v),Lp.coeFn_smul z (R.map ψ)] with x hK ha hzv
  have h := congrArg (fun y : Lp ℂ 2 μ => y x) (R.rightInverse ψ)
  change (z • R.map ψ + K v) x=ψ x at h
  rw [ha] at h
  change (z • R.map ψ) x + (K v) x = ψ x at h
  rw [hzv,hK] at h
  change z*(R.map ψ) x+(w x:ℂ)*(R.map ψ) x=ψ x at h
  have hn : z+(w x:ℂ) ≠ 0 := by
    intro hh
    have him := congrArg Complex.im hh
    simp at him
    exact hz him
  rw [←h,←add_mul,←mul_assoc,inv_mul_cancel₀ hn,one_mul]

/-- The bounded resolvent actually constructed from the closed graph
has the concrete spectral representation needed by the matrix measure. -/
theorem closing_coordinate_cauchy_ae (μ : Measure X) (w : X → ℝ) (hw : Measurable w)
    (z : ℂ) (hz : z.im ≠ 0) (ψ : Lp ℂ 2 μ) :
    let K := UV.sourceL2Multiplier μ (fun x => (w x:ℂ))
    let R := closingNonrealResolvent K (UV.sourceL2Multiplier_real_selfAdjoint μ w hw) z hz
    (R.map ψ : X → ℂ) =ᵐ[μ] fun x => (z+(w x:ℂ))⁻¹ * ψ x :=
  closing_multiplier_resolvent_ae μ w z hz _ ψ

end UV.SectorPlane
