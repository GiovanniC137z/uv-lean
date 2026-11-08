import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

noncomputable section
open scoped InnerProductSpace

namespace UV

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- The kinetic operator obtained by transporting a quadratic action through
an actual invertible field map. -/
def fieldTransportedKinetic (T : E ≃L[ℝ] E) (K : E →L[ℝ] E) : E →L[ℝ] E :=
  T.toContinuousLinearMap.adjoint.comp (K.comp T.toContinuousLinearMap)

theorem fieldTransportedKinetic_quadratic (T : E ≃L[ℝ] E) (K : E →L[ℝ] E) (φ : E) :
    ⟪φ, fieldTransportedKinetic T K φ⟫_ℝ = ⟪T φ, K (T φ)⟫_ℝ := by
  exact ContinuousLinearMap.adjoint_inner_right T.toContinuousLinearMap φ (K (T φ))

/-- The inverse-square damping carried by a pure field redefinition. -/
def fieldDamping (T : E ≃L[ℝ] E) : E →L[ℝ] E :=
  T.symm.toContinuousLinearMap.comp T.symm.toContinuousLinearMap

/- The two endpoint factors cancel the inverse-square damping whenever the
original covariance commutes with the field map. -/
omit [FiniteDimensional ℝ E] in
theorem fieldDamping_endpoint_cancellation (T : E ≃L[ℝ] E) (Δ : E →L[ℝ] E)
    (hcomm : Δ.comp T.toContinuousLinearMap = T.toContinuousLinearMap.comp Δ) :
    (T.toContinuousLinearMap.comp ((fieldDamping T).comp Δ)).comp
      T.toContinuousLinearMap = Δ := by
  ext φ
  change T (T.symm (T.symm (Δ (T φ)))) = Δ φ
  rw [T.apply_symm_apply]
  have hh := congrArg (fun A : E →L[ℝ] E => A φ) hcomm
  change Δ (T φ) = T (Δ φ) at hh
  rw [hh, T.symm_apply_apply]

/-- The general transported covariance uses the inverse and inverse adjoint;
no self-adjointness or commutation premise is needed. -/
def fieldTransportedCovariance (T : E ≃L[ℝ] E) (Δ : E →L[ℝ] E) : E →L[ℝ] E :=
  T.symm.toContinuousLinearMap.comp (Δ.comp T.symm.toContinuousLinearMap.adjoint)

theorem fieldTransportedCovariance_endpoint_cancellation
    (T : E ≃L[ℝ] E) (Δ : E →L[ℝ] E) :
    (T.toContinuousLinearMap.comp (fieldTransportedCovariance T Δ)).comp
      T.toContinuousLinearMap.adjoint = Δ := by
  have hadj : T.symm.toContinuousLinearMap.adjoint.comp T.toContinuousLinearMap.adjoint =
      ContinuousLinearMap.id ℝ E := by
    rw [← ContinuousLinearMap.adjoint_comp, ContinuousLinearEquiv.coe_comp_coe_symm,
      ContinuousLinearMap.adjoint_id]
  ext φ
  change T (T.symm (Δ (T.symm.toContinuousLinearMap.adjoint
    (T.toContinuousLinearMap.adjoint φ)))) = Δ φ
  rw [T.apply_symm_apply]
  have hh := congrArg (fun A : E →L[ℝ] E => A φ) hadj
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using congrArg Δ hh

end UV
