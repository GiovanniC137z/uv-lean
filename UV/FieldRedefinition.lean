import UV.GlobalConvergence
import UV.FieldRedefinitionAlgebra

/-! Exact finite-mode change of field coordinates.  The integration measure is
an actual finite-dimensional real Haar measure; the normalization domain is
stated explicitly rather than inferred from a formal path integral. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace UV

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Undamped finite-mode action with an arbitrary real interaction and the
physical source paired with the physical field. -/
def finiteFieldAction (K : E →L[ℝ] E) (V : E → ℝ) (J χ : E) : ℝ :=
  (1 / 2 : ℝ) * ⟪χ, K χ⟫_ℝ + V χ - ⟪J, χ⟫_ℝ

def finiteFieldWeight (K : E →L[ℝ] E) (V : E → ℝ) (J χ : E) : ℝ :=
  Real.exp (-finiteFieldAction K V J χ)

/-- All three terms are transported together: kinetic form, interaction, and
source pairing. -/
def transportedFieldAction (T : E ≃L[ℝ] E) (K : E →L[ℝ] E)
    (V : E → ℝ) (J φ : E) : ℝ :=
  (1 / 2 : ℝ) * ⟪φ, fieldTransportedKinetic T K φ⟫_ℝ + V (T φ) - ⟪J, T φ⟫_ℝ

def transportedFieldWeight (T : E ≃L[ℝ] E) (K : E →L[ℝ] E)
    (V : E → ℝ) (J φ : E) : ℝ :=
  Real.exp (-transportedFieldAction T K V J φ)

theorem transportedFieldAction_eq (T : E ≃L[ℝ] E) (K : E →L[ℝ] E)
    (V : E → ℝ) (J φ : E) :
    transportedFieldAction T K V J φ = finiteFieldAction K V J (T φ) := by
  unfold transportedFieldAction finiteFieldAction
  rw [fieldTransportedKinetic_quadratic]

theorem transportedFieldWeight_eq (T : E ≃L[ℝ] E) (K : E →L[ℝ] E)
    (V : E → ℝ) (J φ : E) :
    transportedFieldWeight T K V J φ = finiteFieldWeight K V J (T φ) := by
  unfold transportedFieldWeight finiteFieldWeight
  rw [transportedFieldAction_eq]

/-- The Jacobian of χ=Tφ, derived from the actual finite linear equivalence. -/
def finiteFieldJacobian (T : E ≃L[ℝ] E) : ℝ := |LinearMap.det T.toLinearMap|

omit [FiniteDimensional ℝ E] in
theorem finiteFieldJacobian_pos (T : E ≃L[ℝ] E) : 0 < finiteFieldJacobian T := by
  unfold finiteFieldJacobian
  exact abs_pos.mpr T.toLinearEquiv.isUnit_det'.ne_zero


variable [MeasurableSpace E] [BorelSpace E]

def finiteFieldPartition (μ : Measure E) (K : E →L[ℝ] E)
    (V : E → ℝ) (J : E) : ℝ := ∫ χ, finiteFieldWeight K V J χ ∂μ

def transportedFieldPartition (μ : Measure E) (T : E ≃L[ℝ] E)
    (K : E →L[ℝ] E) (V : E → ℝ) (J : E) : ℝ :=
  ∫ φ, transportedFieldWeight T K V J φ ∂μ


def jacobianFieldPartition (μ : Measure E) (T : E ≃L[ℝ] E)
    (K : E →L[ℝ] E) (V : E → ℝ) (J : E) : ℝ :=
  finiteFieldJacobian T * transportedFieldPartition μ T K V J

def finiteFieldNormalized (μ : Measure E) (K : E →L[ℝ] E)
    (V : E → ℝ) (J : E) : ℝ :=
  finiteFieldPartition μ K V J / finiteFieldPartition μ K V 0

def transportedFieldNormalized (μ : Measure E) (T : E ≃L[ℝ] E)
    (K : E →L[ℝ] E) (V : E → ℝ) (J : E) : ℝ :=
  jacobianFieldPartition μ T K V J / jacobianFieldPartition μ T K V 0

variable (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem transportedFieldWeight_integrable (T : E ≃L[ℝ] E) (K : E →L[ℝ] E)
    (V : E → ℝ) (J : E) (hJ : Integrable (finiteFieldWeight K V J) μ) :
    Integrable (transportedFieldWeight T K V J) μ := by
  have h := routing_integrable μ T 0 hJ
  simpa only [add_zero, ← transportedFieldWeight_eq] using h

theorem transportedFieldPartition_jacobian (T : E ≃L[ℝ] E) (K : E →L[ℝ] E)
    (V : E → ℝ) (J : E) :
    transportedFieldPartition μ T K V J =
      |(LinearMap.det T.toLinearMap)⁻¹| * finiteFieldPartition μ K V J := by
  unfold transportedFieldPartition finiteFieldPartition
  simpa only [add_zero, ← transportedFieldWeight_eq] using
    routing_integral μ T 0 (finiteFieldWeight K V J)

theorem jacobianFieldPartition_eq (T : E ≃L[ℝ] E) (K : E →L[ℝ] E)
    (V : E → ℝ) (J : E) :
    jacobianFieldPartition μ T K V J = finiteFieldPartition μ K V J := by
  unfold jacobianFieldPartition finiteFieldJacobian
  rw [transportedFieldPartition_jacobian, abs_inv, ← mul_assoc,
    mul_inv_cancel₀ (abs_ne_zero.mpr T.toLinearEquiv.isUnit_det'.ne_zero), one_mul]

/-- Cancellation of the field- and source-independent determinant in the
normalized source functional, before including it explicitly in the measure. -/
theorem transportedFieldPartition_ratio (T : E ≃L[ℝ] E) (K : E →L[ℝ] E)
    (V : E → ℝ) (J : E) :
    transportedFieldPartition μ T K V J / transportedFieldPartition μ T K V 0 =
      finiteFieldNormalized μ K V J := by
  rw [transportedFieldPartition_jacobian, transportedFieldPartition_jacobian]
  unfold finiteFieldNormalized
  exact mul_div_mul_left _ _ (abs_ne_zero.mpr
    (inv_ne_zero T.toLinearEquiv.isUnit_det'.ne_zero))

/-- The manuscript's finite-mode proposition, on the explicit domain where
both partition integrals exist and the zero-source normalization is nonzero. -/
theorem pure_field_redefinition_cancellation (T : E ≃L[ℝ] E) (K : E →L[ℝ] E)
    (V : E → ℝ) (J : E)
    (hJ : Integrable (finiteFieldWeight K V J) μ)
    (h0 : Integrable (finiteFieldWeight K V 0) μ)
    (hZ0 : finiteFieldPartition μ K V 0 ≠ 0) :
    Integrable (transportedFieldWeight T K V J) μ ∧
      Integrable (transportedFieldWeight T K V 0) μ ∧
      jacobianFieldPartition μ T K V 0 ≠ 0 ∧
      transportedFieldNormalized μ T K V J = finiteFieldNormalized μ K V J := by
  refine ⟨transportedFieldWeight_integrable μ T K V J hJ,
    transportedFieldWeight_integrable μ T K V 0 h0, ?_, ?_⟩
  · rw [jacobianFieldPartition_eq]
    exact hZ0
  · unfold transportedFieldNormalized finiteFieldNormalized
    rw [jacobianFieldPartition_eq, jacobianFieldPartition_eq]

end UV
