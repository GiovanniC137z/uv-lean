import UV.AnalyticScalar
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! Rotational invariance of the actual real scalar comparison integral. -/

noncomputable section
open MeasureTheory

namespace UV

theorem scalarCovariance_linearIsometry (a M m : ℝ)
    (R : ScalarMomentum ≃ₗᵢ[ℝ] ScalarMomentum) (q : ScalarMomentum) :
    scalarCovariance a M m (R q) = scalarCovariance a M m q := by
  simp only [scalarCovariance, R.norm_map]

theorem scalarBubble_linearIsometry (a M m : ℝ)
    (R : ScalarMomentum ≃ₗᵢ[ℝ] ScalarMomentum) (P : ScalarMomentum) :
    scalarBubble a M m (R P) = scalarBubble a M m P := by
  unfold scalarBubble
  congr 1
  have he := R.measurePreserving.integral_comp
    R.toHomeomorph.measurableEmbedding (scalarBubbleIntegrand a M m (R P))
  rw [← he]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  simp only [scalarBubbleIntegrand, ← R.map_add, scalarCovariance_linearIsometry]

/-- Equal-norm momenta are related by an explicitly constructed reflection,
including coincident or zero vectors. -/
theorem scalarBubble_eq_of_norm_eq (a M m : ℝ) {P Q : ScalarMomentum}
    (hPQ : ‖P‖ = ‖Q‖) : scalarBubble a M m P = scalarBubble a M m Q := by
  let R : ScalarMomentum ≃ₗᵢ[ℝ] ScalarMomentum :=
    (Submodule.span ℝ {P - Q})ᗮ.reflection
  have hR : R P = Q := Submodule.reflection_sub hPQ
  rw [← hR, scalarBubble_linearIsometry]

def scalarAxis (r : ℝ) : ScalarMomentum := EuclideanSpace.single 0 r

theorem scalarAxis_norm (r : ℝ) : ‖scalarAxis r‖ = |r| := by
  simp only [scalarAxis, EuclideanSpace.norm_single, Real.norm_eq_abs]

theorem scalarBubble_axis_reduction (a M m : ℝ) (P : ScalarMomentum) :
    scalarBubble a M m P = scalarBubble a M m (scalarAxis ‖P‖) := by
  apply scalarBubble_eq_of_norm_eq
  rw [scalarAxis_norm, abs_of_nonneg (norm_nonneg P)]

theorem scalarBubble_axis_even (a M m r : ℝ) :
    scalarBubble a M m (scalarAxis (-r)) = scalarBubble a M m (scalarAxis r) := by
  apply scalarBubble_eq_of_norm_eq
  simp only [scalarAxis_norm, abs_neg]

end UV
