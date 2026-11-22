import UV.SectorPlaneGaugeMultiplier
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! The flat Euclidean gauge benchmark and its separate Lorentzian sector-plane
prescription. The longitudinal projector uses the normalized momentum itself. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology RealInnerProductSpace

abbrev EuclideanPlaneMomentum := WithLp 2 (ℝ × Spatial)

def euclideanMomentumUnit (q : EuclideanPlaneMomentum) (hq : q ≠ 0) : ConeUnitDirection :=
  ⟨‖q‖⁻¹ • q, by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hq)]⟩

def longitudinalProjection (u : ConeUnitDirection) : EuclideanPlaneMomentum →L[ℝ] EuclideanPlaneMomentum :=
  (innerSL ℝ u.val).smulRight u.val

theorem longitudinal_projection_idempotent (u : ConeUnitDirection) (x : EuclideanPlaneMomentum) :
    longitudinalProjection u (longitudinalProjection u x) = longitudinalProjection u x := by
  change ⟪u.val, ⟪u.val,x⟫ • u.val⟫ • u.val = ⟪u.val,x⟫ • u.val
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq, u.property, one_pow, mul_one]

theorem longitudinal_projection_component (q : EuclideanPlaneMomentum) (hq : q ≠ 0) (u v : ConeUnitDirection) :
    ⟪u.val, longitudinalProjection (euclideanMomentumUnit q hq) v.val⟫ =
      ⟪u.val,q⟫ * ⟪v.val,q⟫ / ‖q‖^2 := by
  change ⟪u.val, ⟪‖q‖⁻¹ • q,v.val⟫ • (‖q‖⁻¹ • q)⟫ = _
  rw [real_inner_smul_right, real_inner_smul_right, real_inner_smul_left, real_inner_comm q v.val]
  ring

def gaugeProjectorSum (u : ConeUnitDirection) (ζ : ℝ) (x : EuclideanPlaneMomentum) : EuclideanPlaneMomentum :=
  x - longitudinalProjection u x + ζ • longitudinalProjection u x

private theorem longitudinal_gauge_projector_sum (u : ConeUnitDirection) (ζ : ℝ) (x : EuclideanPlaneMomentum) :
    longitudinalProjection u (gaugeProjectorSum u ζ x) = ζ • longitudinalProjection u x := by
  simp [gaugeProjectorSum, longitudinal_projection_idempotent]

theorem gauge_projector_sum_inverse (u : ConeUnitDirection) {ζ : ℝ} (hζ : ζ ≠ 0) (x : EuclideanPlaneMomentum) :
    gaugeProjectorSum u ζ⁻¹ (gaugeProjectorSum u ζ x) = x := by
  rw [gaugeProjectorSum, longitudinal_gauge_projector_sum, smul_smul, inv_mul_cancel₀ hζ, one_smul, gaugeProjectorSum]
  abel

private theorem gauge_projector_sum_smul (u : ConeUnitDirection) (ζ c : ℝ) (x : EuclideanPlaneMomentum) :
    gaugeProjectorSum u ζ (c • x) = c • gaugeProjectorSum u ζ x := by
  simp [gaugeProjectorSum, smul_add, smul_sub, smul_comm ζ c]

def euclideanGhostCoefficient (φ : ℝ → ℝ) (a : ℝ) (q : EuclideanPlaneMomentum) : ℝ := φ (a^2 * ‖q‖^2) / ‖q‖^2

def euclideanGaugeCovariance (φ : ℝ → ℝ) (a ζ : ℝ) (q : EuclideanPlaneMomentum) (hq : q ≠ 0)
    (x : EuclideanPlaneMomentum) : EuclideanPlaneMomentum :=
  euclideanGhostCoefficient φ a q • gaugeProjectorSum (euclideanMomentumUnit q hq) ζ x

def euclideanGaugeKinetic (φ : ℝ → ℝ) (a ζ : ℝ) (q : EuclideanPlaneMomentum) (hq : q ≠ 0)
    (x : EuclideanPlaneMomentum) : EuclideanPlaneMomentum :=
  (‖q‖^2 / φ (a^2 * ‖q‖^2)) • gaugeProjectorSum (euclideanMomentumUnit q hq) ζ⁻¹ x

/-- The stipulated flat Euclidean quadratic has the displayed gauge inverse and
ghost reciprocal on each nonzero mode where the kernel is invertible. -/
theorem euclidean_gauge_and_ghost_inverse (φ : ℝ → ℝ) (a : ℝ) {ζ : ℝ} (hζ : 0 < ζ)
    (q : EuclideanPlaneMomentum) (hq : q ≠ 0) (hφ : φ (a^2 * ‖q‖^2) ≠ 0) (x : EuclideanPlaneMomentum) :
    euclideanGaugeKinetic φ a ζ q hq (euclideanGaugeCovariance φ a ζ q hq x) = x ∧
    euclideanGaugeCovariance φ a ζ q hq (euclideanGaugeKinetic φ a ζ q hq x) = x ∧
    (‖q‖^2 / φ (a^2 * ‖q‖^2)) * euclideanGhostCoefficient φ a q = 1 := by
  have hh : ‖q‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hq)
  have hP := gauge_projector_sum_inverse (euclideanMomentumUnit q hq) hζ.ne' x
  have hQ := gauge_projector_sum_inverse (euclideanMomentumUnit q hq) (inv_ne_zero hζ.ne') x
  simp only [inv_inv] at hQ
  have hG : (‖q‖^2 / φ (a^2 * ‖q‖^2)) * euclideanGhostCoefficient φ a q = 1 := by
    unfold euclideanGhostCoefficient
    rw [← inv_div, inv_mul_cancel₀ (div_ne_zero hφ hh)]
  simp only [euclideanGaugeKinetic, euclideanGaugeCovariance, gauge_projector_sum_smul, smul_smul,
    hP, hQ, hG, mul_comm (euclideanGhostCoefficient φ a q), one_smul, and_self]

variable {E : Type*} [NormedAddCommGroup E]

/-- The directed lift of an arbitrary prescribed scalar function reads the first
character and embeds the value back into the actual real carrier algebra. -/
def directedProfile (φ : ℂ → ℂ) (z : QuotientCarrier) : QuotientCarrier := directed (φ (quotientCharacterEquiv z).1)

theorem Plane.gauge_directed_kinetic_data (diamond : Plane E) (ε : Evolution) (h : Height)
    (φ : ℂ → ℂ) (a w : ℝ) :
    diamond.poleDenominator ε h w = algebraMap ℂ QuotientCarrier w +
      algebraMap ℂ QuotientCarrier (Complex.I * ((diamond.eta ε * (h : ℝ) : ℝ) : ℂ)) * poleRoot ∧
    directed (diamond.scalarKernelReadout ε a φ h w) =
      directedProfile φ (directed (-(a : ℂ)^2) * diamond.poleDenominator ε h w) := by
  constructor
  · exact diamond.pole_denominator_literal ε h w
  · simp [Plane.scalarKernelReadout, directedProfile, Plane.poleDenominator, Plane.shiftedShellCoefficient, directed]

theorem Plane.ghost_template_vectorial (diamond : Plane E) (ε : Evolution) (h : Height) (φ : ℂ → ℂ)
    (a : ℝ) (q : MassiveMomentum) (hq : q.1 ≠ 0) :
    diamond.scalarLine ε h φ a 0 q.1 q.2 hq =
      directed (Complex.I * ((diamond.eta ε * axialSign q.1 : ℝ) : ℂ)) *
      directedProfile φ (directed (-(a : ℂ)^2) * diamond.poleDenominator ε h (shellSquare q.1 q.2)) *
      diamond.poleInverse ε h (shellSquare q.1 q.2) := by
  rw [← (diamond.gauge_directed_kinetic_data ε h φ a _).2]
  simp [Plane.scalarLine, Plane.scalarKernelReadout, Plane.shiftedShellCoefficient]

end UV.SectorPlane
