import UV.ContinueRelativeSoftHessian
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! The four-momentum trace and the exact radial measure of the soft response. -/

noncomputable section

namespace UV.RelativeSoft

open UV.SectorPlane MeasureTheory Set Real
open scoped RealInnerProductSpace

local instance : MeasurableSpace EuclideanPlaneMomentum := borel _
local instance : BorelSpace EuclideanPlaneMomentum := ⟨rfl⟩

theorem soft_momentum_finrank : Module.finrank ℝ EuclideanPlaneMomentum = 4 := by
  rw [(WithLp.linearEquiv 2 ℝ (ℝ × Spatial)).finrank_eq,Module.finrank_prod]
  simp [Spatial]

private def splitAlong (u : ConeUnitDirection) (t r : ℝ) :
    Module.End ℝ EuclideanPlaneMomentum :=
  let P := (longitudinalProjection u).toLinearMap
  t • (1-P) + r • P

private theorem split_along_trace (u : ConeUnitDirection) (t r : ℝ) :
    LinearMap.trace ℝ EuclideanPlaneMomentum (splitAlong u t r) = 3*t+r := by
  have hp : LinearMap.trace ℝ EuclideanPlaneMomentum (longitudinalProjection u).toLinearMap = 1 := by
    change LinearMap.trace ℝ EuclideanPlaneMomentum ((innerSL ℝ u.val).toLinearMap.smulRight u.val) = 1
    rw [LinearMap.trace_smulRight,ContinuousLinearMap.coe_coe,innerSL_apply,
      real_inner_self_eq_norm_sq,u.property,one_pow]
  simp only [splitAlong,map_add,map_sub,map_smul,LinearMap.trace_one,soft_momentum_finrank,hp,
    Nat.cast_ofNat,smul_eq_mul,mul_one]
  ring

private theorem split_along_sub (u : ConeUnitDirection) (t r t' r' : ℝ) :
    splitAlong u t r - splitAlong u t' r' = splitAlong u (t-t') (r-r') := by
  simp only [splitAlong,sub_smul]
  abel

private theorem split_along_mul (u : ConeUnitDirection) (t r t' r' : ℝ) :
    splitAlong u t r * splitAlong u t' r' = splitAlong u (t*t') (r*r') := by
  let P := (longitudinalProjection u).toLinearMap
  let Q : Module.End ℝ EuclideanPlaneMomentum := 1-P
  have h : P*P = P := LinearMap.ext (longitudinal_projection_idempotent u)
  have hQP : Q*P = 0 := by
    simp only [Q,sub_mul,one_mul,h,sub_self]
  have hPQ : P*Q = 0 := by
    simp only [Q,mul_sub,mul_one,h,sub_self]
  have hQQ : Q*Q = Q := by
    rw [show Q*Q = Q*(1-P) by rfl,mul_sub,mul_one,hQP,sub_zero]
  change (t • Q + r • P)*(t' • Q + r' • P) = (t*t') • Q + (r*r') • P
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,hQQ,hQP,hPQ,h,smul_zero,zero_add,add_zero,smul_smul,mul_comm t' t,mul_comm r' r]

private theorem soft_outer_eq_projection {k : EuclideanPlaneMomentum} (hk : k ≠ 0) :
    (softOuter k).toLinearMap = ‖k‖^2 • (longitudinalProjection (euclideanMomentumUnit k hk)).toLinearMap := by
  ext v
  change inner ℝ k v • k = ‖k‖^2 • (inner ℝ (‖k‖⁻¹ • k) v • (‖k‖⁻¹ • k))
  rw [real_inner_smul_left]
  simp_rw [smul_smul]
  congr 1
  have h := norm_ne_zero_iff.mpr hk
  field_simp

private theorem soft_chord_split (σ : ℝ) {k : EuclideanPlaneMomentum} (hk : k ≠ 0) :
    (softChordDifferential σ k).toLinearMap = splitAlong (euclideanMomentumUnit k hk)
      (tangentialChord (σ^2*‖k‖^2)) (radialChord (σ^2*‖k‖^2)) := by
  let g := Real.exp (-(σ^2*‖k‖^2))
  change g • 1 - (2*σ^2*g) • (softOuter k).toLinearMap = _
  rw [soft_outer_eq_projection hk]
  simp only [splitAlong,tangentialChord,radialChord,smul_sub,smul_smul]
  change g • 1 - _ = g • 1 - _ + _
  module

private theorem soft_log_split (m : ℝ) {k : EuclideanPlaneMomentum} (hk : k ≠ 0) :
    (softLogHessian m k).toLinearMap = splitAlong (euclideanMomentumUnit k hk)
      (4/(m^2+‖k‖^2)) (4*(m^2-‖k‖^2)/(m^2+‖k‖^2)^2) := by
  let d := m^2+‖k‖^2
  change (4/d) • 1 - (8/d^2) • (softOuter k).toLinearMap = _
  rw [soft_outer_eq_projection hk]
  have hh : d ≠ 0 := by dsimp [d]; positivity
  have he : 4*(m^2-‖k‖^2)/d^2 = 4/d - (8/d^2)*‖k‖^2 := by
    field_simp
    dsimp [d]
    ring
  change (4/d) • 1 - (8/d^2) • (‖k‖^2 • _) = (4/d) • (1-_) + (4*(m^2-‖k‖^2)/d^2) • _
  rw [he]
  module

def softCartesianTrace (m σ : ℝ) (k : EuclideanPlaneMomentum) : ℝ :=
  let D := (softChordDifferential σ k).toLinearMap
  let H := (softLogHessian m k).toLinearMap
  LinearMap.trace ℝ EuclideanPlaneMomentum (H*(D^2-D))

/-- The three tangential and one normalized radial contributions to the original trace. -/
def softTraceAtRadius (m σ r : ℝ) : ℝ :=
  3*(4/(m^2+r^2))*tangentialDifference (σ^2*r^2) +
    (4*(m^2-r^2)/(m^2+r^2)^2)*radialDifference (σ^2*r^2)

theorem soft_cartesian_trace_eq_radial (m σ : ℝ) {k : EuclideanPlaneMomentum} (hk : k ≠ 0) :
    softCartesianTrace m σ k = softTraceAtRadius m σ ‖k‖ := by
  simp only [softCartesianTrace,soft_chord_split σ hk,soft_log_split m hk,pow_two,
    split_along_mul,split_along_sub,split_along_trace,softTraceAtRadius,
    tangentialDifference,radialDifference]
  ring

def softCartesianLinearTrace (m σ : ℝ) (k : EuclideanPlaneMomentum) : ℝ :=
  LinearMap.trace ℝ EuclideanPlaneMomentum
    ((softLogHessian m k).toLinearMap * (softChordDifferential σ k).toLinearMap)

def softLinearTraceAtRadius (m σ r : ℝ) : ℝ :=
  3*(4/(m^2+r^2))*tangentialChord (σ^2*r^2) +
    (4*(m^2-r^2)/(m^2+r^2)^2)*radialChord (σ^2*r^2)

theorem soft_cartesian_linear_eq_radial (m σ : ℝ) {k : EuclideanPlaneMomentum} (hk : k ≠ 0) :
    softCartesianLinearTrace m σ k = softLinearTraceAtRadius m σ ‖k‖ := by
  simp only [softCartesianLinearTrace,soft_chord_split σ hk,soft_log_split m hk,
    split_along_mul,split_along_trace,softLinearTraceAtRadius]
  ring

theorem soft_four_volume_radial (f : ℝ → ℝ) :
    (∫ k : EuclideanPlaneMomentum, f ‖k‖) = 2*π^2 * ∫ r in Ioi (0:ℝ), r^3*f r := by
  rw [integral_fun_norm_addHaar volume,soft_momentum_finrank,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,Measure.real,InnerProductSpace.volume_ball_of_dim_even (k := 2) (by rw [soft_momentum_finrank])]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, Nat.factorial_succ, Nat.factorial_zero,
    Nat.mul_one, Nat.cast_ofNat,
    smul_eq_mul, show (4:ℕ)-1=3 by decide]
  rw [ENNReal.toReal_ofReal]
  · ring
  · positivity

theorem squared_radius_image {σ : ℝ} (hσ : 0 < σ) :
    (fun r : ℝ => σ^2*r^2) '' Ioi 0 = Ioi 0 := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    have : 0 < r := hr
    exact mem_Ioi.mpr (by positivity)
  · intro hy
    have h : 0 < y := hy
    refine ⟨√(y/σ^2), mem_Ioi.mpr (by positivity), ?_⟩
    change σ^2 * (√(y/σ^2))^2 = y
    rw [Real.sq_sqrt (by positivity)]
    field_simp

theorem squared_radius_injective {σ : ℝ} (hσ : 0 < σ) :
    InjOn (fun r : ℝ => σ^2*r^2) (Ioi 0) := by
  intro r hr t ht h
  have h₁ : 0 < r := hr
  have h₂ : 0 < t := ht
  have hs := mul_left_cancel₀ (pow_ne_zero 2 hσ.ne') h
  nlinarith

theorem squared_radius_derivative (σ : ℝ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => σ^2*r^2) (2*σ^2*r) r := by
  convert (hasDerivAt_pow 2 r).const_mul (σ^2) using 1
  ring

private theorem radial_trace_density (m : ℝ) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    r^3*softTraceAtRadius m σ r =
      (2/σ^2)*(|2*σ^2*r| • softShapeIntegrand (m*σ) (σ^2*r^2)) := by
  have hd : m^2+r^2 ≠ 0 := by positivity
  have hh : (m*σ)^2+σ^2*r^2 ≠ 0 := by positivity
  rw [abs_of_pos (by positivity),smul_eq_mul,softTraceAtRadius,softShapeIntegrand]
  field_simp
  ring

private theorem radial_trace_integral (m : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (∫ r in Ioi (0:ℝ), r^3*softTraceAtRadius m σ r) = (2/σ^2)*relativeSoftShape (m*σ) := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun r _ => (squared_radius_derivative σ r).hasDerivWithinAt)
    (squared_radius_injective hσ) (softShapeIntegrand (m*σ))
  rw [squared_radius_image hσ] at h
  change relativeSoftShape (m*σ) = _ at h
  rw [h,← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun _ hr => radial_trace_density m hσ hr

private theorem radial_trace_integrable (m : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun r => r^3*softTraceAtRadius m σ r) (Ioi 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun r _ => (squared_radius_derivative σ r).hasDerivWithinAt)
    (squared_radius_injective hσ) (softShapeIntegrand (m*σ))
  rw [squared_radius_image hσ] at h
  refine ((h.mp (soft_shape_integrable (m*σ))).const_mul (2/σ^2)).congr ?_
  exact (ae_restrict_mem measurableSet_Ioi).mono fun _ hr => (radial_trace_density m hσ hr).symm

private theorem cartesian_trace_radial_ae (m σ : ℝ) :
    softCartesianTrace m σ =ᵐ[(volume : Measure EuclideanPlaneMomentum)]
      (fun k => softTraceAtRadius m σ ‖k‖) := by
  have h : ∀ᵐ k ∂(volume : Measure EuclideanPlaneMomentum), k ≠ 0 :=
    ae_iff.mpr (by simpa only [not_ne_iff, setOf_eq_eq_singleton] using
      (measure_singleton (μ := (volume : Measure EuclideanPlaneMomentum)) (0 : EuclideanPlaneMomentum)))
  exact h.mono fun _ hk => soft_cartesian_trace_eq_radial m σ hk

theorem soft_cartesian_trace_integrable (m : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (softCartesianTrace m σ) := by
  apply Integrable.congr _ (cartesian_trace_radial_ae m σ).symm
  apply (integrable_fun_norm_addHaar volume).mpr
  simpa only [soft_momentum_finrank,show (4:ℕ)-1=3 by decide,smul_eq_mul] using
    radial_trace_integrable m hσ

/-- The literal four-momentum Hessian trace gives the response with the manuscript's
Fourier normalization, for every positive width. -/
theorem soft_cartesian_response_eq (e m : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (e^2/4) * ((∫ k : EuclideanPlaneMomentum, softCartesianTrace m σ k) / (2*π)^4) =
      relativeSoftResponse e m σ := by
  rw [integral_congr_ae (cartesian_trace_radial_ae m σ),soft_four_volume_radial,
    radial_trace_integral m hσ,relativeSoftResponse]
  have hp := Real.pi_ne_zero
  field_simp
  ring

end UV.RelativeSoft
