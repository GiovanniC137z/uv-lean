import UV.ContinueRelativeSoftDepth
import UV.SectorPlaneGaugeData
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.LinearAlgebra.Trace

/-! Actual derivatives on the fixed sector-plane Euclidean momentum chart. -/

noncomputable section

namespace UV.RelativeSoft

open UV.SectorPlane
open scoped RealInnerProductSpace

/-- The Gaussian chord on the original four-momentum, with the sector's
one axial slot and three spatial slots. -/
def softChord (σ : ℝ) (k : EuclideanPlaneMomentum) : EuclideanPlaneMomentum :=
  Real.exp (-(σ^2*‖k‖^2)) • k

def softLog (m : ℝ) (k : EuclideanPlaneMomentum) : ℝ :=
  2 * Real.log (m^2+‖k‖^2)

def softLogGradient (m : ℝ) (k : EuclideanPlaneMomentum) : EuclideanPlaneMomentum :=
  (4/(m^2+‖k‖^2)) • k

/-- The rank-one map k ⊗ k, using the plane's Euclidean pairing. -/
def softOuter (k : EuclideanPlaneMomentum) : EuclideanPlaneMomentum →L[ℝ] EuclideanPlaneMomentum :=
  (innerSL ℝ k).smulRight k

def softChordDifferential (σ : ℝ) (k : EuclideanPlaneMomentum) :
    EuclideanPlaneMomentum →L[ℝ] EuclideanPlaneMomentum :=
  let g := Real.exp (-(σ^2*‖k‖^2))
  g • ContinuousLinearMap.id ℝ _ - (2*σ^2*g) • softOuter k

def softLogHessian (m : ℝ) (k : EuclideanPlaneMomentum) :
    EuclideanPlaneMomentum →L[ℝ] EuclideanPlaneMomentum :=
  let d := m^2+‖k‖^2
  (4/d) • ContinuousLinearMap.id ℝ _ - (8/d^2) • softOuter k

theorem soft_chord_hasFDerivAt (σ : ℝ) (k : EuclideanPlaneMomentum) :
    HasFDerivAt (softChord σ) (softChordDifferential σ k) k := by
  have hu := (hasStrictFDerivAt_norm_sq k).hasFDerivAt
  have hd := ((hu.const_mul (σ^2)).neg.exp).smul
    ((ContinuousLinearMap.id ℝ EuclideanPlaneMomentum).hasFDerivAt (x := k))
  convert hd using 1
  ext v
  simp only [softChordDifferential,softOuter,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,innerSL_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.neg_apply,smul_smul,smul_eq_mul,Pi.neg_apply]
  module

theorem soft_log_hasFDerivAt (m : ℝ) (k : EuclideanPlaneMomentum)
    (hd : m^2+‖k‖^2 ≠ 0) :
    HasFDerivAt (softLog m) (innerSL ℝ (softLogGradient m k)) k := by
  have hu := (hasStrictFDerivAt_norm_sq k).hasFDerivAt
  have h := ((Real.hasDerivAt_log hd).comp_hasFDerivAt k (hu.const_add (m^2))).const_mul 2
  convert h using 1
  ext v
  simp only [softLogGradient,innerSL_apply,real_inner_smul_left,
    ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

theorem soft_log_gradient_hasFDerivAt (m : ℝ) (k : EuclideanPlaneMomentum)
    (hd : m^2+‖k‖^2 ≠ 0) :
    HasFDerivAt (softLogGradient m) (softLogHessian m k) k := by
  have hu := (hasStrictFDerivAt_norm_sq k).hasFDerivAt.const_add (m^2)
  have hi := (hasDerivAt_inv hd).comp_hasFDerivAt k hu
  have h := ((hi.const_mul 4).smul
    ((ContinuousLinearMap.id ℝ EuclideanPlaneMomentum).hasFDerivAt (x := k)))
  have hf : softLogGradient m = fun x : EuclideanPlaneMomentum => (4*(m^2+‖x‖^2)⁻¹) • x := by
    funext x
    rw [softLogGradient,div_eq_mul_inv]
  rw [hf]
  convert h using 1
  ext v
  simp only [softLogHessian,softOuter,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,innerSL_apply,ContinuousLinearMap.add_apply,
    smul_smul,smul_eq_mul,Function.comp_apply]
  module

theorem soft_outer_radial (k : EuclideanPlaneMomentum) (hk : k ≠ 0) :
    softOuter k (euclideanMomentumUnit k hk).val = ‖k‖^2 • (euclideanMomentumUnit k hk).val := by
  change ⟪k,‖k‖⁻¹ • k⟫ • k = ‖k‖^2 • (‖k‖⁻¹ • k)
  rw [real_inner_smul_right,real_inner_self_eq_norm_sq,smul_smul,mul_comm]

theorem soft_outer_tangential (k : EuclideanPlaneMomentum) (hk : k ≠ 0)
    (u : ConeUnitDirection) (hu : ⟪(euclideanMomentumUnit k hk).val,u.val⟫ = 0) :
    softOuter k u.val = 0 := by
  change ⟪‖k‖⁻¹ • k,u.val⟫ = 0 at hu
  rw [real_inner_smul_left,mul_eq_zero] at hu
  rcases hu with h | h
  · exact False.elim ((inv_ne_zero (norm_ne_zero_iff.mpr hk)) h)
  · change ⟪k,u.val⟫ • k = 0
    rw [h,zero_smul]

theorem soft_chord_unit_eigenvalues (σ : ℝ) (k : EuclideanPlaneMomentum) (hk : k ≠ 0)
    (u : ConeUnitDirection) (hu : ⟪(euclideanMomentumUnit k hk).val,u.val⟫ = 0) :
    softChordDifferential σ k u.val = tangentialChord (σ^2*‖k‖^2) • u.val ∧
    softChordDifferential σ k (euclideanMomentumUnit k hk).val =
      radialChord (σ^2*‖k‖^2) • (euclideanMomentumUnit k hk).val := by
  constructor
  · simp [softChordDifferential,tangentialChord,soft_outer_tangential k hk u hu]
  · simp only [softChordDifferential,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply,soft_outer_radial k hk,radialChord,smul_smul]
    module

theorem soft_log_unit_eigenvalues (m : ℝ) (k : EuclideanPlaneMomentum) (hk : k ≠ 0)
    (u : ConeUnitDirection) (hu : ⟪(euclideanMomentumUnit k hk).val,u.val⟫ = 0) :
    softLogHessian m k u.val = (4/(m^2+‖k‖^2)) • u.val ∧
    softLogHessian m k (euclideanMomentumUnit k hk).val =
      (4*(m^2-‖k‖^2)/(m^2+‖k‖^2)^2) • (euclideanMomentumUnit k hk).val := by
  constructor
  · simp [softLogHessian,soft_outer_tangential k hk u hu]
  · have h : m^2+‖k‖^2 ≠ 0 := by positivity
    simp only [softLogHessian,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply,soft_outer_radial k hk,smul_smul]
    rw [← sub_smul]
    congr 1
    field_simp
    ring

end UV.RelativeSoft
