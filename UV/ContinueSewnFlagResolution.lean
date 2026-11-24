import UV.StableCovariance
import Mathlib.MeasureTheory.Function.L2Space

/-! The one-scale Gaussian resolution comparison on the four real
Euclidean coordinates. All final reading coordinates are integrated. -/

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal RealInnerProductSpace ComplexConjugate
namespace UV.SewnFlags

private def resolutionPrecision (ℓ : ℝ) : ℝ := (4*ℓ^2)⁻¹
private def resolutionConstant (ℓ : ℝ) : ℝ := (2*π*ℓ^2)⁻¹

def oneScaleDisplacementDensity (ℓ : ℝ) (d : ScalarMomentum) : ℝ :=
  resolutionConstant ℓ ^ 2 * exp (-(2*resolutionPrecision ℓ)*‖d‖^2)

def oneScalePointer (ℓ : ℝ) (d x : ScalarMomentum) : ℝ :=
  resolutionConstant ℓ * exp (-resolutionPrecision ℓ * ‖x-d‖^2)

def oneScaleMarkedAmplitude (ℓ : ℝ) (k x : ScalarMomentum) : ℂ :=
  ∫ d, (oneScaleDisplacementDensity ℓ d : ℂ) * stableFourierPhase d k * (oneScalePointer ℓ d x : ℂ)

private theorem oneScaleDensity_mass_constant {ℓ : ℝ} (hℓ : 0 < ℓ) :
    resolutionConstant ℓ ^ 2 * (π^2/(2*resolutionPrecision ℓ)^2) = 1 := by
  unfold resolutionConstant resolutionPrecision
  field_simp [hℓ.ne',pi_pos.ne']
  ring

theorem oneScaleDensity_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (d : ScalarMomentum) :
    oneScaleDisplacementDensity ℓ d = ((2*π*ℓ^2)^2)⁻¹ * exp (-‖d‖^2/(2*ℓ^2)) := by
  unfold oneScaleDisplacementDensity resolutionConstant resolutionPrecision
  rw [inv_pow]
  congr 2
  field_simp [hℓ.ne']
  ring

theorem oneScaleDisplacementDensity_integral {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ d, oneScaleDisplacementDensity ℓ d) = 1 := by
  unfold oneScaleDisplacementDensity
  rw [integral_const_mul,scalar_gaussian_integral (by unfold resolutionPrecision; positivity)]
  exact oneScaleDensity_mass_constant hℓ

theorem oneScalePointer_sq (ℓ : ℝ) (d x : ScalarMomentum) :
    (oneScalePointer ℓ d x)^2 = oneScaleDisplacementDensity ℓ (x-d) := by
  unfold oneScalePointer oneScaleDisplacementDensity
  rw [mul_pow,pow_two (exp _),← exp_add]
  congr 2
  ring

theorem oneScalePointer_nonneg (ℓ : ℝ) (d x : ScalarMomentum) : 0 ≤ oneScalePointer ℓ d x := by
  unfold oneScalePointer resolutionConstant
  positivity

theorem oneScalePointer_eq_sqrt (ℓ : ℝ) (d x : ScalarMomentum) :
    oneScalePointer ℓ d x = sqrt (oneScaleDisplacementDensity ℓ (x-d)) := by
  rw [← oneScalePointer_sq]
  exact (sqrt_sq (oneScalePointer_nonneg ℓ d x)).symm

theorem oneScalePointer_normalized {ℓ : ℝ} (hℓ : 0 < ℓ) (d : ScalarMomentum) :
    (∫ x, (oneScalePointer ℓ d x)^2) = 1 := by
  simp_rw [oneScalePointer_sq,sub_eq_add_neg]
  rw [integral_add_right_eq_self]
  exact oneScaleDisplacementDensity_integral hℓ

theorem oneScalePointer_overlap {ℓ : ℝ} (hℓ : 0 < ℓ) (d e : ScalarMomentum) :
    (∫ x, oneScalePointer ℓ d x * oneScalePointer ℓ e x) = exp (-‖d-e‖^2/(8*ℓ^2)) := by
  let a := resolutionPrecision ℓ
  let c := resolutionConstant ℓ
  let b := (1/2:ℝ) • (d+e)
  have ha : 0 < a := by unfold a resolutionPrecision; positivity
  have hNorm (x : ScalarMomentum) : ‖x-d‖^2+‖x-e‖^2 = 2*‖x-b‖^2 + ‖d-e‖^2/2 := by
    unfold b
    simp only [norm_sub_sq_real,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : 0 ≤ (1/2:ℝ)),
      mul_pow,norm_add_sq_real,inner_smul_right,inner_add_right]
    ring
  have h (x : ScalarMomentum) : oneScalePointer ℓ d x * oneScalePointer ℓ e x =
      (c^2*exp (-(a/2)*‖d-e‖^2)) * exp (-(2*a)*‖x-b‖^2) := by
    change (c*exp (-a*‖x-d‖^2))*(c*exp (-a*‖x-e‖^2)) = _
    calc
      _ = c^2*exp (-a*(‖x-d‖^2+‖x-e‖^2)) := by rw [mul_add,exp_add]; ring
      _ = _ := by rw [hNorm,show -a*(2*‖x-b‖^2+‖d-e‖^2/2) =
        -(a/2)*‖d-e‖^2 + -(2*a)*‖x-b‖^2 by ring,exp_add,mul_assoc]
  simp_rw [h,sub_eq_add_neg]
  have hTrans : (∫ u : ScalarMomentum, exp (-(2*a)*‖u+(-b)‖^2)) =
      ∫ u : ScalarMomentum, exp (-(2*a)*‖u‖^2) :=
    integral_add_right_eq_self (fun u : ScalarMomentum => exp (-(2*a)*‖u‖^2)) (-b)
  rw [integral_const_mul,hTrans,scalar_gaussian_integral (mul_pos (by norm_num) ha)]
  rw [mul_right_comm,show c^2*(π^2/(2*a)^2)=1 from oneScaleDensity_mass_constant hℓ,one_mul]
  congr 1
  unfold a resolutionPrecision
  field_simp [hℓ.ne']
  ring

private theorem oneScale_joint_gaussian_factor {a : ℝ} (ha : 0 < a) (d x : ScalarMomentum) :
    exp (-(2*a)*‖d‖^2) * exp (-a*‖x-d‖^2) =
      exp (-(2*a/3)*‖x‖^2) * exp (-(3*a)*‖d-(1/3:ℝ) • x‖^2) := by
  have h := two_line_gaussian_factor (w₁ := 2*a) (w₂ := a) (ne_of_gt (by positivity)) (-x) d
  rw [show 2*a+a = 3*a by ring,show (a/(3*a)) = (1/3:ℝ) by field_simp [ha.ne'],
    show 2*a*a/(3*a)=2*a/3 by field_simp [ha.ne'],norm_neg,smul_neg,
    ← sub_eq_add_neg d x,← sub_eq_add_neg d ((1/3:ℝ) • x),norm_sub_rev d x] at h
  rw [← exp_add]
  simpa only [sub_eq_add_neg,neg_mul] using h

theorem oneScaleMarkedAmplitude_exact {ℓ : ℝ} (hℓ : 0 < ℓ) (k x : ScalarMomentum) :
    let a := resolutionPrecision ℓ
    let c := resolutionConstant ℓ
    oneScaleMarkedAmplitude ℓ k x =
      ((c^3*exp (-(2*a/3)*‖x‖^2):ℝ):ℂ) * stableFourierPhase ((1/3:ℝ) • x) k *
        ((π^2/(3*a)^2 * exp (-‖k‖^2/(4*(3*a))):ℝ):ℂ) := by
  dsimp only
  let a := resolutionPrecision ℓ
  let c := resolutionConstant ℓ
  let b := (1/3:ℝ) • x
  have ha : 0 < a := by unfold a resolutionPrecision; positivity
  let Z := ((c^3 * exp (-(2*a/3)*‖x‖^2):ℝ):ℂ)*stableFourierPhase b k
  have h (d : ScalarMomentum) : (oneScaleDisplacementDensity ℓ d:ℂ) * stableFourierPhase d k *
      (oneScalePointer ℓ d x:ℂ) = Z * stableGaussianWave (3*a) k (d-b) := by
    have hPhase : stableFourierPhase d k = stableFourierPhase b k*stableFourierPhase (d-b) k := by
      rw [← stableFourierPhase_add_frequency,add_comm b,sub_add_cancel]
    calc
      _ = ((c^3*(exp (-(2*a)*‖d‖^2)*exp (-a*‖x-d‖^2)):ℝ):ℂ)*stableFourierPhase d k := by
        unfold oneScaleDisplacementDensity oneScalePointer
        change ((c^2*exp (-(2*a)*‖d‖^2):ℝ):ℂ)*stableFourierPhase d k *
          ((c*exp (-a*‖x-d‖^2):ℝ):ℂ) = _
        push_cast
        ring
      _ = _ := by
        rw [oneScale_joint_gaussian_factor ha,hPhase]
        unfold Z stableGaussianWave
        have hs : stableFourierPhase (d-b) k = stableFourierPhase k (d-b) := by
          unfold stableFourierPhase
          rw [real_inner_comm]
        rw [hs]
        push_cast
        ring
  unfold oneScaleMarkedAmplitude
  simp_rw [h,sub_eq_add_neg]
  rw [integral_const_mul,integral_add_right_eq_self,stable_gaussian_characteristic_integral (by positivity)]

private theorem oneScaleNormConstant {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (resolutionConstant ℓ ^ 3 * (π^2/(3*resolutionPrecision ℓ)^2))^2 *
      (π^2/(4*resolutionPrecision ℓ/3)^2) = (2/3:ℝ)^2 := by
  unfold resolutionConstant resolutionPrecision
  field_simp [hℓ.ne',pi_pos.ne']
  ring

/-- Inclusive integration over the actual reading recovers the
normalized one-scale Gaussian suppression, at every momentum. -/
theorem oneScaleMarkedAmplitude_inclusive {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ScalarMomentum) :
    Integrable (fun x => ‖oneScaleMarkedAmplitude ℓ k x‖^2) ∧
      (∫ x, ‖oneScaleMarkedAmplitude ℓ k x‖^2) = (2/3:ℝ)^2*exp (-(2*ℓ^2/3)*‖k‖^2) := by
  let a := resolutionPrecision ℓ
  let c := resolutionConstant ℓ
  have ha : 0 < a := by unfold a resolutionPrecision; positivity
  have hc : 0 < c := by unfold c resolutionConstant; positivity
  let B := (c^3*(π^2/(3*a)^2))^2 * exp (-(2*ℓ^2/3)*‖k‖^2)
  have he (x : ScalarMomentum) : ‖oneScaleMarkedAmplitude ℓ k x‖^2 = B * exp (-(4*a/3)*‖x‖^2) := by
    rw [oneScaleMarkedAmplitude_exact hℓ,norm_mul,norm_mul,stableFourierPhase_norm,mul_one,
      Complex.norm_real, Complex.norm_real]
    change (‖c^3*exp (-(2*a/3)*‖x‖^2)‖*‖π^2/(3*a)^2*exp (-‖k‖^2/(4*(3*a)))‖)^2 = _
    rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity),mul_pow,mul_pow,mul_pow,
      pow_two (exp (-(2*a/3)*‖x‖^2)),pow_two (exp (-‖k‖^2/(4*(3*a)))),← exp_add,← exp_add]
    have hE : -‖k‖^2/(4*(3*a)) + -‖k‖^2/(4*(3*a)) = -(2*ℓ^2/3)*‖k‖^2 := by
      unfold a resolutionPrecision
      field_simp [hℓ.ne']
      ring
    rw [hE,show -(2*a/3)*‖x‖^2 + -(2*a/3)*‖x‖^2 = -(4*a/3)*‖x‖^2 by ring]
    unfold B
    ring
  simp_rw [he]
  have hβ : 0 < 4*a/3 := by positivity
  refine ⟨(scalar_gaussian_integrable hβ).const_mul B,?_⟩
  rw [integral_const_mul,scalar_gaussian_integral hβ]
  unfold B
  rw [mul_right_comm,show (c^3*(π^2/(3*a)^2))^2*(π^2/(4*a/3)^2) = (2/3:ℝ)^2 from
    oneScaleNormConstant hℓ]

end UV.SewnFlags
