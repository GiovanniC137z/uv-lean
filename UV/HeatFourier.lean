import UV.ScalarGaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Literal physical-frequency Gaussian Fourier identities in four dimensions.
The Fourier phase is exp(i⟪q,x⟫), with inverse factor (2π)⁻⁴. -/

noncomputable section
open MeasureTheory Set Real
open scoped RealInnerProductSpace Complex ENNReal

namespace UV

def stableFourierPhase (q x : ScalarMomentum) : ℂ :=
  Complex.exp (Complex.I * (⟪q, x⟫ : ℝ))

def stableGaussianWave (t : ℝ) (x q : ScalarMomentum) : ℂ :=
  stableFourierPhase x q * (Real.exp (-t * ‖q‖ ^ 2) : ℂ)

def stableHeatKernel (t : ℝ) (x : ScalarMomentum) : ℝ :=
  Real.exp (-‖x‖ ^ 2 / (4 * t)) / (16 * Real.pi ^ 2 * t ^ 2)

def stableUnitGaussian : Measure ScalarMomentum :=
  volume.withDensity (fun x => ENNReal.ofReal (stableHeatKernel 1 x))

theorem stableFourierPhase_norm (q x : ScalarMomentum) : ‖stableFourierPhase q x‖ = 1 := by
  simp [stableFourierPhase, Complex.norm_exp, Complex.mul_re]

theorem stableFourierPhase_continuous : Continuous (fun p : ScalarMomentum × ScalarMomentum =>
    stableFourierPhase p.1 p.2) := by unfold stableFourierPhase; fun_prop

theorem stableFourierPhase_add (q x y : ScalarMomentum) :
    stableFourierPhase q (x + y) = stableFourierPhase q x * stableFourierPhase q y := by
  unfold stableFourierPhase
  rw [inner_add_right, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem stableFourierPhase_neg (q x : ScalarMomentum) :
    stableFourierPhase q (-x) = stableFourierPhase (-q) x := by
  simp [stableFourierPhase]

theorem stableGaussianWave_norm (t : ℝ) (x q : ScalarMomentum) :
    ‖stableGaussianWave t x q‖ = Real.exp (-t * ‖q‖ ^ 2) := by
  rw [stableGaussianWave, norm_mul, stableFourierPhase_norm, one_mul,
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]

lemma stableGaussianWave_eq (t : ℝ) (x q : ScalarMomentum) :
    stableGaussianWave t x q =
      Complex.exp (-(t : ℂ) * (‖q‖ : ℂ) ^ 2 + Complex.I * (⟪x, q⟫ : ℝ)) := by
  unfold stableGaussianWave stableFourierPhase
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem stable_gaussian_characteristic_integrable {t : ℝ} (ht : 0 < t) (x : ScalarMomentum) :
    Integrable (stableGaussianWave t x) := by
  have heq : stableGaussianWave t x = fun q : ScalarMomentum =>
      Complex.exp (-(t : ℂ) * (‖q‖ : ℂ) ^ 2 + Complex.I * (⟪x, q⟫ : ℝ)) :=
    funext (stableGaussianWave_eq t x)
  rw [heq]
  exact GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (show 0 < (t : ℂ).re from ht) Complex.I x

/-- The exact unnormalized Gaussian Fourier integral, in physical frequency. -/
theorem stable_gaussian_characteristic_integral {t : ℝ} (ht : 0 < t) (x : ScalarMomentum) :
    (∫ q : ScalarMomentum, stableGaussianWave t x q) =
      ((Real.pi ^ 2 / t ^ 2) * Real.exp (-‖x‖ ^ 2 / (4 * t)) : ℝ) := by
  simp_rw [stableGaussianWave_eq]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (show 0 < (t : ℂ).re from ht) Complex.I x]
  have hdim : (Module.finrank ℝ ScalarMomentum / 2 : ℂ) = 2 := by
    norm_num [ScalarMomentum, finrank_euclideanSpace]
  rw [hdim, Complex.cpow_two, Complex.I_sq, neg_one_mul]
  push_cast
  rw [div_pow]

theorem stableHeatKernel_nonneg (t : ℝ) (x : ScalarMomentum) : 0 ≤ stableHeatKernel t x := by
  unfold stableHeatKernel
  positivity

theorem stableHeatKernel_continuous (t : ℝ) : Continuous (stableHeatKernel t) := by
  unfold stableHeatKernel
  fun_prop

theorem stableHeatKernel_measurable (t : ℝ) : Measurable (stableHeatKernel t) :=
  (stableHeatKernel_continuous t).measurable

theorem stableHeatKernel_integrable {t : ℝ} (ht : 0 < t) : Integrable (stableHeatKernel t) := by
  have h := (scalar_gaussian_integrable (b := 1 / (4 * t)) (by positivity)).div_const
    (16 * Real.pi ^ 2 * t ^ 2)
  convert h using 1
  ext x
  unfold stableHeatKernel
  congr 2
  ring

theorem stableHeatKernel_integral {t : ℝ} (ht : 0 < t) :
    (∫ x : ScalarMomentum, stableHeatKernel t x) = 1 := by
  have heq : stableHeatKernel t = fun x : ScalarMomentum =>
      Real.exp (-(1 / (4 * t)) * ‖x‖ ^ 2) / (16 * Real.pi ^ 2 * t ^ 2) := by
    ext x
    unfold stableHeatKernel
    congr 2
    ring
  rw [heq, integral_div, scalar_gaussian_integral (by positivity)]
  field_simp
  norm_num

instance stableUnitGaussian_probability : IsProbabilityMeasure stableUnitGaussian := by
  constructor
  rw [stableUnitGaussian, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (stableHeatKernel_integrable (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall (stableHeatKernel_nonneg 1)), stableHeatKernel_integral (by norm_num)]
  exact ENNReal.ofReal_one

/-- The actual with-density integral, usable for real and complex integrands. -/
theorem stableUnitGaussian_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ScalarMomentum → E) :
    (∫ x, f x ∂stableUnitGaussian) = ∫ x, stableHeatKernel 1 x • f x := by
  rw [stableUnitGaussian, integral_withDensity_eq_integral_toReal_smul
    (stableHeatKernel_measurable 1).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (stableHeatKernel_nonneg 1 x)]

theorem stableUnitGaussian_characteristic (q : ScalarMomentum) :
    (∫ x, stableFourierPhase q x ∂stableUnitGaussian) = (Real.exp (-‖q‖ ^ 2) : ℂ) := by
  rw [stableUnitGaussian_integral]
  have heq : (fun x : ScalarMomentum => stableHeatKernel 1 x • stableFourierPhase q x) =
      fun x => ((16 * Real.pi ^ 2)⁻¹ : ℂ) * stableGaussianWave (1 / 4) q x := by
    ext x
    simp only [stableHeatKernel, one_pow, mul_one, Complex.real_smul, stableGaussianWave]
    rw [show -‖x‖ ^ 2 / (4 : ℝ) = -(1 / 4 : ℝ) * ‖x‖ ^ 2 by ring]
    push_cast
    ring
  rw [heq, integral_const_mul, stable_gaussian_characteristic_integral (by norm_num)]
  push_cast
  norm_num
  field_simp

end UV
