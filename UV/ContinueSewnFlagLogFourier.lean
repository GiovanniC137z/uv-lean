import UV.ContinueSewnFlagLogKernel
import UV.HeatFourier
import UV.ContinueNetworkTonelli
import Mathlib.MeasureTheory.Integral.Pi

/-! Exact marginal denominator and fixed-duration Fourier integrals
in the four Euclidean coordinates of the locked sector plane. -/

noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal BigOperators
namespace UV.SewnFlags

open UV.RevisionJointHeat

def marginalSchwinger (μ : ℝ) (q : ScalarMomentum) (t : ℝ) :=
  t * exp (-(μ^2+‖q‖^2)*t)/(2*π)^4

def marginalHeat (μ t x : ℝ) :=
  exp (-(μ^2*t+x^2/(4*t)))/((4*π)^2*t)

theorem marginal_schwinger_lintegral {μ : ℝ} (hμ : 0 < μ) (q : ScalarMomentum) :
    (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (marginalSchwinger μ q t)) =
      ENNReal.ofReal (((μ^2+‖q‖^2)^2)⁻¹/(2*π)^4) := by
  let A := μ^2+‖q‖^2
  have hA : 0 < A := by dsimp [A]; positivity
  have he : marginalSchwinger μ q =
      fun t => selectorDensity A 0 2 t/(2*π)^4 := by
    funext t
    rw [marginalSchwinger,selectorDensity,zero_div,add_zero,show (2:ℝ)-1=1 by norm_num,rpow_one]
    rw [neg_mul]
  have hi : IntegrableOn (marginalSchwinger μ q) (Ioi 0) := by
    rw [he]
    exact ((selectorDensity_zero_integrable_iff hA).2 (by norm_num : (0:ℝ) < 2)).div_const _
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] marginalSchwinger μ q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    unfold marginalSchwinger
    have ht' : 0 < t := ht
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,he,integral_div,← selectorZ,selectorZ_zero_gamma hA (by norm_num),
    Gamma_two,mul_one,rpow_neg hA.le,rpow_two]

private theorem marginal_fourier_factor (μ t : ℝ) (d q : ScalarMomentum) :
    (marginalSchwinger μ q t : ℂ)*stableFourierPhase d q =
      ((t*exp (-(μ^2)*t)/(2*π)^4:ℝ):ℂ)*stableGaussianWave t d q := by
  simp only [marginalSchwinger,stableGaussianWave,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow]
  rw [show -(μ^2+‖q‖^2)*t = -(μ^2)*t + -t*‖q‖^2 by ring,exp_add,Complex.ofReal_mul]
  ring

theorem marginal_fourier_integrable (μ : ℝ) {t : ℝ} (ht : 0 < t) (d : ScalarMomentum) :
    Integrable (fun q : ScalarMomentum => (marginalSchwinger μ q t:ℂ)*stableFourierPhase d q) := by
  simp_rw [marginal_fourier_factor]
  exact (stable_gaussian_characteristic_integrable ht d).const_mul _

theorem marginal_fourier_gaussian (μ : ℝ) {t : ℝ} (ht : 0 < t) (d : ScalarMomentum) :
    (∫ q : ScalarMomentum, (marginalSchwinger μ q t:ℂ)*stableFourierPhase d q) =
      (marginalHeat μ t ‖d‖:ℂ) := by
  simp_rw [marginal_fourier_factor]
  rw [integral_const_mul,stable_gaussian_characteristic_integral ht d,← Complex.ofReal_mul]
  congr 1
  unfold marginalHeat
  rw [show -(μ^2*t+‖d‖^2/(4*t))= -(μ^2)*t + -‖d‖^2/(4*t) by ring,exp_add]
  field_simp [pi_pos.ne',ht.ne']
  ring

/-- At every fixed positive vector of durations the full loop Fourier
integral gives the product of the exact normalized heat factors. -/
theorem joint_marginal_fourier_gaussian {ι : Type*} [Fintype ι]
    (μ : ℝ) (t : ι → ℝ) (ht : ∀ i, 0 < t i) (d : ι → ScalarMomentum) :
    (∫ q : ι → ScalarMomentum,
      ∏ i, (marginalSchwinger μ (q i) (t i):ℂ)*stableFourierPhase (d i) (q i)) =
      (∏ i, marginalHeat μ (t i) ‖d i‖ : ℝ) := by
  rw [integral_fintype_prod_volume_eq_prod
    (fun i q => (marginalSchwinger μ q (t i):ℂ)*stableFourierPhase (d i) q)]
  simp only [marginal_fourier_gaussian μ (ht _),Complex.ofReal_prod]

/-- The positive time integral on the product of all loop axes equals
the product of the Bessel kernels, allowing infinite individual factors. -/
theorem joint_marginal_proper_time {ι : Type*} [Fintype ι] (μ : ℝ) (d : ι → ScalarMomentum) :
    (∫⁻ t : ι → ℝ, ∏ i, ENNReal.ofReal (marginalHeat μ (t i) ‖d i‖)
      ∂Measure.pi (fun _ : ι => volume.restrict (Ioi (0:ℝ)))) =
      ∏ i, logKernel μ ‖d i‖ := by
  rw [UV.network_lintegral_fintype_prod _ (fun i t => ENNReal.ofReal (marginalHeat μ t ‖d i‖))
    (fun _ => by unfold marginalHeat; fun_prop)]
  simp only [logKernel_proper_time,marginalHeat]

end UV.SewnFlags
