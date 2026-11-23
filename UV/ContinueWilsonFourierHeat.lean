import UV.ContinueWilsonShellDensityBound
import UV.ContinueWilsonPolygonCurrent
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! Fourier normalization for Gaussian windows in four carrier coordinates.
The momentum window has height one. Its inverse transform has a positive,
width-independent integral in the angular-frequency convention. -/

noncomputable section

open MeasureTheory Set Filter Real
open scoped Topology ENNReal RealInnerProductSpace

namespace UV

def wilsonHeatWindow (t : ℝ) (p : OSFourSpace) : ℝ := Real.exp (-t*‖p‖^2)

theorem wilson_heat_window_pos (t : ℝ) (p : OSFourSpace) : 0 < wilsonHeatWindow t p := Real.exp_pos _

def wilsonHeatKernel (t : ℝ) (d : OSFourSpace) : ℝ := (π/t)^2 * wilsonHeatWindow (4*t)⁻¹ d

theorem wilson_heat_window_integrable {t : ℝ} (ht : 0 < t) : Integrable (wilsonHeatWindow t) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := OSFourSpace)
    (b := (t:ℂ)) (by simpa using ht) 0 0).norm
  change Integrable (fun p : OSFourSpace => Real.exp (-t*‖p‖^2))
  simpa [Complex.norm_exp,Complex.mul_re,←Complex.ofReal_pow] using h

theorem wilson_heat_window_integral {t : ℝ} (ht : 0 < t) : (∫ p, wilsonHeatWindow t p) = (π/t)^2 := by
  simpa only [wilsonHeatWindow,finrank_euclideanSpace,Fintype.card_fin,Nat.cast_ofNat,
    show (4:ℝ)/2 = 2 by norm_num,Real.rpow_two] using
      (GaussianFourier.integral_rexp_neg_mul_sq_norm (V := OSFourSpace) ht)

theorem wilson_heat_fourier {t : ℝ} (ht : 0 < t) (d : OSFourSpace) :
    ∫ p, (wilsonHeatWindow t p:ℂ)*thinPlaneWave p d = (wilsonHeatKernel t d:ℂ) := by
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (b := (t:ℂ)) (by simpa using ht) Complex.I d
  calc
    _ = ∫ p : OSFourSpace, Complex.exp (-(t:ℂ)*‖p‖^2 + Complex.I*⟪d,p⟫) := by
      congr 1
      funext p
      simp [wilsonHeatWindow,thinPlaneWave,Complex.ofReal_exp,←Complex.exp_add,real_inner_comm p d]
    _ = _ := by
      rw [h]
      simp only [wilsonHeatKernel,wilsonHeatWindow,finrank_euclideanSpace,Fintype.card_fin,
        Nat.cast_ofNat,show (4:ℂ)/2=2 by norm_num,Complex.cpow_ofNat,
        Complex.I_sq,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_div,
        Complex.ofReal_exp,Complex.ofReal_neg,Complex.ofReal_inv,Complex.ofReal_ofNat]
      congr 2
      ring

theorem wilson_heat_kernel_integrable {t : ℝ} (ht : 0 < t) : Integrable (wilsonHeatKernel t) :=
  (wilson_heat_window_integrable (inv_pos.mpr (mul_pos (by norm_num) ht))).const_mul _

theorem wilson_heat_kernel_mass {t : ℝ} (ht : 0 < t) : (∫ d, wilsonHeatKernel t d) = (2*π)^4 := by
  unfold wilsonHeatKernel
  rw [integral_const_mul,wilson_heat_window_integral (by positivity)]
  field_simp
  ring

theorem wilson_heat_kernel_pos {t : ℝ} (ht : 0 < t) (d : OSFourSpace) : 0 < wilsonHeatKernel t d :=
  mul_pos (sq_pos_of_pos (div_pos Real.pi_pos ht)) (Real.exp_pos _)

theorem wilson_heat_kernel_measure_bound {μ : Measure OSFourSpace} {C : ℝ≥0∞} (hμ : μ ≤ C • volume)
    (hC : C ≠ ⊤) {t : ℝ} (ht : 0 < t) : (∫ d, wilsonHeatKernel t d ∂μ) ≤ C.toReal*(2*π)^4 := by
  apply (integral_mono_measure hμ (Eventually.of_forall fun d => (wilson_heat_kernel_pos ht d).le)
    ((wilson_heat_kernel_integrable ht).smul_measure hC)).trans_eq
  rw [integral_smul_measure,wilson_heat_kernel_mass ht,smul_eq_mul]

end UV
