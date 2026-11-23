import UV.StableCovariance
import UV.RevisionOSJoint
import Mathlib.Analysis.Distribution.FourierSchwartz

/-! Integrable Poisson transfers and their exact multiplier in the Fourier
normalization used for the massive reflection test. -/

noncomputable section

open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace Topology ComplexConjugate

namespace UV

def osTransferSymbol (r : ℝ) (k : OSFourSpace) : ℝ :=
  Real.exp (-r * (2 * Real.pi * ‖k‖))

theorem osKernel_weighted_joint {K g : OSFourSpace → ℝ} (hK : Continuous K)
    (hKi : Integrable K) (hg : Integrable g) :
    Integrable (fun p : OSFourSpace × OSFourSpace => K (p.2-p.1) * g p.1)
      (volume.prod volume) := by
  have hmeas := (hK.comp (continuous_snd.sub continuous_fst)).aestronglyMeasurable
    (μ := (volume : Measure OSFourSpace).prod volume)
  apply (integrable_prod_iff (hmeas.mul hg.1.comp_fst)).mpr
  have htr (y : OSFourSpace) : Integrable (fun x => K (x-y)) := by
    simpa only [sub_eq_add_neg] using
      (measurePreserving_add_right volume (-y)).integrable_comp_of_integrable hKi
  refine ⟨Eventually.of_forall (fun y => (htr y).mul_const (g y)), ?_⟩
  change Integrable (fun y => ∫ x, ‖K (x - y) * g y‖)
  have h (y : OSFourSpace) : (∫ x, ‖K (x - y) * g y‖) = (∫ x, ‖K x‖) * ‖g y‖ := by
    simp_rw [norm_mul, sub_eq_add_neg, integral_mul_const]
    rw [integral_add_right_eq_self (fun x => ‖K x‖) (-y)]
  simpa only [h] using hg.norm.const_mul (∫ x, ‖K x‖)

theorem osPoisson_weighted_joint {r : ℝ} (hr : 0 < r)
    {g : OSFourSpace → ℝ} (hg : Integrable g) :
    Integrable (fun p : OSFourSpace × OSFourSpace =>
      stablePoissonKernel r (p.2-p.1) * g p.1) (volume.prod volume) :=
  osKernel_weighted_joint (stablePoissonKernel_continuous hr) (stablePoissonKernel_integrable hr) hg

theorem osPoissonTransfer_integrable {r : ℝ} (hr : 0 < r)
    {g : OSFourSpace → ℝ} (hg : Integrable g) :
    Integrable (osPoissonTransfer r g) :=
  (osPoisson_weighted_joint hr hg).swap.integral_prod_left

theorem osFourier_phase (k : OSFourSpace) (f : OSFourSpace → ℂ) :
    𝓕 f k = ∫ x, stableFourierPhase ((-(2 * Real.pi)) • k) x * f x := by
  rw [Real.fourierIntegral_eq']
  congr 1
  funext x
  rw [stableFourierPhase, real_inner_smul_left, real_inner_comm k x, smul_eq_mul]
  push_cast
  ring_nf

/-- Convolution duality for the physical and the cycles-per-length Fourier conventions. -/
theorem osKernel_convolution_fourier {K g : OSFourSpace → ℝ} (hK : Continuous K)
    (hKi : Integrable K) (hg : Integrable g) (k : OSFourSpace) :
    𝓕 (fun x => ((∫ y, K (x-y) * g y : ℝ) : ℂ)) k =
      𝓕 (fun x => (K x : ℂ)) k * 𝓕 (fun x => (g x : ℂ)) k := by
  let q := (-(2 * Real.pi)) • k
  have hbase := osKernel_weighted_joint hK hKi hg
  have hj : Integrable (fun p : OSFourSpace × OSFourSpace =>
      stableFourierPhase q p.2 * ((K (p.2 - p.1) * g p.1 : ℝ) : ℂ))
      (volume.prod volume) := by
    refine hbase.norm.mono' (stableFourierPhase_continuous.comp
      (continuous_const.prodMk continuous_snd) |>.aestronglyMeasurable |>.mul
        (Complex.ofRealCLM.continuous.comp_aestronglyMeasurable hbase.1)) ?_
    filter_upwards with p
    rw [norm_mul, stableFourierPhase_norm, one_mul, Complex.norm_real]
  simp only [osFourier_phase]
  change (∫ x, stableFourierPhase q x * ((∫ y, K (x-y) * g y : ℝ) : ℂ)) =
    (∫ x, stableFourierPhase q x * (K x : ℂ)) * ∫ y, stableFourierPhase q y * (g y : ℂ)
  calc
    _ = ∫ x, ∫ y, stableFourierPhase q x *
        ((K (x - y) * g y : ℝ) : ℂ) := by
      congr 1
      funext x
      rw [integral_const_mul, integral_complex_ofReal]
    _ = ∫ y, ∫ x, stableFourierPhase q x *
        ((K (x - y) * g y : ℝ) : ℂ) := (integral_integral_swap hj).symm
    _ = _ := by
      rw [← integral_const_mul]
      congr 1
      funext y
      simp_rw [Complex.ofReal_mul, ← mul_assoc]
      rw [integral_mul_const]
      have htr := integral_add_right_eq_self (μ := volume)
        (fun x : OSFourSpace => stableFourierPhase q x * (K (x-y) : ℂ)) y
      simp only [add_sub_cancel_right, stableFourierPhase_add] at htr
      rw [← htr]
      simp_rw [mul_right_comm (stableFourierPhase q _ ) (stableFourierPhase q y)]
      rw [integral_mul_const]

/-- The actual Poisson convolution has the exponential depth multiplier
at physical momentum 2πk. -/
theorem osPoissonTransfer_fourier {r : ℝ} (hr : 0 < r)
    {g : OSFourSpace → ℝ} (hg : Integrable g) (k : OSFourSpace) :
    𝓕 (fun x => (osPoissonTransfer r g x : ℂ)) k =
      (osTransferSymbol r k : ℂ) * 𝓕 (fun x => (g x : ℂ)) k := by
  unfold osPoissonTransfer
  rw [osKernel_convolution_fourier (stablePoissonKernel_continuous hr) (stablePoissonKernel_integrable hr) hg,
    osFourier_phase k (fun x => (stablePoissonKernel r x : ℂ)), stablePoissonKernel_characteristic hr]
  simp [osTransferSymbol, norm_smul, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- Fourier duality with an arbitrary integrable right source and a
Schwartz left probe. Both integrals are Lebesgue integrals. -/
theorem osFourier_duality (u : 𝓢(OSFourSpace, ℂ)) {v : OSFourSpace → ℂ}
    (hv : Integrable v) :
    (∫ k, 𝓕⁻ u k * 𝓕 v k) = ∫ x, u x * v x := by
  let U := (SchwartzMap.fourierTransformCLE ℂ).symm u
  have hU (k : OSFourSpace) : U k = 𝓕⁻ u k := by
    change (⇑((SchwartzMap.fourierTransformCLE ℂ).symm u)) k = _
    rw [SchwartzMap.fourierTransformCLE_symm_apply]
  have hi (x : OSFourSpace) : 𝓕 U x = u x := by
    exact congrArg (fun f : 𝓢(OSFourSpace, ℂ) => f x)
      ((SchwartzMap.fourierTransformCLE ℂ).apply_symm_apply u)
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := volume) (ν := volume) (L := innerₗ OSFourSpace) Real.continuous_fourierChar continuous_inner U.integrable hv
  rw [flip_innerₗ] at h
  change (∫ x, 𝓕 U x * v x) = ∫ k, U k * 𝓕 v k at h
  simpa only [hi, hU] using h.symm

/-- For a real probe, inverse Fourier transform is complex conjugation of the
forward transform at the same momentum. -/
theorem osFourier_inverse_real (u : OSFourSpace → ℝ) (k : OSFourSpace) :
    𝓕⁻ (fun x => (u x : ℂ)) k = conj (𝓕 (fun x => (u x : ℂ)) k) := by
  rw [Real.fourierIntegral_eq', Real.fourierIntegralInv_eq', ← integral_conj]
  congr 1
  funext x
  simp [smul_eq_mul, ← Complex.exp_conj, map_ofNat]

end UV
