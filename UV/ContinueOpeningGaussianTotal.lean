import UV.ContinueOpeningGaussianWaves
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-! Fourier uniqueness for L¹ densities against an arbitrary finite
measure on the line. The real positive densities are recovered by
characteristic-function uniqueness and the real and imaginary
components are then separated using the two signs of frequency. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ComplexConjugate ENNReal

namespace UV

theorem opening_wave_mul_integrable {μ : Measure ℝ} {g : ℝ → ℂ} (hg : Integrable g μ) (t : ℝ) :
    Integrable (fun x => g x * openingFourierWave t x) μ := by
  apply hg.norm.mono' (hg.aestronglyMeasurable.mul (opening_fourier_wave_continuous t).aestronglyMeasurable)
  exact Eventually.of_forall fun x => by change ‖g x * openingFourierWave t x‖ ≤ ‖g x‖; rw [norm_mul,opening_fourier_wave_norm,mul_one]

private theorem opening_wave_real_unique {μ : Measure ℝ} [IsFiniteMeasure μ] {g : ℝ → ℝ} (hg : Integrable g μ)
    (hz : ∀ t, (∫ x, (g x:ℂ)*openingFourierWave t x ∂μ)=0) : g =ᵐ[μ] 0 := by
  let q := fun x => |g x|
  let p := fun x => |g x|+g x
  have hqI : Integrable q μ := hg.abs
  have hpI : Integrable p μ := hqI.add hg
  have hq (x) : 0 ≤ q x := abs_nonneg _
  have hp (x) : 0 ≤ p x := by dsimp only [p]; linarith [neg_abs_le (g x)]
  let M := fun (a:ℝ→ℝ) => μ.withDensity (fun x => ENNReal.ofReal (a x))
  haveI : IsFiniteMeasure (M p) := isFiniteMeasure_withDensity_ofReal hpI.hasFiniteIntegral
  haveI : IsFiniteMeasure (M q) := isFiniteMeasure_withDensity_ofReal hqI.hasFiniteIntegral
  have hchar (a : ℝ → ℝ) (hm : Integrable a μ) (ha : ∀ x, 0≤a x) (t : ℝ) :
      charFun (M a) t = ∫ x, (a x:ℂ)*openingFourierWave t x ∂μ := by
    rw [charFun_apply_real]
    unfold M
    rw [integral_withDensity_eq_integral_toReal_smul₀ (hm.aemeasurable.ennreal_ofReal)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae (Eventually.of_forall fun x => ?_)
    rw [ENNReal.toReal_ofReal (ha x),Complex.real_smul]
    rfl
  have hm : M p=M q := by
    apply Measure.ext_of_charFun
    funext t
    rw [hchar p hpI hp,hchar q hqI hq]
    have hadd (x) : (p x:ℂ)*openingFourierWave t x =
      (q x:ℂ)*openingFourierWave t x+(g x:ℂ)*openingFourierWave t x := by dsimp [p,q];push_cast;ring
    simp_rw [hadd]
    have iq : Integrable (fun x => (q x:ℂ)*openingFourierWave t x) μ := opening_wave_mul_integrable hqI.ofReal t
    have ig : Integrable (fun x => (g x:ℂ)*openingFourierWave t x) μ := opening_wave_mul_integrable hg.ofReal t
    rw [integral_add iq ig,hz,add_zero]
  have hae := (withDensity_eq_iff_of_sigmaFinite hpI.aemeasurable.ennreal_ofReal hqI.aemeasurable.ennreal_ofReal).mp hm
  filter_upwards [hae] with x hx
  have h := congrArg ENNReal.toReal hx
  rw [ENNReal.toReal_ofReal (hp x),ENNReal.toReal_ofReal (hq x)] at h
  change |g x|+g x = |g x| at h
  change g x = 0
  linarith

/-- Every complex integrable density against a finite real-line measure
is determined by its full real-frequency Fourier transform. -/
theorem opening_fourier_density_unique {μ : Measure ℝ} [IsFiniteMeasure μ] {g : ℝ → ℂ} (hg : Integrable g μ)
    (hz : ∀ t, (∫ x, g x*openingFourierWave t x ∂μ)=0) : g =ᵐ[μ] 0 := by
  let h := fun x => conj (g x)
  have hI : Integrable h μ := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp hg
  have hconj (t) : (∫ x, h x*openingFourierWave t x ∂μ)=0 := by
    have he (x) : h x*openingFourierWave t x = conj (g x*openingFourierWave (-t) x) := by simp [h,opening_fourier_wave_conj]
    simp_rw [he]
    rw [integral_conj,hz,map_zero]
  have hre (t) : (∫ x, ((g x).re:ℂ)*openingFourierWave t x ∂μ)=0 := by
    have he (x) : ((g x).re:ℂ)*openingFourierWave t x =
      (g x*openingFourierWave t x+h x*openingFourierWave t x)/2 := by rw [Complex.re_eq_add_conj];dsimp only [h];ring
    simp_rw [he,integral_div,integral_add (opening_wave_mul_integrable hg _) (opening_wave_mul_integrable hI _),hz,hconj,zero_add,zero_div]
  have him (t) : (∫ x, ((g x).im:ℂ)*openingFourierWave t x ∂μ)=0 := by
    have he (x) : ((g x).im:ℂ)*openingFourierWave t x =
      (g x*openingFourierWave t x-h x*openingFourierWave t x)/(2*Complex.I) := by rw [Complex.im_eq_sub_conj];dsimp only [h];ring
    simp_rw [he]
    rw [integral_div,integral_sub (opening_wave_mul_integrable hg t) (opening_wave_mul_integrable hI t),hz,hconj]
    simp
  filter_upwards [opening_wave_real_unique hg.re hre,opening_wave_real_unique hg.im him] with x hx hy
  exact Complex.ext hx hy

end UV
