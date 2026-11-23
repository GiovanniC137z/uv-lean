import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Tactic

/-! The standard Gaussian spectral carrier and its normalized phase
waves. The Gaussian coordinate is the oscillator coordinate alone. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ComplexInnerProductSpace ComplexConjugate NNReal

namespace UV

abbrev openingGaussianLaw := gaussianReal 0 1
abbrev OpeningGaussianCarrier := Lp ℂ 2 openingGaussianLaw

def openingFourierWave (t x : ℝ) : ℂ := Complex.exp ((t:ℂ)*(x:ℂ)*Complex.I)

theorem opening_fourier_wave_norm (t x : ℝ) : ‖openingFourierWave t x‖=1 := by
  simp [openingFourierWave,Complex.norm_exp,Complex.mul_re,Complex.mul_im]

theorem opening_fourier_wave_add (s t x : ℝ) : openingFourierWave (s+t) x=openingFourierWave s x*openingFourierWave t x := by
  rw [openingFourierWave,openingFourierWave,openingFourierWave,←Complex.exp_add]
  push_cast
  ring_nf

theorem opening_fourier_wave_conj (t x : ℝ) : conj (openingFourierWave t x)=openingFourierWave (-t) x := by
  rw [openingFourierWave,openingFourierWave,←Complex.exp_conj]
  simp [Complex.conj_ofReal]

@[fun_prop] theorem opening_fourier_wave_continuous (t : ℝ) : Continuous (openingFourierWave t) := by
  unfold openingFourierWave
  fun_prop

theorem opening_fourier_wave_memLp (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    MemLp (openingFourierWave t) 2 μ :=
  MemLp.of_bound (opening_fourier_wave_continuous t).aestronglyMeasurable 1 (Eventually.of_forall fun x => (opening_fourier_wave_norm t x).le)

def openingGaussianWave (t : ℝ) : OpeningGaussianCarrier := (opening_fourier_wave_memLp openingGaussianLaw t).toLp _

theorem opening_gaussian_wave_ae (t : ℝ) : ⇑(openingGaussianWave t) =ᵐ[openingGaussianLaw] openingFourierWave t :=
  (opening_fourier_wave_memLp openingGaussianLaw t).coeFn_toLp

theorem opening_gaussian_wave_gram (s t : ℝ) :
    ⟪openingGaussianWave s,openingGaussianWave t⟫ = (Real.exp (-(s-t)^2/2):ℂ) := by
  rw [L2.inner_def]
  calc _ = ∫ x, openingFourierWave (t-s) x ∂openingGaussianLaw := by
             apply integral_congr_ae
             filter_upwards [opening_gaussian_wave_ae s,opening_gaussian_wave_ae t] with x hs ht
             rw [hs,ht,RCLike.inner_apply,opening_fourier_wave_conj,←opening_fourier_wave_add,sub_eq_add_neg]
       _ = charFun openingGaussianLaw (t-s) := (charFun_apply_real _).symm
       _ = _ := by
             rw [charFun_gaussianReal,Complex.ofReal_exp]
             congr 1
             push_cast
             ring

end UV
