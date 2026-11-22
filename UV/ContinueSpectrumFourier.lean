import UV.ResumeSpectrumBulk
import Mathlib.Analysis.Fourier.Inversion

/-! Exact Cauchy cosine transforms derived from actual Fourier inversion.
These provide the oscillatory integrals for nonboundary layer readouts. -/

noncomputable section
open MeasureTheory Real Complex Filter Set
open scoped Topology FourierTransform RealInnerProductSpace

namespace UV.RevisionSpectrum

def continueLaplaceFunction (c t : ℝ) : ℂ :=
  (Real.exp (-(2*Real.pi*c)*|t|) : ℂ)

theorem continueLaplaceFunction_continuous (c : ℝ) : Continuous (continueLaplaceFunction c) := by
  unfold continueLaplaceFunction
  fun_prop

theorem continueLaplaceFunction_integrable {c : ℝ} (hc : 0<c) :
    Integrable (continueLaplaceFunction c) := by
  have hcp : 0<2*Real.pi*c := by positivity
  have hL : IntegrableOn (continueLaplaceFunction c) (Iic 0) := by
    have hi : IntegrableOn (fun t : ℝ => (Real.exp ((2*Real.pi*c)*t):ℂ)) (Iic 0) :=
      (integrableOn_exp_mul_Iic (a:=2*Real.pi*c) hcp 0).ofReal
    apply hi.congr_fun _ measurableSet_Iic
    intro t ht
    change t≤0 at ht
    simp only [continueLaplaceFunction,abs_of_nonpos ht,neg_mul_neg]
  have hR : IntegrableOn (continueLaplaceFunction c) (Ioi 0) := by
    have hi : IntegrableOn (fun t : ℝ => (Real.exp (-(2*Real.pi*c)*t):ℂ)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (a:=-(2*Real.pi*c)) (neg_lt_zero.mpr hcp) 0).ofReal
    apply hi.congr_fun _ measurableSet_Ioi
    intro t ht
    change 0<t at ht
    unfold continueLaplaceFunction
    rw [abs_of_pos ht]
  simpa only [Iic_union_Ioi, IntegrableOn, Measure.restrict_univ] using hL.union hR

theorem continueLaplaceFunction_fourier {c : ℝ} (hc : 0<c) (k : ℝ) :
    𝓕 (continueLaplaceFunction c) k =
      ((c/(Real.pi*(k^2+c^2)) : ℝ) : ℂ) := by
  let aL : ℂ := (2*Real.pi*c:ℝ) - (2*Real.pi*k:ℝ)*Complex.I
  let aR : ℂ := -(2*Real.pi*c:ℝ) - (2*Real.pi*k:ℝ)*Complex.I
  let g : ℝ → ℂ := fun t => Complex.exp ((↑(-2*Real.pi*(t*k)):ℂ)*Complex.I) * continueLaplaceFunction c t
  have heL : EqOn g (fun t : ℝ => Complex.exp (aL*t)) (Iic 0) := by
    intro t ht
    dsimp [g,continueLaplaceFunction,aL]
    rw [abs_of_nonpos ht,Complex.ofReal_exp,← Complex.exp_add]
    congr 1
    push_cast
    ring
  have heR : EqOn g (fun t : ℝ => Complex.exp (aR*t)) (Ioi 0) := by
    intro t ht
    dsimp [g,continueLaplaceFunction,aR]
    rw [abs_of_pos ht,Complex.ofReal_exp,← Complex.exp_add]
    congr 1
    push_cast
    ring
  have haL : 0<aL.re := by
    simpa [aL] using mul_pos (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos) hc
  have haR : aR.re<0 := by
    simpa [aR] using neg_lt_zero.mpr (mul_pos (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos) hc)
  have hL : IntegrableOn g (Iic 0) :=
    (integrableOn_exp_mul_complex_Iic haL 0).congr_fun (fun t ht => (heL ht).symm) measurableSet_Iic
  have hR : IntegrableOn g (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi haR 0).congr_fun (fun t ht => (heR ht).symm) measurableSet_Ioi
  have hFT : 𝓕 (continueLaplaceFunction c) k = ∫ t : ℝ,g t := by
    rw [Real.fourierIntegral_eq']
    apply integral_congr_ae
    filter_upwards with t
    simp [g,smul_eq_mul,mul_comm]
  rw [hFT,← intervalIntegral.integral_Iic_add_Ioi hL hR,
    setIntegral_congr_fun measurableSet_Iic heL,
    setIntegral_congr_fun measurableSet_Ioi heR,
    integral_exp_mul_complex_Iic haL 0,integral_exp_mul_complex_Ioi haR 0]
  norm_num only [Complex.ofReal_zero,mul_zero,Complex.exp_zero]
  have hreal : k^2+c^2≠0 := by positivity
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    simp [aL,aR,Complex.div_re,Complex.normSq_apply,pow_two]
    field_simp
    ring
  · simp only [Complex.ofReal_im]
    simp [aL,aR,Complex.div_im,Complex.normSq_apply]

theorem continueCauchy_integrable {c : ℝ} (hc : 0<c) :
    Integrable (fun k : ℝ => (k^2+c^2)⁻¹) := by
  have hs := (integrable_comp_mul_left_iff (fun k : ℝ => (1+k^2)⁻¹) (inv_ne_zero hc.ne')).mpr
    integrable_inv_one_add_sq
  have ht := hs.const_mul ((c^2)⁻¹)
  apply ht.congr
  filter_upwards with k
  have h₁ : k^2+c^2≠0 := by positivity
  have h₂ : 1+(c⁻¹*k)^2≠0 := by positivity
  field_simp
  ring

theorem continueLaplaceFunction_fourier_integrable {c : ℝ} (hc : 0<c) :
    Integrable (𝓕 (continueLaplaceFunction c)) := by
  have he : 𝓕 (continueLaplaceFunction c) =
      fun k : ℝ => ((c/Real.pi:ℝ):ℂ) * (((k^2+c^2)⁻¹:ℝ):ℂ) := by
    funext k
    rw [continueLaplaceFunction_fourier hc]
    push_cast
    field_simp
  rw [he]
  exact (continueCauchy_integrable hc).ofReal.const_mul _

def continueCauchyWave (c r k : ℝ) : ℂ :=
  Complex.exp ((k*r:ℝ)*Complex.I) * (((k^2+c^2)⁻¹:ℝ):ℂ)

theorem continueCauchyWave_integrable {c : ℝ} (hc : 0<c) (r : ℝ) :
    Integrable (continueCauchyWave c r) := by
  apply (continueCauchy_integrable hc).mono'
  · exact (by unfold continueCauchyWave; fun_prop : Measurable (continueCauchyWave c r)).aestronglyMeasurable
  · filter_upwards with k
    dsimp only [continueCauchyWave]
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0≤(k^2+c^2)⁻¹)]
    simp [Complex.norm_exp,Complex.mul_re]

theorem continueCauchyWave_integral {c : ℝ} (hc : 0<c) (r : ℝ) :
    (∫ k : ℝ,continueCauchyWave c r k) = ((Real.pi/c*Real.exp (-c*|r|):ℝ):ℂ) := by
  have hInv := (continueLaplaceFunction_integrable hc).fourier_inversion
    (continueLaplaceFunction_fourier_integrable hc)
    ((continueLaplaceFunction_continuous c).continuousAt (x:=r/(2*Real.pi)))
  rw [Real.fourierIntegralInv_eq'] at hInv
  simp_rw [continueLaplaceFunction_fourier hc] at hInv
  have he (k : ℝ) :
      Complex.exp ((↑(2*Real.pi*⟪k,r/(2*Real.pi)⟫):ℂ)*Complex.I) •
        (((c/(Real.pi*(k^2+c^2)):ℝ)):ℂ) =
      (((c/Real.pi:ℝ)):ℂ) * continueCauchyWave c r k := by
    have hex : 2*Real.pi*⟪k,r/(2*Real.pi)⟫=k*r := by
      simp only [RCLike.inner_apply,conj_trivial]
      field_simp
    rw [hex]
    dsimp only [continueCauchyWave,smul_eq_mul]
    push_cast
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  simp_rw [he] at hInv
  rw [integral_const_mul] at hInv
  have hexp : -(2*Real.pi*c)*|r/(2*Real.pi)| = -c*|r| := by
    rw [abs_div,abs_of_pos (by positivity : 0<2*Real.pi)]
    field_simp
  rw [continueLaplaceFunction,hexp] at hInv
  have hcoef : (((c/Real.pi:ℝ)):ℂ)≠0 := by exact_mod_cast (div_pos hc Real.pi_pos).ne'
  calc
    _ = (((c/Real.pi:ℝ)):ℂ)⁻¹ *
        ((((c/Real.pi:ℝ)):ℂ) * ∫ k : ℝ,continueCauchyWave c r k) := by field_simp
    _ = _ := by rw [hInv]; push_cast; field_simp

theorem continueCauchyCos_integrable {c : ℝ} (hc : 0<c) (r : ℝ) :
    Integrable (fun k : ℝ => Real.cos (k*r)*(k^2+c^2)⁻¹) := by
  apply (continueCauchy_integrable hc).mono'
  · exact (by fun_prop : Measurable (fun k : ℝ => Real.cos (k*r)*(k^2+c^2)⁻¹)).aestronglyMeasurable
  · filter_upwards with k
    rw [norm_mul,Real.norm_eq_abs,Real.norm_of_nonneg (by positivity : 0≤(k^2+c^2)⁻¹)]
    exact mul_le_of_le_one_left (by positivity) (Real.abs_cos_le_one _)

theorem continueCauchyCos_integral {c : ℝ} (hc : 0<c) (r : ℝ) :
    (∫ k : ℝ in Ioi 0,Real.cos (k*r)*(k^2+c^2)⁻¹) =
      Real.pi/(2*c)*Real.exp (-c*|r|) := by
  have hre : (∫ k : ℝ,continueCauchyWave c r k).re =
      ∫ k : ℝ,Real.cos (k*r)*(k^2+c^2)⁻¹ := by
    calc
      _ = ∫ k : ℝ,(continueCauchyWave c r k).re := by
        simpa only [RCLike.re_to_complex] using (integral_re (continueCauchyWave_integrable hc r)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with k
        simp only [continueCauchyWave,Complex.mul_re,Complex.ofReal_re,
          Complex.ofReal_im,mul_zero,sub_zero]
        simp [Complex.exp_re]
  have hw := congrArg Complex.re (continueCauchyWave_integral hc r)
  rw [hre,Complex.ofReal_re] at hw
  have hi := continueCauchyCos_integrable hc r
  have hn := integral_comp_neg_Ioi (f:=fun k : ℝ => Real.cos (k*r)*(k^2+c^2)⁻¹) 0
  simp only [neg_zero,neg_mul,Real.cos_neg,neg_sq] at hn
  have hs := intervalIntegral.integral_Iic_add_Ioi (b:=0) hi.integrableOn hi.integrableOn
  rw [← hn,hw] at hs
  field_simp at hs ⊢
  simp_rw [mul_comm _ r] at hs
  nlinarith [hs]

end UV.RevisionSpectrum
