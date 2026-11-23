import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Basic

/-! The two-frequency test for a positive normalized carrier spectral law. -/

noncomputable section

namespace UV.RelativeSoft

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- The literal Cauchy denominator on a rest eigenspinor. -/
def carrierCauchyKernel (ω E : ℝ) : ℂ := (Complex.I * (ω : ℂ) + (E : ℂ))⁻¹

/-- The scalar rest-fibre response of a positive normalized spectral measure. -/
def carrierSpectralResponse (μ : Measure ℝ) (ω : ℝ) : ℂ :=
  ∫ E, carrierCauchyKernel ω E ∂μ

/-- The observable defect VΩ determined solely by the high-frequency response. -/
def carrierSpectralDefect (Ω ell : ℝ) (gΩ : ℂ) : ℝ :=
  Ω ^ 2 * (1 + Ω * gΩ.im) - 2 * ell * Ω ^ 2 * gΩ.re - ell ^ 2 * Ω * gΩ.im

private theorem carrierDenominator_normSq (ω E : ℝ) :
    Complex.normSq (Complex.I * (ω : ℂ) + (E : ℂ)) = ω ^ 2 + E ^ 2 := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

private theorem carrierDenominator_ne_zero {ω : ℝ} (hω : 0 < ω) (E : ℝ) :
    Complex.I * (ω : ℂ) + (E : ℂ) ≠ 0 := by
  intro hz
  have h := Complex.normSq_eq_zero.mpr hz
  rw [carrierDenominator_normSq] at h
  exact (show 0 < ω ^ 2 + E ^ 2 by positivity).ne' h

theorem carrierCauchyKernel_re (ω E : ℝ) :
    (carrierCauchyKernel ω E).re = E / (ω ^ 2 + E ^ 2) := by
  simp [carrierCauchyKernel, Complex.inv_re, carrierDenominator_normSq, Complex.mul_re]

theorem carrierCauchyKernel_im (ω E : ℝ) :
    (carrierCauchyKernel ω E).im = -ω / (ω ^ 2 + E ^ 2) := by
  simp [carrierCauchyKernel, Complex.inv_im, carrierDenominator_normSq, Complex.mul_im]

private theorem carrierCauchyKernel_measurable (ω : ℝ) :
    Measurable (carrierCauchyKernel ω) := by
  unfold carrierCauchyKernel
  fun_prop

theorem carrierCauchyKernel_integrable {μ : Measure ℝ} [IsFiniteMeasure μ]
    {ω : ℝ} (hω : 0 < ω) : Integrable (carrierCauchyKernel ω) μ := by
  apply (integrable_const ω⁻¹).mono' (carrierCauchyKernel_measurable ω).aestronglyMeasurable
  refine Eventually.of_forall fun E => ?_
  apply le_trans (le_abs_self _) (abs_le_of_sq_le_sq ?_ (inv_nonneg.mpr hω.le))
  rw [carrierCauchyKernel, Complex.sq_norm, Complex.normSq_inv, carrierDenominator_normSq, inv_pow]
  exact inv_anti₀ (by positivity) (le_add_of_nonneg_right (sq_nonneg E))

/-- The nonnegative squared-defect integrand on the spectral line. -/
def carrierDefectIntegrand (Ω ell E : ℝ) : ℝ :=
  Ω ^ 2 * (E - ell) ^ 2 / (Ω ^ 2 + E ^ 2)

private theorem carrierDefectIntegrand_expand {Ω : ℝ} (hΩ : 0 < Ω) (ell E : ℝ) :
    carrierDefectIntegrand Ω ell E = Ω ^ 2 +
      (Ω ^ 3 - ell ^ 2 * Ω) * (carrierCauchyKernel Ω E).im -
      2 * ell * Ω ^ 2 * (carrierCauchyKernel Ω E).re := by
  rw [carrierDefectIntegrand, carrierCauchyKernel_re, carrierCauchyKernel_im]
  have hn : Ω ^ 2 + E ^ 2 ≠ 0 := by positivity
  field_simp
  ring

private theorem carrierDefectIntegrand_integrable {μ : Measure ℝ} [IsFiniteMeasure μ]
    {Ω : ℝ} (hΩ : 0 < Ω) (ell : ℝ) : Integrable (carrierDefectIntegrand Ω ell) μ := by
  have hk := carrierCauchyKernel_integrable (μ := μ) hΩ
  have him := (Complex.imCLM.integrable_comp hk).const_mul (Ω ^ 3 - ell ^ 2 * Ω)
  have hre := (Complex.reCLM.integrable_comp hk).const_mul (2 * ell * Ω ^ 2)
  have hi := ((integrable_const (Ω ^ 2)).add him).sub hre
  exact hi.congr (Eventually.of_forall fun E => (carrierDefectIntegrand_expand hΩ ell E).symm)

/-- The two-frequency observable has the exact positive spectral integral. -/
theorem carrierSpectralDefect_eq_integral {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {Ω : ℝ} (hΩ : 0 < Ω) (ell : ℝ) :
    carrierSpectralDefect Ω ell (carrierSpectralResponse μ Ω) =
      ∫ E, carrierDefectIntegrand Ω ell E ∂μ := by
  have hk := carrierCauchyKernel_integrable (μ := μ) hΩ
  have him := (Complex.imCLM.integrable_comp hk).const_mul (Ω ^ 3 - ell ^ 2 * Ω)
  have hre := (Complex.reCLM.integrable_comp hk).const_mul (2 * ell * Ω ^ 2)
  have hi (E : ℝ) := carrierDefectIntegrand_expand hΩ ell E
  unfold carrierSpectralDefect carrierSpectralResponse
  simp_rw [hi]
  have hsub := integral_sub ((integrable_const (Ω ^ 2)).add him) hre
  simp only [Pi.add_apply, Complex.imCLM_apply, Complex.reCLM_apply] at hsub
  have hadd := integral_add (integrable_const (Ω ^ 2)) him
  simp only [Complex.imCLM_apply] at hadd
  rw [hsub, hadd]
  simp only [integral_const, measureReal_univ_eq_one, one_smul, integral_const_mul]
  have hre' : (∫ E, (carrierCauchyKernel Ω E).re ∂μ) =
      (∫ E, carrierCauchyKernel Ω E ∂μ).re := integral_re hk
  have him' : (∫ E, (carrierCauchyKernel Ω E).im ∂μ) =
      (∫ E, carrierCauchyKernel Ω E ∂μ).im := integral_im hk
  rw [hre', him']
  ring

private def carrierResidual (ω ell E : ℝ) : ℂ :=
  ((ell - E : ℝ) : ℂ) * carrierCauchyKernel ω E

private theorem carrierResidual_eq {ω : ℝ} (hω : 0 < ω) (ell E : ℝ) :
    carrierResidual ω ell E =
      (Complex.I * (ω : ℂ) + (ell : ℂ)) * carrierCauchyKernel ω E - 1 := by
  simp only [carrierResidual, carrierCauchyKernel, Complex.ofReal_sub]
  field_simp [carrierDenominator_ne_zero hω E]
  ring

private theorem carrierResidual_normSq (ω ell E : ℝ) :
    ‖carrierResidual ω ell E‖ ^ 2 = (E - ell) ^ 2 / (ω ^ 2 + E ^ 2) := by
  rw [carrierResidual, carrierCauchyKernel, Complex.sq_norm, Complex.normSq_mul,
    Complex.normSq_ofReal, Complex.normSq_inv, carrierDenominator_normSq, div_eq_mul_inv]
  ring

private theorem carrierResidual_bound {ω Ω : ℝ} (hω : 0 < ω) (hΩ : ω ≤ Ω) (ell E : ℝ) :
    ‖carrierResidual ω ell E‖ ^ 2 ≤ ω⁻¹ ^ 2 * carrierDefectIntegrand Ω ell E := by
  have hΩp := hω.trans_le hΩ
  have hωs : 0 < ω ^ 2 := by positivity
  have hΩd : 0 < Ω ^ 2 + E ^ 2 := by positivity
  have hωd : 0 < ω ^ 2 + E ^ 2 := by positivity
  have hden : 0 < Ω ^ 2 * (ω ^ 2 + E ^ 2) := by positivity
  have hr : (Ω ^ 2 + E ^ 2) / (Ω ^ 2 * (ω ^ 2 + E ^ 2)) ≤ ω⁻¹ ^ 2 := by
    rw [inv_pow, inv_eq_one_div]
    apply (div_le_div_iff₀ hden hωs).2
    have hsq := pow_le_pow_left₀ hω.le hΩ 2
    nlinarith [mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg E)]
  rw [carrierResidual_normSq]
  calc
    _ = carrierDefectIntegrand Ω ell E * ((Ω ^ 2 + E ^ 2) / (Ω ^ 2 * (ω ^ 2 + E ^ 2))) := by
      unfold carrierDefectIntegrand
      field_simp
    _ ≤ carrierDefectIntegrand Ω ell E * ω⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_left hr (by unfold carrierDefectIntegrand; positivity)
    _ = _ := mul_comm _ _

private theorem carrierResidual_integral {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {ω : ℝ} (hω : 0 < ω) (ell : ℝ) :
    (∫ E, carrierResidual ω ell E ∂μ) =
      (Complex.I * (ω : ℂ) + (ell : ℂ)) * carrierSpectralResponse μ ω - 1 := by
  have hk := carrierCauchyKernel_integrable (μ := μ) hω
  simp_rw [carrierResidual_eq hω ell]
  rw [integral_sub (hk.const_mul _) (integrable_const 1), integral_const_mul]
  simp [carrierSpectralResponse]

/-- Two positive frequencies bound the squared error of a rest-fibre
resolvent represented by a normalized positive measure. -/
theorem carrierSpectral_two_frequency_bound {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {ω Ω : ℝ} (hω : 0 < ω) (hΩ : ω ≤ Ω) (ell : ℝ) :
    ‖(Complex.I * (ω : ℂ) + (ell : ℂ)) * carrierSpectralResponse μ ω - 1‖ ^ 2 ≤
      ω⁻¹ ^ 2 * carrierSpectralDefect Ω ell (carrierSpectralResponse μ Ω) := by
  let f := carrierResidual ω ell
  have hf : Integrable f μ := by
    have hk := carrierCauchyKernel_integrable (μ := μ) hω
    exact ((hk.const_mul _).sub (integrable_const (1 : ℂ))).congr
      (Eventually.of_forall fun E => (carrierResidual_eq hω ell E).symm)
  have hV := carrierDefectIntegrand_integrable (μ := μ) (hω.trans_le hΩ) ell
  have hP : ∀ E, ‖f E‖ ^ 2 ≤ ω⁻¹ ^ 2 * carrierDefectIntegrand Ω ell E :=
    carrierResidual_bound hω hΩ ell
  have hs : Integrable (fun E => ‖f E‖ ^ 2) μ := by
    refine (hV.const_mul (ω⁻¹ ^ 2)).mono' (hf.norm.aestronglyMeasurable.pow 2) ?_
    exact Eventually.of_forall fun E => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hP E
  have hLp := (memLp_two_iff_integrable_sq hf.norm.aestronglyMeasurable).2 hs
  have hCS := variance_nonneg (fun E => ‖f E‖) μ
  rw [variance_eq_sub hLp] at hCS
  rw [carrierSpectralDefect_eq_integral (hω.trans_le hΩ) ell, ← integral_const_mul,
    ← carrierResidual_integral hω ell]
  calc
    _ ≤ (∫ E, ‖f E‖ ∂μ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm f) 2
    _ ≤ ∫ E, ‖f E‖ ^ 2 ∂μ := sub_nonneg.mp hCS
    _ ≤ _ := integral_mono hs (hV.const_mul _) hP

/-- A strict violation at two finite frequencies excludes a positive
normalized representation that agrees at those frequencies. -/
theorem no_carrierSpectralLaw_of_two_frequency_violation (g : ℝ → ℂ)
    {ω Ω : ℝ} (hω : 0 < ω) (hΩ : ω ≤ Ω) (ell : ℝ)
    (hstrict : ω⁻¹ ^ 2 * carrierSpectralDefect Ω ell (g Ω) <
      ‖(Complex.I * (ω : ℂ) + (ell : ℂ)) * g ω - 1‖ ^ 2) :
    ¬ ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      g ω = carrierSpectralResponse μ ω ∧ g Ω = carrierSpectralResponse μ Ω := by
  rintro ⟨μ, hμ, hgω, hgΩ⟩
  letI := hμ
  rw [hgω, hgΩ] at hstrict
  exact hstrict.not_ge (carrierSpectral_two_frequency_bound hω hΩ ell)

/-- A vanishing high-frequency defect and a strict fixed-frequency deviation
force a violation at every sufficiently large finite frequency. -/
theorem carrierSpectral_eventually_violates (g : ℝ → ℂ) {ω : ℝ} (hω : 0 < ω) (ell : ℝ)
    (hfixed : (Complex.I * (ω : ℂ) + (ell : ℂ)) * g ω ≠ 1)
    (hV : Tendsto (fun Ω => carrierSpectralDefect Ω ell (g Ω)) atTop (𝓝 0)) :
    ∀ᶠ Ω in atTop, 0 < Ω ∧ ω ≤ Ω ∧ ω⁻¹ ^ 2 * carrierSpectralDefect Ω ell (g Ω) <
      ‖(Complex.I * (ω : ℂ) + (ell : ℂ)) * g ω - 1‖ ^ 2 := by
  have hpos : 0 < ‖(Complex.I * (ω : ℂ) + (ell : ℂ)) * g ω - 1‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hfixed))
  have hlim : Tendsto (fun Ω => ω⁻¹ ^ 2 * carrierSpectralDefect Ω ell (g Ω)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hV.const_mul (ω⁻¹ ^ 2)
  filter_upwards [eventually_ge_atTop ω, hlim.eventually_lt_const hpos] with Ω hΩ hstrict
  exact ⟨hω.trans_le hΩ, hΩ, hstrict⟩

end UV.RelativeSoft
