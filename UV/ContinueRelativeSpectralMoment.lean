import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-! The scalar positive-measure step of the relative-chord rest-fibre
obstruction. The carrier frequency is real, and the spectral energy ranges
over both signs. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace UV.ContinueRelativeSpectralMoment

/-- A diagonal entry of the proposed positive spectral law. -/
def kernel (ω E : ℝ) : ℂ := ((ω : ℂ) * Complex.I + (E : ℂ))⁻¹

def weight (ω E : ℝ) : ℝ := ω^2/(ω^2+E^2)

def coefficient (μ : Measure ℝ) (ω : ℝ) : ℂ := ∫ E, kernel ω E ∂μ

def massSignal (μ : Measure ℝ) (ω : ℝ) : ℝ := -ω * (coefficient μ ω).im

def varianceSignal (μ : Measure ℝ) (ℓ ω : ℝ) : ℝ :=
  ω^2 * (1 + ω * (coefficient μ ω).im) -
    2*ℓ*ω^2*(coefficient μ ω).re - ℓ^2*ω*(coefficient μ ω).im

theorem kernel_re (ω E : ℝ) : (kernel ω E).re = E/(ω^2+E^2) := by
  simp [kernel, Complex.inv_re, Complex.normSq_apply, pow_two, add_comm]

theorem kernel_im (ω E : ℝ) : (kernel ω E).im = -ω/(ω^2+E^2) := by
  simp [kernel, Complex.inv_im, Complex.normSq_apply, pow_two, add_comm]

private theorem weight_nonneg (ω E : ℝ) : 0 ≤ weight ω E := by
  unfold weight
  positivity

private theorem weight_le_one (ω E : ℝ) (hω : 0 < ω) : weight ω E ≤ 1 := by
  unfold weight
  exact (div_le_one₀ (by positivity)).mpr (le_add_of_nonneg_right (sq_nonneg _))

private theorem weight_limit {ω : ℕ → ℝ} (hω : ∀ n, 0 < ω n)
    (htop : Tendsto ω atTop atTop) (E : ℝ) :
    Tendsto (fun n ↦ weight (ω n) E) atTop (𝓝 1) := by
  have hInv : Tendsto (fun n ↦ (ω n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp htop
  have hden : Tendsto (fun n ↦ 1 + (E * (ω n)⁻¹)^2) atTop (𝓝 (1 : ℝ)) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add ((hInv.const_mul E).pow 2))
  have hlim := tendsto_const_nhds (x := (1 : ℝ)) |>.div hden one_ne_zero
  rw [div_one] at hlim
  apply hlim.congr
  intro n
  have hn := hω n
  change 1/(1+(E*(ω n)⁻¹)^2) = (ω n)^2/((ω n)^2+E^2)
  have h₁ : 0 < 1+(E*(ω n)⁻¹)^2 := by positivity
  have h₂ : 0 < (ω n)^2+E^2 := by positivity
  field_simp [hn.ne', h₁.ne', h₂.ne']

/-- Nonnegative Fatou inequality along the physical frequency sequence. -/
private theorem limit_lintegral_le {μ : Measure ℝ} {F : ℕ → ℝ → ℝ≥0∞} {f : ℝ → ℝ≥0∞}
    {L : ℝ≥0∞} (hF : ∀ n, Measurable (F n))
    (hf : ∀ E, Tendsto (fun n ↦ F n E) atTop (𝓝 (f E)))
    (hL : Tendsto (fun n ↦ ∫⁻ E, F n E ∂μ) atTop (𝓝 L)) : (∫⁻ E, f E ∂μ) ≤ L := by
  calc
    _ = ∫⁻ E, liminf (fun n ↦ F n E) atTop ∂μ :=
      lintegral_congr fun E ↦ (hf E).liminf_eq.symm
    _ ≤ _ := lintegral_liminf_le hF
    _ = _ := hL.liminf_eq

theorem massSignal_eq {μ : Measure ℝ} {ω : ℝ}
    (hi : Integrable (kernel ω) μ) :
    massSignal μ ω = ∫ E, weight ω E ∂μ := by
  unfold massSignal coefficient
  change -ω * RCLike.im (∫ E, kernel ω E ∂μ) = _
  rw [← integral_im hi, ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro E
  change -ω * (kernel ω E).im = _
  rw [kernel_im, weight]
  ring

private theorem massSignal_lintegral {μ : Measure ℝ} {ω : ℝ}
    (hi : Integrable (kernel ω) μ) :
    ENNReal.ofReal (massSignal μ ω) = ∫⁻ E, ENNReal.ofReal (weight ω E) ∂μ := by
  rw [massSignal_eq hi]
  apply ofReal_integral_eq_lintegral_ofReal
  · have he : weight ω = fun E ↦ -ω * RCLike.im (kernel ω E) := by
      ext E
      change _ = -ω * (kernel ω E).im
      rw [weight, kernel_im]
      ring
    rw [he]
    exact hi.im.const_mul _
  · exact ae_of_all _ (weight_nonneg ω)

/-- The leading imaginary asymptotic alone recovers the total mass. -/
theorem mass_one {μ : Measure ℝ} {ω : ℕ → ℝ}
    (hω : ∀ n, 0 < ω n) (htop : Tendsto ω atTop atTop)
    (hi : ∀ n, Integrable (kernel (ω n)) μ)
    (hm : Tendsto (fun n ↦ massSignal μ (ω n)) atTop (𝓝 1)) :
    μ univ = 1 := by
  have hL : Tendsto (fun n ↦ ∫⁻ E, ENNReal.ofReal (weight (ω n) E) ∂μ) atTop (𝓝 1) := by
    simpa only [massSignal_lintegral (hi _), ENNReal.ofReal_one] using ENNReal.tendsto_ofReal hm
  apply le_antisymm
  · simpa using limit_lintegral_le (μ := μ) (f := fun _ ↦ (1 : ℝ≥0∞))
      (fun n ↦ by unfold weight; fun_prop)
      (fun E ↦ by simpa only [ENNReal.ofReal_one] using
        ENNReal.tendsto_ofReal (weight_limit hω htop E)) hL
  · apply le_of_tendsto hL
    exact Eventually.of_forall fun n ↦ by
      rw [← lintegral_one]
      exact lintegral_mono fun E ↦ ENNReal.ofReal_le_one.mpr (weight_le_one _ _ (hω n))

private theorem varianceSignal_lintegral {μ : Measure ℝ} {ℓ ω : ℝ}
    (hμ : μ univ = 1) (hω : 0 < ω) (hi : Integrable (kernel ω) μ) :
    ENNReal.ofReal (varianceSignal μ ℓ ω) =
      ∫⁻ E, ENNReal.ofReal (weight ω E * (E-ℓ)^2) ∂μ := by
  let A := ω^3-ℓ^2*ω
  let B := -(2*ℓ*ω^2)
  let f := fun E : ℝ ↦ ω^2 + A * RCLike.im (kernel ω E) + B * RCLike.re (kernel ω E)
  haveI : IsProbabilityMeasure μ := ⟨hμ⟩
  have hiA : Integrable (fun E ↦ A * RCLike.im (kernel ω E)) μ := hi.im.const_mul _
  have hiB : Integrable (fun E ↦ B * RCLike.re (kernel ω E)) μ := hi.re.const_mul _
  have hifi : Integrable f μ := ((integrable_const _).add hiA).add hiB
  have he (E : ℝ) : f E = weight ω E * (E-ℓ)^2 := by
    change ω^2 + A * (kernel ω E).im + B * (kernel ω E).re = _
    rw [kernel_im, kernel_re, weight]
    dsimp [A, B]
    field_simp [show 0 < ω^2+E^2 by positivity]
    ring
  have hnn : 0 ≤ᵐ[μ] f := ae_of_all _ fun E ↦ he E ▸ mul_nonneg (weight_nonneg _ _) (sq_nonneg _)
  have hcalc : (∫ E, f E ∂μ) = varianceSignal μ ℓ ω := by
    have hi₁ : Integrable (fun E ↦ ω^2 + A * RCLike.im (kernel ω E)) μ :=
      (integrable_const _).add hiA
    change (∫ E, ω^2 + A * RCLike.im (kernel ω E) + B * RCLike.re (kernel ω E) ∂μ) = _
    rw [integral_add hi₁ hiB, integral_add (integrable_const _) hiA, integral_const,
      integral_const_mul, integral_const_mul, integral_im hi, integral_re hi]
    unfold varianceSignal coefficient
    change μ.real univ * ω^2 + A * (∫ E, kernel ω E ∂μ).im +
        B * (∫ E, kernel ω E ∂μ).re = _
    rw [measureReal_def, hμ, ENNReal.toReal_one]
    dsimp [A, B]
    ring
  rw [← hcalc, ofReal_integral_eq_lintegral_ofReal hifi hnn]
  exact lintegral_congr fun E ↦ congrArg ENNReal.ofReal (he E)

/-- The mass and centered second-moment limits force the single pole at `ℓ`. -/
theorem measure_eq_dirac_of_asymptotic {μ : Measure ℝ} {ω : ℕ → ℝ} {ℓ : ℝ}
    (hω : ∀ n, 0 < ω n) (htop : Tendsto ω atTop atTop)
    (hi : ∀ n, Integrable (kernel (ω n)) μ)
    (hm : Tendsto (fun n ↦ massSignal μ (ω n)) atTop (𝓝 1))
    (hv : Tendsto (fun n ↦ varianceSignal μ ℓ (ω n)) atTop (𝓝 0)) :
    μ = Measure.dirac ℓ := by
  have hμ : μ univ = 1 := mass_one hω htop hi hm
  have hL : Tendsto (fun n ↦ ∫⁻ E, ENNReal.ofReal (weight (ω n) E * (E-ℓ)^2) ∂μ)
      atTop (𝓝 0) := by
    simpa only [varianceSignal_lintegral hμ (hω _) (hi _), ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal hv
  have hz : (∫⁻ E, ENNReal.ofReal ((E-ℓ)^2) ∂μ) = 0 := by
    refine le_antisymm (limit_lintegral_le (fun n ↦ by unfold weight; fun_prop) ?_ hL) (zero_le _)
    intro E
    simpa only [one_mul] using ENNReal.tendsto_ofReal ((weight_limit hω htop E).mul_const ((E-ℓ)^2))
  have he : ∀ᵐ E ∂μ, E = ℓ := by
    have h := (lintegral_eq_zero_iff (μ := μ) (f := fun E ↦ ENNReal.ofReal ((E-ℓ)^2))
      (by fun_prop)).mp hz
    filter_upwards [h] with E hE
    have hs : (E-ℓ)^2 ≤ 0 := ENNReal.ofReal_eq_zero.mp hE
    nlinarith [sq_nonneg (E-ℓ)]
  refine Measure.ext_of_lintegral _ fun f _ ↦ ?_
  rw [lintegral_dirac]
  rw [lintegral_congr_ae (he.mono fun E hE ↦ congrArg f hE), lintegral_const, hμ, mul_one]

theorem dirac_spectral_moments (ℓ : ℝ) :
    (Measure.dirac ℓ) univ = 1 ∧ (∫ E, E ∂Measure.dirac ℓ) = ℓ ∧
      (∫ E, E^2 ∂Measure.dirac ℓ) = ℓ^2 := by simp

private theorem freeVariance (ℓ ω : ℝ) (hω : 0 < ω) :
    ω^2 * (1 + ω * (kernel ω ℓ).im) - 2*ℓ*ω^2*(kernel ω ℓ).re -
      ℓ^2*ω*(kernel ω ℓ).im = 0 := by
  rw [kernel_im, kernel_re]
  field_simp [show 0 < ω^2+ℓ^2 by positivity]
  ring

/-- Inverse-cubic little-o agreement with the free resolvent suffices for the scalar rigidity. -/
theorem measure_eq_dirac_of_resolvent_error {μ : Measure ℝ} {ω : ℕ → ℝ} {ℓ : ℝ}
    (hω : ∀ n, 0 < ω n) (htop : Tendsto ω atTop atTop)
    (hi : ∀ n, Integrable (kernel (ω n)) μ)
    (herr : Tendsto (fun n ↦ (((ω n)^3 : ℝ) : ℂ) *
      (coefficient μ (ω n) - kernel (ω n) ℓ)) atTop (𝓝 0)) :
    μ = Measure.dirac ℓ := by
  let δ := fun n ↦ coefficient μ (ω n) - kernel (ω n) ℓ
  have hre : Tendsto (fun n ↦ (ω n)^3 * (δ n).re) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.zero_re, δ] using Complex.continuous_re.continuousAt.tendsto.comp herr
  have him : Tendsto (fun n ↦ (ω n)^3 * (δ n).im) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, Complex.zero_im, δ] using Complex.continuous_im.continuousAt.tendsto.comp herr
  have hinv : Tendsto (fun n ↦ (ω n)⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero.comp htop
  have hre₂ : Tendsto (fun n ↦ (ω n)^2 * (δ n).re) atTop (𝓝 0) := by
    have hh : Tendsto (fun n ↦ ((ω n)^3 * (δ n).re) * (ω n)⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using hre.mul hinv
    apply hh.congr
    intro n
    field_simp [(hω n).ne']
  have him₁ : Tendsto (fun n ↦ ω n * (δ n).im) atTop (𝓝 0) := by
    have hh : Tendsto (fun n ↦ ((ω n)^3 * (δ n).im) * ((ω n)⁻¹)^2) atTop (𝓝 0) := by
      simpa only [zero_mul] using him.mul (hinv.pow 2)
    apply hh.congr
    intro n
    field_simp [(hω n).ne']
  apply measure_eq_dirac_of_asymptotic hω htop hi
  · have hg : Tendsto (fun n ↦ weight (ω n) ℓ - ω n * (δ n).im) atTop (𝓝 1) := by
      simpa only [sub_zero] using (weight_limit hω htop ℓ).sub him₁
    apply hg.congr
    intro n
    change weight (ω n) ℓ - ω n * ((coefficient μ (ω n)).im - (kernel (ω n) ℓ).im) =
      massSignal μ (ω n)
    rw [weight, kernel_im, massSignal]
    ring
  · have hg : Tendsto (fun n ↦ (ω n)^3 * (δ n).im -
        (2*ℓ) * ((ω n)^2 * (δ n).re) - ℓ^2 * (ω n * (δ n).im)) atTop (𝓝 0) := by
      simpa only [mul_zero, sub_zero] using (him.sub (hre₂.const_mul (2*ℓ))).sub (him₁.const_mul (ℓ^2))
    apply hg.congr
    intro n
    have hz := freeVariance ℓ (ω n) (hω n)
    unfold varianceSignal
    simp only [δ, Complex.sub_im, Complex.sub_re]
    nlinarith only [hz]

end UV.ContinueRelativeSpectralMoment
