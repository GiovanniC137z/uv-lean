import UV.NextNativeBridgeKernel
import Mathlib.Analysis.Fourier.Inversion

/-! The free normal resolvent and its real-space Green readout have exactly
the source Fourier normalization. -/

noncomputable section
open MeasureTheory Set Complex Real
open scoped FourierTransform Topology

namespace UV.NextNativeBridge

private theorem normal_green_integrable {ω : ℝ} (hω : 0 < ω) :
    Integrable (normalGreenKernel ω) := by
  have h := UV.integrable_norm_pow_exp (E := ℝ) (μ := volume) hω 0
  change Integrable (fun t : ℝ => Real.exp (-ω * |t|) / (2 * ω))
  simpa only [pow_zero, one_mul, Real.norm_eq_abs, neg_mul] using
    h.div_const (2 * ω)

def normalGreenComplex (ω t : ℝ) : ℂ := ↑(normalGreenKernel ω t)

def normalResolvent (ω η : ℝ) : ℂ := ((η ^ 2 + ω ^ 2 : ℝ) : ℂ)⁻¹

/-- The forward transform, with the (2π) convention of mathlib,
equals the bare free normal resolvent at angular momentum (2πw). -/
theorem normal_green_fourier {ω : ℝ} (hω : 0 < ω) (w : ℝ) :
    𝓕 (normalGreenComplex ω) w = normalResolvent ω (2 * Real.pi * w) := by
  rw [Real.fourierIntegral_real_eq_integral_exp_smul]
  let b : ℝ := 2 * Real.pi * w
  let α : ℂ := -(ω : ℂ) - (b : ℂ) * Complex.I
  let β : ℂ := (ω : ℂ) - (b : ℂ) * Complex.I
  have hα : α.re < 0 := by simpa [α, Complex.mul_re] using neg_neg_of_pos hω
  have hβ : 0 < β.re := by simpa [β, Complex.mul_re] using hω
  let f := fun t : ℝ =>
    Complex.exp (↑(-2 * Real.pi * t * w) * Complex.I) • normalGreenComplex ω t
  change (∫ t, f t) = normalResolvent ω b
  have hf (t : ℝ) : f t =
      Complex.exp ((↑(-ω * |t|) : ℂ) + (↑(-2 * Real.pi * t * w) : ℂ) * Complex.I) /
        ↑(2 * ω) := by
    simp only [f, normalGreenComplex, normalGreenKernel, smul_eq_mul,
      Complex.ofReal_div, Complex.ofReal_exp, Complex.exp_add]
    ring
  have hpos (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      f t = Complex.exp (α * ↑t) / ↑(2 * ω) := by
    rw [hf, abs_of_pos (mem_Ioi.mp ht)]
    congr 2
    push_cast
    dsimp [α, b]
    push_cast
    ring
  have hneg (t : ℝ) (ht : t ∈ Iic (0 : ℝ)) :
      f t = Complex.exp (β * ↑t) / ↑(2 * ω) := by
    rw [hf, abs_of_nonpos (mem_Iic.mp ht)]
    congr 2
    push_cast
    dsimp [β, b]
    push_cast
    ring
  have hpI : IntegrableOn (fun t : ℝ => Complex.exp (α * ↑t) / ↑(2 * ω)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi hα 0).div_const ((2 * ω : ℝ) : ℂ)
  have hnI : IntegrableOn (fun t : ℝ => Complex.exp (β * ↑t) / ↑(2 * ω)) (Iic 0) :=
    (integrableOn_exp_mul_complex_Iic hβ 0).div_const ((2 * ω : ℝ) : ℂ)
  have hfI : Integrable f := by
    have hh := (hpI.congr_fun (fun t ht => (hpos t ht).symm) measurableSet_Ioi).union
      (hnI.congr_fun (fun t ht => (hneg t ht).symm) measurableSet_Iic)
    rwa [← compl_Ioi, union_compl_self, integrableOn_univ] at hh
  rw [← integral_add_compl measurableSet_Ioi hfI, compl_Ioi,
    setIntegral_congr_fun measurableSet_Ioi hpos, setIntegral_congr_fun measurableSet_Iic hneg,
    integral_div, integral_div, integral_exp_mul_complex_Ioi hα,
    integral_exp_mul_complex_Iic hβ]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have ha : α ≠ 0 := fun h => hα.ne (by rw [h, Complex.zero_re])
  have hb : β ≠ 0 := fun h => hβ.ne' (by rw [h, Complex.zero_re])
  have hs : (↑(b ^ 2 + ω ^ 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr ((add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hω))).ne'
  unfold normalResolvent
  field_simp [ha, hb, hs, hω.ne']
  dsimp [α, β]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem normal_resolvent_scaled_integrable {ω : ℝ} (hω : 0 < ω) :
    Integrable (fun w => normalResolvent ω (2 * Real.pi * w)) := by
  let c := min (ω ^ 2) ((2 * Real.pi) ^ 2)
  have hc : 0 < c := lt_min (sq_pos_of_pos hω) (sq_pos_of_pos (by positivity))
  have hh := integrable_inv_one_add_sq.const_mul c⁻¹
  apply hh.mono'
  · unfold normalResolvent
    exact (by fun_prop : Measurable (fun w : ℝ =>
      (↑((2 * Real.pi * w) ^ 2 + ω ^ 2 : ℝ) : ℂ)⁻¹)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun w => ?_
    have h₀ : 0 ≤ (2 * Real.pi * w) ^ 2 + ω ^ 2 := by positivity
    simp only [normalResolvent, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h₀]
    rw [← mul_inv]
    apply inv_anti₀ (mul_pos hc (by positivity))
    have h₁ := mul_le_mul_of_nonneg_right (min_le_right (ω ^ 2) ((2 * Real.pi) ^ 2))
      (sq_nonneg w)
    nlinarith [min_le_left (ω ^ 2) ((2 * Real.pi) ^ 2), mul_pow (2 * Real.pi) w 2]

/-- Exact inverse Green representation with the physical angular momentum
variable and (dη/(2π)) measure. -/
theorem normal_green_inverse_fourier {ω : ℝ} (hω : 0 < ω) (t : ℝ) :
    (∫ η : ℝ, Complex.exp (↑(η * t) * Complex.I) * normalResolvent ω η) /
      ↑(2 * Real.pi) = normalGreenComplex ω t := by
  have hI : Integrable (normalGreenComplex ω) :=
    (normal_green_integrable hω).ofReal
  have hTrans : Integrable (𝓕 (normalGreenComplex ω)) := by
    rw [show 𝓕 (normalGreenComplex ω) = (fun w => normalResolvent ω (2 * Real.pi * w))
      from funext (normal_green_fourier hω)]
    exact normal_resolvent_scaled_integrable hω
  have hc : Continuous (normalGreenComplex ω) := by
    unfold normalGreenComplex normalGreenKernel
    fun_prop
  have h := hI.fourier_inversion hTrans (hc.continuousAt (x := t))
  rw [Real.fourierIntegralInv_eq_fourierIntegral_neg, Real.fourierIntegral_real_eq_integral_exp_smul] at h
  simp_rw [normal_green_fourier hω, smul_eq_mul] at h
  let f := fun η : ℝ => Complex.exp (↑(η * t) * Complex.I) * normalResolvent ω η
  have hrescale : (∫ w : ℝ, f ((2 * Real.pi) * w)) = normalGreenComplex ω t := by
    refine Eq.trans ?_ h
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun w => ?_
    dsimp [f]
    rw [show 2 * Real.pi * w * t = -2 * Real.pi * w * -t by ring]
  have hscale := Measure.integral_comp_mul_left f (2 * Real.pi)
  rw [hrescale, abs_of_pos (by positivity : 0 < (2 * Real.pi)⁻¹)] at hscale
  simpa only [f, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using hscale.symm

end UV.NextNativeBridge
