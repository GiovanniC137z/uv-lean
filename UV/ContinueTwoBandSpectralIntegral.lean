import UV.ContinueTwoBandSpectralKernel
import Mathlib.MeasureTheory.Integral.Prod

/-! Exact frequency integration of the Euclidean two-band density trace. The external
transfer is an arbitrary real carrier frequency. The sign in the final formula is
the one in the stripped trace, before restoring the closed fermion-loop sign. -/

noncomputable section
open MeasureTheory Complex Filter
open scoped Topology

namespace UV.SectorPlane

open UV.RelativeSoft (carrierCauchyKernel carrierCauchyKernel_re carrierCauchyKernel_im)

/-- Two poles with the same signed-energy orientation integrate to zero, including
the coincident double pole. -/
theorem twoBand_same_band_frequency_zero {a b : ℝ} (hab : 0 < a*b) (ν : ℝ) :
    (∫ x : ℝ, carrierCauchyKernel x a * carrierCauchyKernel (x+ν) b) = 0 := by
  have ha := left_ne_zero_of_mul hab.ne'
  have hb := right_ne_zero_of_mul hab.ne'
  by_cases h : (b:ℂ)-a+I*ν = 0
  · have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    simp [Complex.mul_re,Complex.mul_im] at hr hi
    have he : b = a := by linarith
    subst b
    subst ν
    simpa using twoBand_signed_line_integral_coincident ha
  · rw [twoBand_signed_line_integral_distinct ha hb ν h]
    suffices a*(Real.pi/|a|)-b*(Real.pi/|b|) = 0 by simp [this]
    rcases mul_pos_iff.mp hab with ⟨ha',hb'⟩ | ⟨ha',hb'⟩
    · rw [abs_of_pos ha',abs_of_pos hb']
      field_simp
      ring
    · rw [abs_of_neg ha',abs_of_neg hb']
      field_simp
      ring

private def bandPairReal (a b ν x : ℝ) : ℝ :=
  (carrierCauchyKernel x a * carrierCauchyKernel (x+ν) b).re

private theorem band_pair_real_eq (a b ν x : ℝ) :
    bandPairReal a b ν x = (a*b-x*(x+ν))/((x^2+a^2)*((x+ν)^2+b^2)) := by
  simp only [bandPairReal,Complex.mul_re,carrierCauchyKernel_re,carrierCauchyKernel_im,
    div_eq_mul_inv,_root_.mul_inv_rev]
  ring

private theorem band_pair_real_integrable {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (ν : ℝ) :
    Integrable (bandPairReal a b ν) := (twoBand_signed_line_product_integrable ha hb ν).re

private theorem band_pair_same {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (ν : ℝ) :
    (∫ x, bandPairReal a b ν x) = 0 := by
  exact (integral_re (twoBand_signed_line_product_integrable ha.ne' hb.ne' ν)).trans
    (by rw [twoBand_same_band_frequency_zero (mul_pos ha hb)]; rfl)

private theorem band_pair_opposite {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (ν : ℝ) :
    (∫ x, bandPairReal a (-b) ν x) = -2*Real.pi*(a+b)/((a+b)^2+ν^2) := by
  have hne : ((-b:ℝ):ℂ)-a+I*ν ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    simp [Complex.mul_re] at h
    linarith
  have hc := twoBand_signed_line_integral_distinct ha.ne' (neg_ne_zero.mpr hb.ne') ν hne
  have hD : ((a+b)^2+ν^2) ≠ 0 := by positivity
  calc
    _ = (∫ x : ℝ, carrierCauchyKernel x a * carrierCauchyKernel (x+ν) (-b)).re :=
      integral_re (twoBand_signed_line_product_integrable ha.ne' (neg_ne_zero.mpr hb.ne') ν)
    _ = _ := by
      rw [hc,abs_of_pos ha,abs_neg,abs_of_pos hb]
      simp [Complex.div_re,Complex.mul_re,Complex.mul_im,Complex.normSq_apply]
      rw [show (-b-a)*(-b-a)+ν*ν = (a+b)^2+ν^2 by ring]
      field_simp
      ring

/-- The unnormalized convolution of the two positive Cauchy denominators, at
arbitrary transfer and with no distinct-energy hypothesis. -/
theorem twoBand_cauchy_convolution {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (ν : ℝ) :
    Integrable (fun x : ℝ => 1/((x^2+a^2)*((x+ν)^2+b^2))) ∧
    (∫ x : ℝ, 1/((x^2+a^2)*((x+ν)^2+b^2))) =
      Real.pi*(a+b)/(a*b*((a+b)^2+ν^2)) := by
  have hP := band_pair_real_integrable ha.ne' hb.ne' ν
  have hN := band_pair_real_integrable ha.ne' (neg_ne_zero.mpr hb.ne') ν
  have he (x : ℝ) : 1/((x^2+a^2)*((x+ν)^2+b^2)) =
      (2*a*b)⁻¹*(bandPairReal a b ν x-bandPairReal a (-b) ν x) := by
    rw [band_pair_real_eq,band_pair_real_eq,neg_sq]
    simp only [div_eq_mul_inv,← sub_mul]
    field_simp [ha.ne',hb.ne']
    ring
  simp_rw [he]
  refine ⟨(hP.sub hN).const_mul _,?_⟩
  rw [integral_const_mul,integral_sub hP hN,band_pair_same ha hb,band_pair_opposite ha hb]
  simp only [div_eq_mul_inv,_root_.mul_inv_rev]
  ring

/-- The manuscript's positive spectral convolution in the measure
`dξ/(2π)` for the two Euclidean time orderings. -/
theorem twoBand_lorentzian_convolution {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (ν : ℝ) :
    (∫ x : ℝ, (2*a/(x^2+a^2))*(2*b/((x+ν)^2+b^2)))/(2*Real.pi) =
      2*(a+b)/(ν^2+(a+b)^2) := by
  have he (x : ℝ) : (2*a/(x^2+a^2))*(2*b/((x+ν)^2+b^2)) =
      (4*a*b)*(1/((x^2+a^2)*((x+ν)^2+b^2))) := by
    simp only [div_eq_mul_inv,_root_.mul_inv_rev]
    ring
  simp_rw [he]
  rw [integral_const_mul,(twoBand_cauchy_convolution ha hb ν).2,add_comm (ν^2)]
  field_simp
  ring

private theorem band_trace_spectral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (c ν : ℝ) :
    Integrable (fun x : ℝ => 2*(c-x*(x+ν))/((x^2+a^2)*((x+ν)^2+b^2))) ∧
    (∫ x : ℝ, 2*(c-x*(x+ν))/((x^2+a^2)*((x+ν)^2+b^2))) =
      2*Real.pi*(-(1-c/(a*b))*(a+b)/((a+b)^2+ν^2)) := by
  have hP := band_pair_real_integrable ha.ne' hb.ne' ν
  have hN := band_pair_real_integrable ha.ne' (neg_ne_zero.mpr hb.ne') ν
  have he (x : ℝ) : 2*(c-x*(x+ν))/((x^2+a^2)*((x+ν)^2+b^2)) =
      (1+c/(a*b))*bandPairReal a b ν x+(1-c/(a*b))*bandPairReal a (-b) ν x := by
    rw [band_pair_real_eq,band_pair_real_eq,neg_sq]
    simp only [div_eq_mul_inv]
    field_simp [ha.ne',hb.ne']
    ring
  simp_rw [he]
  refine ⟨(hP.const_mul _).add (hN.const_mul _),?_⟩
  rw [integral_add (hP.const_mul _) (hN.const_mul _),integral_const_mul,integral_const_mul,
    band_pair_same ha hb,band_pair_opposite ha hb]
  ring

/-- The onsite trace has zero frequency integral at every positive mass and
every real external frequency. -/
theorem twoBand_onsite_trace_frequency {m : ℝ} (hm : 0 < m) (ν : ℝ) :
    Integrable (fun x : ℝ => twoBandTraceFormula m 0 0 x (x+ν)) ∧
      (∫ x : ℝ, twoBandTraceFormula m 0 0 x (x+ν)) = 0 := by
  have h := band_trace_spectral hm hm (m^2) ν
  have he : m^2/(m*m) = 1 := by rw [pow_two,div_self (mul_ne_zero hm.ne' hm.ne')]
  simpa [twoBandTraceFormula,twoBandInversionFactor,he] using h

/-- The normalized frequency integral of the two-mark difference at the same
carrier momentum. Only the opposite-band pair remains. This includes equal
energies, zero transfer, and vanishing or equal hopping amplitudes. -/
theorem twoBand_relative_bubble_frequency_integral {m : ℝ} (hm : 0 < m) (v w ν : ℝ) :
    let a := Real.sqrt (m^2+v^2)
    let b := Real.sqrt (m^2+w^2)
    Integrable (fun x : ℝ => twoBandRelativeBubble m v w x (x+ν)) ∧
    (∫ x : ℝ, twoBandRelativeBubble m v w x (x+ν))/(2*Real.pi) =
      -(1-(m^2+v*w)/(a*b))*(a+b)/((a+b)^2+ν^2) := by
  dsimp only
  let a := Real.sqrt (m^2+v^2)
  let b := Real.sqrt (m^2+w^2)
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have hb : 0 < b := Real.sqrt_pos.mpr (by positivity)
  have ea : a^2 = m^2+v^2 := Real.sq_sqrt (by positivity)
  have eb : b^2 = m^2+w^2 := Real.sq_sqrt (by positivity)
  have h := band_trace_spectral ha hb (m^2+v*w) ν
  have he (x : ℝ) : twoBandTraceFormula m v w x (x+ν) =
      2*(m^2+v*w-x*(x+ν))/((x^2+a^2)*((x+ν)^2+b^2)) := by
    simp only [twoBandTraceFormula,twoBandInversionFactor,ea,eb,add_assoc]
  simp_rw [← he] at h
  have h₀ := twoBand_onsite_trace_frequency hm ν
  refine ⟨h.1.sub h₀.1, ?_⟩
  simp only [twoBandRelativeBubble]
  rw [integral_sub h.1 h₀.1,h₀.2,sub_zero,h.2]
  rw [mul_div_cancel_left₀ _ (by positivity)]

/-- The zero frequency integral of the onsite word does not give absolute
convergence of the original four-dimensional integrand. -/
theorem twoBand_onsite_trace_not_integrable {m : ℝ} (hm : 0 < m) (ν : ℝ) :
    ¬ Integrable (fun p : ℝ × Spatial => twoBandTraceFormula m 0 0 p.1 (p.1+ν)) := by
  let F := fun x : ℝ => twoBandTraceFormula m 0 0 x (x+ν)
  have hc : Continuous F := by
    unfold F twoBandTraceFormula twoBandInversionFactor
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro x
    positivity
  have hpos : 0 < F 0 := by
    simp [F,twoBandTraceFormula,twoBandInversionFactor]
    positivity
  intro h
  have h' : Integrable (fun p : ℝ × Spatial => F p.1)
      ((volume : Measure ℝ).prod (volume : Measure Spatial)) := h
  have hzero : F =ᵐ[volume] fun _ => 0 := by
    filter_upwards [h'.prod_right_ae] with x hx
    by_contra hne
    have hfinite := (integrable_const_iff_isFiniteMeasure hne).mp hx
    have htop : (volume : Measure Spatial) Set.univ = ⊤ := by simp
    exact (lt_irrefl ⊤) (htop ▸ hfinite.measure_univ_lt_top)
  exact hpos.ne' (congrFun (Measure.eq_of_ae_eq hzero hc continuous_const) 0)

end UV.SectorPlane
