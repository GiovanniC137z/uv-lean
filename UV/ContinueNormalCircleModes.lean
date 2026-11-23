import UV.ContinueNormalWindingIntegral
import UV.ContinueNormalFrequency

/-! Periodic charged spinors on a circle of circumference L. In the
coordinate t=z/L, the periodic gauge multiplies the cover translates by
exp(−iθ(t+j)). Its integer Fourier modes have frequency (2πn+θ)/L. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Matrix.Norms.L2Operator

namespace UV

def normalAngularPhase (a t : ℝ) : ℂ := Complex.exp (-Complex.I*(a:ℂ)*(t:ℂ))

theorem normal_angular_phase_norm (a t : ℝ) : ‖normalAngularPhase a t‖ = 1 := by
  simp [normalAngularPhase,Complex.norm_exp,Complex.mul_re]

def normalCircleTerm (m L θ : ℝ) (p : OSFourSpace) (t : ℝ) (j : ℤ) : DiracMatrix :=
  normalAngularPhase θ (t+(j:ℝ)) • normalDiracCover normalCoverGamma5 m p (L*(t+(j:ℝ)))

def normalCircleKernel (m L θ : ℝ) (p : OSFourSpace) (t : ℝ) : DiracMatrix :=
  ∑' j : ℤ, normalCircleTerm m L θ p t j

theorem normal_circle_term_bound {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ : ℝ) (p : OSFourSpace) (t : ℝ) (j : ℤ) :
    ‖normalCircleTerm m L θ p t j‖ ≤ (2*Real.exp (m*L*|t|))*normalWindingRate (4*m) L j := by
  rw [normalCircleTerm,norm_smul,normal_angular_phase_norm,one_mul]
  apply (normal_dirac_cover_bound _ normal_cover_gamma_norm hm p _).trans
  rw [normalWindingRate,mul_assoc,←Real.exp_add]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  have he := (normal_cover_energy_bounds hm p).1
  have ht : |(j:ℝ)| ≤ |t|+|t+(j:ℝ)| := by
    simpa only [neg_add_cancel_left,abs_neg] using abs_add_le (-t) (t+(j:ℝ))
  have hmul := mul_le_mul_of_nonneg_left ht (mul_nonneg hm.le hL.le)
  rw [abs_mul,abs_mul,abs_of_pos hL]
  nlinarith [mul_le_mul_of_nonneg_right he (mul_nonneg hL.le (abs_nonneg (t+(j:ℝ))))]

theorem normal_circle_term_summable {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ : ℝ) (p : OSFourSpace) (t : ℝ) :
    Summable (fun j => ‖normalCircleTerm m L θ p t j‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (normal_circle_term_bound hm hL θ p t)
    ((normal_winding_rate_summable (m := 4*m) (by positivity) hL).mul_left _)

theorem normal_circle_kernel_periodic (m L θ : ℝ) (p : OSFourSpace) : Function.Periodic (normalCircleKernel m L θ p) 1 := by
  intro t
  unfold normalCircleKernel
  rw [← (Equiv.addLeft (1:ℤ)).tsum_eq (f := normalCircleTerm m L θ p t)]
  apply tsum_congr fun j => ?_
  change normalCircleTerm m L θ p (t+1) j = normalCircleTerm m L θ p t (1+j)
  simp only [normalCircleTerm,Int.cast_add,Int.cast_one,add_assoc]

local instance normalCircleMatrixMeasurable : MeasurableSpace DiracMatrix := borel _
local instance normalCircleMatrixBorel : BorelSpace DiracMatrix := ⟨rfl⟩

theorem normal_circle_kernel_measurable {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ : ℝ) (p : OSFourSpace) :
    Measurable (normalCircleKernel m L θ p) := by
  have h (j : ℤ) : Measurable (fun t => normalCircleTerm m L θ p t j) :=
    (show Continuous (fun t : ℝ => normalAngularPhase θ (t+(j:ℝ))) by unfold normalAngularPhase; fun_prop).measurable.smul
      (normal_cover_args_measurable normalCoverGamma5 m measurable_const (by fun_prop))
  exact measurable_of_tendsto_metrizable' atTop (fun I : Finset ℤ => Finset.measurable_sum I (fun j _ => h j))
    (tendsto_pi_nhds.mpr fun t => (normal_circle_term_summable hm hL θ p t).of_norm.hasSum)

theorem normal_circle_kernel_integrable {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ : ℝ) (p : OSFourSpace) :
    IntegrableOn (normalCircleKernel m L θ p) (Ioc 0 1) := by
  let K := 2*Real.exp (m*L)
  let g := normalWindingRate (4*m) L
  have hs := (normal_winding_rate_summable (m := 4*m) (by positivity) hL).mul_left K
  apply (integrableOn_const (C := ∑' j : ℤ, K*g j) (hs := measure_Ioc_lt_top.ne)).mono'
    (normal_circle_kernel_measurable hm hL θ p).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  apply (norm_tsum_le_tsum_norm (normal_circle_term_summable hm hL θ p t)).trans
  apply (normal_circle_term_summable hm hL θ p t).tsum_le_tsum _ hs
  intro j
  apply (normal_circle_term_bound hm hL θ p t j).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  rw [abs_of_pos ht.1]
  nlinarith [mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hm.le hL.le)]

theorem normal_cell_integral_tsum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Integrable f) :
    (∫ t in Ioc (0:ℝ) 1, ∑' j : ℤ, f (t+(j:ℝ))) = ∫ x, f x := by
  have hnorm := hf.norm.hasSum_intervalIntegral_comp_add_int
  have h := hf.hasSum_intervalIntegral_comp_add_int
  simp only [intervalIntegral.integral_of_le zero_le_one] at hnorm h
  have hi (j : ℤ) : IntegrableOn (fun t : ℝ => f (t+(j:ℝ))) (Ioc 0 1) :=
    ((measurePreserving_add_right volume (j:ℝ)).integrable_comp_of_integrable hf).integrableOn
  exact (hasSum_integral_of_summable_integral_norm hi hnorm.summable).unique h

theorem normal_circle_mode_phase {L : ℝ} (hL : 0 < L) (θ t : ℝ) (n j : ℤ) :
    normalAngularPhase (2*Real.pi*(n:ℝ)) t * normalAngularPhase θ (t+(j:ℝ)) =
      normalAngularPhase ((2*Real.pi*(n:ℝ)+θ)/L) (L*(t+(j:ℝ))) := by
  unfold normalAngularPhase
  rw [←Complex.exp_add]
  have he : -Complex.I*((2*Real.pi*(n:ℝ)+θ)/L:ℝ)*(L*(t+(j:ℝ)):ℝ) =
      (-Complex.I*(2*Real.pi*(n:ℝ):ℝ)*(t:ℂ)+(-Complex.I*(θ:ℂ)*(t+(j:ℝ):ℝ)))+
        ((-(n*j):ℤ):ℂ)*(2*(Real.pi:ℂ)*Complex.I) := by
    push_cast
    field_simp [hL.ne']; ring
  rw [he,Complex.exp_add (x := -Complex.I*(2*Real.pi*(n:ℝ):ℝ)*(t:ℂ)+(-Complex.I*(θ:ℂ)*(t+(j:ℝ):ℝ))),Complex.exp_int_mul_two_pi_mul_I,mul_one]

/-- The Fourier coefficient with physical integration dz=L dt is the
actual Dirac multiplier at the shifted integer mode. -/
theorem normal_circle_fourier_mode {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ : ℝ) (p : OSFourSpace) (n : ℤ) :
    L • (∫ t in Ioc (0:ℝ) 1, normalAngularPhase (2*Real.pi*(n:ℝ)) t • normalCircleKernel m L θ p t) =
      normalDiracFrequency m p ((2*Real.pi*(n:ℝ)+θ)/L) := by
  let ξ := (2*Real.pi*(n:ℝ)+θ)/L
  let F := fun d => normalAngularPhase ξ d • normalDiracCover normalCoverGamma5 m p d
  have hF : Integrable F := (normal_cover_angular_fourier normalCoverGamma5 hm p ξ).1
  have he (t : ℝ) : normalAngularPhase (2*Real.pi*(n:ℝ)) t • normalCircleKernel m L θ p t =
      ∑' j : ℤ, F (L*(t+(j:ℝ))) := by
    rw [normalCircleKernel,←(normal_circle_term_summable hm hL θ p t).of_norm.tsum_const_smul]
    apply tsum_congr fun j => ?_
    rw [normalCircleTerm,smul_smul,normal_circle_mode_phase hL]
  simp_rw [he]
  rw [normal_cell_integral_tsum (hF.comp_mul_left' hL.ne'),Measure.integral_comp_mul_left,abs_of_pos (inv_pos.mpr hL),
    smul_smul,mul_inv_cancel₀ hL.ne',one_smul]
  exact normal_frequency_is_cover_transform hm p ξ

end UV
