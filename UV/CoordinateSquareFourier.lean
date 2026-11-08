import UV.HeatFourier
import UV.StableMoments
import UV.StableMomentThreshold

/-! The literal physical-frequency transform of a coordinate square:
its five derivatives, positive projected measure, and sixth-order obstruction. -/

noncomputable section
open MeasureTheory Real Filter
open scoped Topology FourierTransform InnerProductSpace ENNReal

namespace UV

def coordinateSquareFourier (C : ScalarMomentum → ℝ) (P : ScalarMomentum) : ℂ :=
  ∫ x, stableFourierPhase P x * (((C x)^2 : ℝ) : ℂ)

def coordinateSquareMeasure (C : ScalarMomentum → ℝ) : Measure ScalarMomentum :=
  volume.withDensity (fun x => ENNReal.ofReal ((C x)^2))

def coordinateProjectionMeasure (C : ScalarMomentum → ℝ) : Measure ℝ :=
  Measure.map (fun x : ScalarMomentum => x 0) (coordinateSquareMeasure C)

theorem coordinateSquareFourier_eq_standard (C : ScalarMomentum → ℝ) (P : ScalarMomentum) :
    coordinateSquareFourier C P =
      𝓕 (fun x : ScalarMomentum => (((C x)^2 : ℝ) : ℂ))
        ((-(2*Real.pi)⁻¹) • P) := by
  rw [Real.fourierIntegral_eq']
  apply integral_congr_ae
  filter_upwards with x
  simp only [stableFourierPhase, smul_eq_mul,
    inner_smul_right, real_inner_comm x P]
  congr 2
  push_cast
  field_simp

theorem coordinateSquareFourier_contDiff_five {C : ScalarMomentum → ℝ}
    (hC : AEStronglyMeasurable C) {K : ℝ} (hK : 0 ≤ K)
    (hdecay : ∀ x, |C x| ≤ K/(1+‖x‖)^5) :
    ContDiff ℝ 5 (coordinateSquareFourier C) := by
  have hF : ContDiff ℝ 5 (𝓕 (fun x : ScalarMomentum => (((C x)^2 : ℝ) : ℂ))) := by
    apply Real.contDiff_fourierIntegral
    intro n hn
    have hn5 : n ≤ 5 := by exact_mod_cast hn
    have hi := polynomial_square_moment_integrable hC hK hdecay n hn5
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_pow, sq_abs] using hi
  have he : coordinateSquareFourier C =
      (𝓕 (fun x : ScalarMomentum => (((C x)^2 : ℝ) : ℂ))) ∘
        (fun P : ScalarMomentum => (-(2*Real.pi)⁻¹) • P) :=
    funext (coordinateSquareFourier_eq_standard C)
  rw [he]
  exact hF.comp (contDiff_const.smul contDiff_id)

 theorem coordinateSquareFourier_integrable {C : ScalarMomentum → ℝ}
    (hC : Measurable C) (hInt : Integrable (fun x => (C x)^2)) (P : ScalarMomentum) :
    Integrable (fun x => stableFourierPhase P x * (((C x)^2:ℝ):ℂ)) := by
  apply hInt.mono'
  · apply Measurable.aestronglyMeasurable
    unfold stableFourierPhase
    fun_prop (disch := assumption)
  · exact Eventually.of_forall fun x => by
      simp only [norm_mul, stableFourierPhase_norm, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_pow, sq_abs, le_refl]

 theorem coordinateSquareMeasure_finite {C : ScalarMomentum → ℝ}
    (hInt : Integrable (fun x => (C x)^2)) : IsFiniteMeasure (coordinateSquareMeasure C) := by
  apply isFiniteMeasure_withDensity
  exact (lintegral_ofReal_ne_top_iff_integrable hInt.aestronglyMeasurable
    (Eventually.of_forall fun _ => sq_nonneg _)).mpr hInt

 theorem coordinateProjectionMeasure_finite {C : ScalarMomentum → ℝ}
    (hInt : Integrable (fun x => (C x)^2)) : IsFiniteMeasure (coordinateProjectionMeasure C) := by
  letI := coordinateSquareMeasure_finite hInt
  unfold coordinateProjectionMeasure
  infer_instance

 theorem coordinateSquareMeasure_integral {C : ScalarMomentum → ℝ} (hC : Measurable C)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ScalarMomentum → E) :
    (∫ x, f x ∂coordinateSquareMeasure C) = ∫ x, (C x)^2 • f x := by
  unfold coordinateSquareMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)]

 theorem coordinateProjectionMeasure_cosine {C : ScalarMomentum → ℝ}
    (hC : Measurable C) (h : ℝ) :
    stableCosineTransform (coordinateProjectionMeasure C) h =
      ∫ x, Real.cos (h*x 0) * (C x)^2 := by
  unfold stableCosineTransform coordinateProjectionMeasure
  rw [integral_map (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0).measurable.aemeasurable
    (by fun_prop), coordinateSquareMeasure_integral hC]
  simp only [smul_eq_mul, mul_comm]

 theorem coordinateSquareFourier_axis_re {C : ScalarMomentum → ℝ}
    (hC : Measurable C) (hInt : Integrable (fun x => (C x)^2)) (h : ℝ) :
    (coordinateSquareFourier C (scalarAxis h)).re =
      stableCosineTransform (coordinateProjectionMeasure C) h := by
  rw [coordinateProjectionMeasure_cosine hC]
  unfold coordinateSquareFourier
  have he : (∫ x, stableFourierPhase (scalarAxis h) x * (((C x)^2:ℝ):ℂ)).re =
      ∫ x, (stableFourierPhase (scalarAxis h) x * (((C x)^2:ℝ):ℂ)).re := by
    simpa only [RCLike.re_to_complex] using
      (integral_re (coordinateSquareFourier_integrable hC hInt (scalarAxis h))).symm
  rw [he]
  apply integral_congr_ae
  filter_upwards with x
  simp [stableFourierPhase, Complex.exp_re, scalarAxis, EuclideanSpace.inner_single_left, pow_two]

 theorem coordinateProjectionMeasure_sixth_moment {C : ScalarMomentum → ℝ}
    (hC : Measurable C) :
    (∫⁻ t, ENNReal.ofReal (t^6) ∂coordinateProjectionMeasure C) =
      ∫⁻ x : ScalarMomentum, ENNReal.ofReal ((x 0)^6 * (C x)^2) := by
  unfold coordinateProjectionMeasure
  rw [lintegral_map (by fun_prop)
    (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0).measurable,
    coordinateSquareMeasure, lintegral_withDensity_eq_lintegral_mul volume (by fun_prop) (by fun_prop)]
  apply lintegral_congr
  intro x
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (sq_nonneg _), mul_comm]

 theorem coordinateSquareFourier_axis_not_contDiffAt {C : ScalarMomentum → ℝ}
    (hC : Measurable C) (hInt : Integrable (fun x => (C x)^2))
    (hMoment : (∫⁻ x : ScalarMomentum, ENNReal.ofReal ((x 0)^6 * (C x)^2)) = ∞) :
    ¬ ContDiffAt ℝ 6 (fun h => (coordinateSquareFourier C (scalarAxis h)).re) 0 := by
  letI := coordinateProjectionMeasure_finite hInt
  have he : (fun h => (coordinateSquareFourier C (scalarAxis h)).re) =
      stableCosineTransform (coordinateProjectionMeasure C) :=
    funext (coordinateSquareFourier_axis_re hC hInt)
  rw [he]
  apply stableCosineTransform_not_contDiffAt
  rw [coordinateProjectionMeasure_sixth_moment hC]
  exact hMoment

 theorem coordinateSquareFourier_not_contDiffAt {C : ScalarMomentum → ℝ}
    (hC : Measurable C) (hInt : Integrable (fun x => (C x)^2))
    (hMoment : (∫⁻ x : ScalarMomentum, ENNReal.ofReal ((x 0)^6 * (C x)^2)) = ∞) :
    ¬ ContDiffAt ℝ 6 (coordinateSquareFourier C) 0 := by
  intro hf
  apply coordinateSquareFourier_axis_not_contDiffAt hC hInt hMoment
  have ha : ContDiffAt ℝ 6 scalarAxis 0 := by
    have he : scalarAxis = (fun h : ℝ => h • scalarAxis 1) := by
      funext h
      ext i
      simp [scalarAxis, EuclideanSpace.single_apply]
    rw [he]
    exact contDiffAt_id.smul contDiffAt_const
  have hf' : ContDiffAt ℝ 6 (coordinateSquareFourier C) (scalarAxis 0) := by
    have hzero : scalarAxis 0 = 0 := by
      ext i
      simp [scalarAxis, EuclideanSpace.single_apply]
    rw [hzero]
    exact hf
  exact Complex.reCLM.contDiff.contDiffAt.comp 0 (hf'.comp 0 ha)

 theorem coordinateSquareFourier_no_holomorphic_square {C : ScalarMomentum → ℝ}
    (hC : Measurable C) (hInt : Integrable (fun x => (C x)^2))
    (hMoment : (∫⁻ x : ScalarMomentum, ENNReal.ofReal ((x 0)^6 * (C x)^2)) = ∞) :
    ¬ ∃ b : ℂ → ℂ, AnalyticAt ℂ b 0 ∧
      (∀ᶠ h : ℝ in 𝓝 0, (b ((h:ℂ)^2)).re =
        (coordinateSquareFourier C (scalarAxis h)).re) := by
  rintro ⟨b,hb,heq⟩
  apply coordinateSquareFourier_axis_not_contDiffAt hC hInt hMoment
  have hbR : ContDiffAt ℝ 6 b 0 :=
    (hb.contDiffAt : ContDiffAt ℂ 6 b 0).restrict_scalars ℝ
  have hs : ContDiffAt ℝ 6 (fun h : ℝ => (h:ℂ)^2) 0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.pow 2
  have hb' : ContDiffAt ℝ 6 b ((0:ℂ)^2) := by simpa using hbR
  have hcomp := Complex.reCLM.contDiff.contDiffAt.comp 0 (hb'.comp 0 hs)
  have heq' : (fun h => (coordinateSquareFourier C (scalarAxis h)).re) =ᶠ[𝓝 0]
      (fun h : ℝ => (b ((h:ℂ)^2)).re) := heq.mono fun _ hh => hh.symm
  exact hcomp.congr_of_eventuallyEq heq'

end UV
