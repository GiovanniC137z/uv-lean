import UV.PoissonTail
import UV.ScalarRotation
import UV.SixthDifference
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.MeanInequalities

/-! Moment threshold and differentiability for the actual coordinate-square
Fourier integral associated with a positive Poisson convolution. -/

noncomputable section
open MeasureTheory Real Filter
open scoped Topology FourierTransform InnerProductSpace ENNReal

namespace UV

theorem stableCoordinateConvolution_continuous {a : ℝ} (ha : 0 < a)
    (μ : Measure ScalarMomentum) [IsFiniteMeasure μ] :
    Continuous (stableCoordinateConvolution a μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_integral_filter_of_dominated_convergence (μ := μ)
    (fun _ => stablePoissonKernel a 0)
  · exact Eventually.of_forall fun z =>
      ((stablePoissonKernel_continuous ha).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact Eventually.of_forall fun z => Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (stablePoissonKernel_pos ha _)]
      exact stablePoissonKernel_le_zero ha _
  · exact integrable_const _
  · exact Eventually.of_forall fun y =>
      ((stablePoissonKernel_continuous ha).comp
        (continuous_id.sub continuous_const)).tendsto x

theorem stableCoordinateConvolution_le_poisson {a : ℝ} (ha : 0 < a)
    (μ : Measure ScalarMomentum) [IsFiniteMeasure μ]
    (hMoment : Integrable (fun y : ScalarMomentum => (1 + ‖y‖ / a)^5) μ)
    (x : ScalarMomentum) :
    stableCoordinateConvolution a μ x ≤ stablePoissonKernel a x *
      (∫ y, (1 + ‖y‖/a)^5 ∂μ) := by
  calc
    _ ≤ ∫ y, stablePoissonKernel a x * (1 + ‖y‖/a)^5 ∂μ := by
      apply integral_mono (stableCoordinateConvolution_integrable ha μ x)
        (hMoment.const_mul _)
      intro y
      have hb := (div_le_iff₀ (stablePoissonKernel_pos ha x)).mp
        (stablePoissonKernel_ratio_bound ha x y)
      simpa only [mul_comm] using hb
    _ = _ := integral_const_mul _ _

theorem stablePoissonKernel_polynomial_bound {a : ℝ} (ha : 0 < a)
    (x : ScalarMomentum) :
    stablePoissonKernel a x ≤
      ((3*a/(4*Real.pi^2)) * (2 / min a 1)^5) / (1 + ‖x‖)^5 := by
  have hd : 0 < min a 1 := lt_min ha zero_lt_one
  have hr := stablePoissonRadius_pos ha x
  have hδa := min_le_left a 1
  have hδ1 := min_le_right a 1
  have hrn := stablePoissonRadius_ge_norm a x
  have hra := stablePoissonRadius_ge a x
  have hn := norm_nonneg x
  have hh := mul_nonneg (sub_nonneg.mpr hδ1) hn
  have hlow : (min a 1 / 2) * (1 + ‖x‖) ≤ stablePoissonRadius a x := by nlinarith
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (min a 1/2)*(1+‖x‖)) hlow 5
  unfold stablePoissonKernel
  calc
    _ ≤ (3*a/(4*Real.pi^2)) / ((min a 1/2)*(1+‖x‖))^5 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
    _ = _ := by field_simp

theorem stableCoordinateConvolution_polynomial_bound {a : ℝ} (ha : 0 < a)
    (μ : Measure ScalarMomentum) [IsFiniteMeasure μ]
    (hMoment : Integrable (fun y : ScalarMomentum => (1 + ‖y‖ / a)^5) μ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |stableCoordinateConvolution a μ x| ≤ K / (1+‖x‖)^5 := by
  let I : ℝ := ∫ y, (1+‖y‖/a)^5 ∂μ
  have hI : 0 ≤ I := integral_nonneg fun _ => by positivity
  refine ⟨((3*a/(4*Real.pi^2)) * (2/min a 1)^5)*I, by positivity, fun x => ?_⟩
  rw [abs_of_nonneg (stableCoordinateConvolution_nonneg ha μ x)]
  calc
    _ ≤ stablePoissonKernel a x * I := stableCoordinateConvolution_le_poisson ha μ hMoment x
    _ ≤ (((3*a/(4*Real.pi^2)) * (2/min a 1)^5)/(1+‖x‖)^5)*I :=
      mul_le_mul_of_nonneg_right (stablePoissonKernel_polynomial_bound ha x) hI
    _ = _ := by ring

theorem polynomial_square_moment_integrable {C : ScalarMomentum → ℝ}
    (hC : AEStronglyMeasurable C) {K : ℝ} (hK : 0 ≤ K)
    (hdecay : ∀ x, |C x| ≤ K/(1+‖x‖)^5) (n : ℕ) (hn : n ≤ 5) :
    Integrable (fun x : ScalarMomentum => ‖x‖^n * (C x)^2) := by
  have hi : Integrable (fun x : ScalarMomentum => (1+‖x‖)^(-(5:ℝ))) :=
    integrable_one_add_norm (by norm_num [finrank_euclideanSpace])
  apply (hi.const_mul (K^2)).mono'
  · exact (continuous_norm.pow n).aestronglyMeasurable.mul (hC.pow 2)
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖x‖^n * (C x)^2)]
    have hp : 0 < 1+‖x‖ := by positivity
    have hcn : ‖x‖^n ≤ (1+‖x‖)^5 := by
      calc
        _ ≤ (1+‖x‖)^n := pow_le_pow_left₀ (norm_nonneg x) (by linarith) n
        _ ≤ _ := pow_le_pow_right₀ (by linarith [norm_nonneg x]) hn
    have hc2 : (C x)^2 ≤ (K/(1+‖x‖)^5)^2 := by
      have := (sq_le_sq₀ (abs_nonneg (C x)) (div_nonneg hK (pow_nonneg hp.le 5))).mpr (hdecay x)
      simpa only [sq_abs] using this
    have he : (1+‖x‖)^(-(5:ℝ)) = 1/(1+‖x‖)^5 := by
      rw [← Real.rpow_natCast (1+‖x‖) 5, one_div]
      exact Real.rpow_neg hp.le (5:ℝ)
    rw [he]
    have hh := mul_le_mul hcn hc2 (sq_nonneg (C x)) (pow_nonneg hp.le 5)
    calc
      _ ≤ (1+‖x‖)^5 * (K/(1+‖x‖)^5)^2 := hh
      _ = _ := by field_simp

theorem stableCoordinateConvolution_square_moment_integrable {a : ℝ} (ha : 0 < a)
    (μ : Measure ScalarMomentum) [IsFiniteMeasure μ]
    (hMoment : Integrable (fun y : ScalarMomentum => (1 + ‖y‖ / a)^5) μ)
    (n : ℕ) (hn : n ≤ 5) :
    Integrable (fun x : ScalarMomentum => ‖x‖^n * (stableCoordinateConvolution a μ x)^2) := by
  obtain ⟨K,hK,hb⟩ := stableCoordinateConvolution_polynomial_bound ha μ hMoment
  exact polynomial_square_moment_integrable
    (stableCoordinateConvolution_continuous ha μ).aestronglyMeasurable hK hb n hn

end UV
