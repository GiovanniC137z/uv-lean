import UV.CentralDifference
import UV.PoissonTail

/-! The sign-definite sixth difference of an actual cosine transform, and
Fatou's obstruction when its positive measure has an infinite sixth moment. -/

noncomputable section
open MeasureTheory Real Filter
open scoped Topology ENNReal

namespace UV

def stableCosineTransform (ν : Measure ℝ) (h : ℝ) : ℝ :=
  ∫ t, Real.cos (h*t) ∂ν

def sixthSinKernel (h t : ℝ) : ℝ := 64 * (Real.sin (h*t/2) / h)^6

theorem stableCosineTransform_integrable (ν : Measure ℝ) [IsFiniteMeasure ν] (h : ℝ) :
    Integrable (fun t => Real.cos (h*t)) ν := by
  apply (integrable_const (1:ℝ)).mono'
  · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · exact Eventually.of_forall fun t => by
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (h*t)

theorem sixth_cosine_identity (t : ℝ) :
    Real.cos (3*t) - 6*Real.cos (2*t) + 15*Real.cos t - 20 +
      15*Real.cos (-t) - 6*Real.cos (-2*t) + Real.cos (-3*t) =
        -64 * Real.sin (t/2)^6 := by
  have hs : 1 - Real.cos t = 2 * Real.sin (t/2)^2 := by
    have h := Real.sin_sq_eq_half_sub (t/2)
    rw [show 2*(t/2)=t by ring] at h
    linarith
  simp only [show -2*t = -(2*t) by ring, show -3*t = -(3*t) by ring,
    Real.cos_neg, Real.cos_three_mul, Real.cos_two_mul]
  calc
    _ = -8 * (1 - Real.cos t)^3 := by ring
    _ = _ := by rw [hs]; ring

theorem sixthSinKernel_nonneg (h t : ℝ) : 0 ≤ sixthSinKernel h t := by
  unfold sixthSinKernel
  positivity

theorem sixthSinKernel_integrable (ν : Measure ℝ) [IsFiniteMeasure ν] (h : ℝ) :
    Integrable (sixthSinKernel h) ν := by
  apply (integrable_const (64 * (1/|h|)^6 : ℝ)).mono'
  · exact (continuous_const.mul (((Real.continuous_sin.comp
      ((continuous_const.mul continuous_id).div_const 2)).div_const h).pow 6)).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (sixthSinKernel_nonneg h t)]
    unfold sixthSinKernel
    have he : (Real.sin (h*t/2) / h)^6 = |Real.sin (h*t/2) / h|^6 := by
      rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ (Real.sin (h*t/2)/h)^6)]
    rw [he, abs_div]
    gcongr
    exact Real.abs_sin_le_one _

theorem stableCosineTransform_sixth_difference (ν : Measure ℝ) [IsFiniteMeasure ν]
    (h : ℝ) :
    -(sixthSymmetricDifference (stableCosineTransform ν) h) / h^6 =
      ∫ t, sixthSinKernel h t ∂ν := by
  have hi (b : ℝ) := stableCosineTransform_integrable ν b
  have h₁ := (hi (3*h)).sub ((hi (2*h)).const_mul 6)
  have h₂ := h₁.add ((hi h).const_mul 15)
  have h₃ := h₂.sub ((hi 0).const_mul 20)
  have h₄ := h₃.add ((hi (-h)).const_mul 15)
  have h₅ := h₄.sub ((hi (-2*h)).const_mul 6)
  change Integrable (fun t => Real.cos ((3*h)*t) - 6*Real.cos ((2*h)*t)) ν at h₁
  change Integrable (fun t => Real.cos ((3*h)*t) - 6*Real.cos ((2*h)*t) +
    15*Real.cos (h*t)) ν at h₂
  change Integrable (fun t => Real.cos ((3*h)*t) - 6*Real.cos ((2*h)*t) +
    15*Real.cos (h*t) - 20*Real.cos (0*t)) ν at h₃
  change Integrable (fun t => Real.cos ((3*h)*t) - 6*Real.cos ((2*h)*t) +
    15*Real.cos (h*t) - 20*Real.cos (0*t) + 15*Real.cos ((-h)*t)) ν at h₄
  change Integrable (fun t => Real.cos ((3*h)*t) - 6*Real.cos ((2*h)*t) +
    15*Real.cos (h*t) - 20*Real.cos (0*t) + 15*Real.cos ((-h)*t) -
    6*Real.cos ((-2*h)*t)) ν at h₅
  have he : sixthSymmetricDifference (stableCosineTransform ν) h =
      ∫ t, -64 * Real.sin (h*t/2)^6 ∂ν := by
    calc
      _ = ∫ t, Real.cos ((3*h)*t) - 6*Real.cos ((2*h)*t) +
          15*Real.cos (h*t) - 20*Real.cos (0*t) +
          15*Real.cos ((-h)*t) - 6*Real.cos ((-2*h)*t) +
          Real.cos ((-3*h)*t) ∂ν := by
        rw [integral_add h₅ (hi (-3*h)), integral_sub h₄ ((hi (-2*h)).const_mul 6),
          integral_add h₃ ((hi (-h)).const_mul 15), integral_sub h₂ ((hi 0).const_mul 20),
          integral_add h₁ ((hi h).const_mul 15), integral_sub (hi (3*h)) ((hi (2*h)).const_mul 6)]
        simp only [integral_const_mul, sixthSymmetricDifference, stableCosineTransform]
      _ = _ := integral_congr_ae (Eventually.of_forall fun t => by
        simpa only [mul_assoc, zero_mul, Real.cos_zero, mul_one, neg_mul] using
          sixth_cosine_identity (h*t))
  rw [he, ← integral_neg, ← integral_div]
  apply integral_congr_ae
  filter_upwards with t
  simp only [sixthSinKernel, div_pow]
  ring

theorem sixthSinKernel_tendsto (t : ℝ) :
    Tendsto (fun h : ℝ => sixthSinKernel h t) (𝓝[≠] 0) (𝓝 (t^6)) := by
  have hd : HasDerivAt (fun h : ℝ => Real.sin (h*t/2)) (t/2) 0 := by
    simpa only [id_eq, zero_mul, zero_div, Real.cos_zero, one_mul] using
      (((hasDerivAt_id (0:ℝ)).mul_const t).div_const 2).sin
  have ht := hd.tendsto_slope_zero
  simp only [zero_add, zero_mul, zero_div, Real.sin_zero, sub_zero, smul_eq_mul,
    ← div_eq_inv_mul] at ht
  have hr := (ht.pow 6).const_mul 64
  rw [show (64:ℝ) * (t/2)^6 = t^6 by ring] at hr
  exact hr

 theorem sixthSinKernel_liminf (ν : Measure ℝ) (h : ℕ → ℝ)
    (hh : Tendsto h atTop (𝓝[≠] 0)) :
    (∫⁻ t, ENNReal.ofReal (t^6) ∂ν) ≤
      Filter.liminf (fun n => ∫⁻ t, ENNReal.ofReal (sixthSinKernel (h n) t) ∂ν) atTop := by
  have hf := lintegral_liminf_le (μ := ν) (f := fun n t =>
    ENNReal.ofReal (sixthSinKernel (h n) t)) (fun n => by
      unfold sixthSinKernel
      fun_prop)
  convert hf using 1
  apply lintegral_congr
  intro t
  exact ((ENNReal.continuous_ofReal.tendsto _).comp ((sixthSinKernel_tendsto t).comp hh)).liminf_eq.symm

 theorem stableCosineTransform_no_finite_sixth_difference_limit
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hMoment : (∫⁻ t, ENNReal.ofReal (t^6) ∂ν) = ∞)
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝[≠] 0)) (L : ℝ) :
    ¬ Tendsto (fun n => -(sixthSymmetricDifference (stableCosineTransform ν) (h n)) /
      (h n)^6) atTop (𝓝 L) := by
  intro hlim
  simp only [stableCosineTransform_sixth_difference] at hlim
  have he : Tendsto (fun n => ∫⁻ t, ENNReal.ofReal (sixthSinKernel (h n) t) ∂ν)
      atTop (𝓝 (ENNReal.ofReal L)) := by
    convert (ENNReal.continuous_ofReal.tendsto L).comp hlim using 1
    funext n
    exact (ofReal_integral_eq_lintegral_ofReal (sixthSinKernel_integrable ν (h n))
      (Eventually.of_forall (sixthSinKernel_nonneg (h n)))).symm
  have hf := sixthSinKernel_liminf ν h hh
  rw [hMoment, he.liminf_eq] at hf
  exact ENNReal.ofReal_ne_top (top_le_iff.mp hf)

 theorem stableCosineTransform_not_contDiffAt
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hMoment : (∫⁻ t, ENNReal.ofReal (t^6) ∂ν) = ∞) :
    ¬ ContDiffAt ℝ 6 (stableCosineTransform ν) 0 := by
  intro hf
  have hh : Tendsto (fun n : ℕ => 1 / ((n:ℝ)+1)) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
    · exact Eventually.of_forall fun n => by simp [ne_of_gt (by positivity : 0 < (n:ℝ)+1)]
  have hlim := (sixthSymmetricDifference_tendsto hf).neg.comp hh
  apply stableCosineTransform_no_finite_sixth_difference_limit ν hMoment _ hh
    (-(iteratedDeriv 6 (stableCosineTransform ν) 0))
  simpa only [neg_div] using hlim

end UV
