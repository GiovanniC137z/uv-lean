import UV.MomentRecurrence
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Exact scalar Gaussian moments for the shared-depth cumulant. We use the
normalized real density `exp (-x²) / √π` and scale it to the given variance. -/

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace UV

theorem centered_gaussian_half_recurrence (n : ℕ) :
    gaussianEvenMoment 0 (n + 1) = ((2 * (n : ℝ) + 1) / 2) * gaussianEvenMoment 0 n := by
  have h0 := gaussianEvenMoment_integrable 0 n
  have h1 := gaussianEvenMoment_integrable 0 (n + 1)
  have hi := (h0.const_mul (2 * (n : ℝ) + 1)).sub (h1.const_mul 2)
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt
      (fun y : ℝ => y ^ (2 * n + 1) * subordinationGaussian 0 y)
      ((2 * (n : ℝ) + 1) * (x ^ (2 * n) * subordinationGaussian 0 x) -
        2 * (x ^ (2 * (n + 1)) * subordinationGaussian 0 x)) x := by
    intro x hx
    convert gaussianOddProduct_hasDerivAt 0 (2 * n) hx using 1
    push_cast
    simp only [zero_pow (by decide : 2 ≠ 0), Nat.mul_succ]
    rw [pow_add, pow_add]
    ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (gaussianOddProduct_continuous_zero 0 (2 * n)) hd hi (gaussianOddProduct_tendsto_zero 0 (2 * n))
  rw [integral_sub (h0.const_mul _) (h1.const_mul _), integral_const_mul, integral_const_mul] at h
  have hn : 2 * n + 1 ≠ 0 := by omega
  simp only [zero_pow hn, zero_mul, sub_zero] at h
  unfold gaussianEvenMoment
  linarith

theorem centered_gaussian_even_integral (n : ℕ) :
    (∫ x : ℝ, x ^ (2 * n) * Real.exp (-(x ^ 2))) = 2 * gaussianEvenMoment 0 n := by
  have hi := integrable_rpow_mul_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num)
    (s := (2 * n : ℕ)) (by exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _))
  simp only [Real.rpow_natCast, neg_one_mul] at hi
  rw [← integral_add_compl measurableSet_Ioi hi, compl_Ioi]
  have he : (∫ x : ℝ in Iic 0, x ^ (2 * n) * Real.exp (-(x ^ 2))) =
      ∫ x : ℝ in Ioi 0, x ^ (2 * n) * Real.exp (-(x ^ 2)) := by
    convert integral_comp_neg_Iic (0 : ℝ) (fun x : ℝ => x ^ (2 * n) * Real.exp (-(x ^ 2))) using 2
    · funext x
      rw [pow_mul, pow_mul, neg_sq]
    · simp
  rw [he]
  simp only [gaussianEvenMoment, subordinationGaussian, zero_pow (by decide : 2 ≠ 0),
    zero_div, add_zero]
  ring

/-- Actual centered scalar Gaussian law with the given variance. The zero
variance case is its deterministic pushforward at zero. -/
def sourceGaussianBase : Measure ℝ := volume.withDensity
  (fun x => ENNReal.ofReal (Real.exp (-(x ^ 2)) / Real.sqrt Real.pi))

def sourceGaussian (v : ℝ) : Measure ℝ :=
  sourceGaussianBase.map (fun x => Real.sqrt (2 * v) * x)

theorem sourceGaussianBase_even_moment (n : ℕ) :
    (∫ x : ℝ, x ^ (2 * n) ∂sourceGaussianBase) =
      (2 * gaussianEvenMoment 0 n) / Real.sqrt Real.pi := by
  have hmeas : Measurable (fun x : ℝ => Real.exp (-(x ^ 2)) / Real.sqrt Real.pi) := by fun_prop
  rw [sourceGaussianBase, integral_withDensity_eq_integral_toReal_smul hmeas.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  calc
    _ = ∫ x : ℝ, (x ^ (2 * n) * Real.exp (-(x ^ 2))) / Real.sqrt Real.pi := by
      apply integral_congr_ae
      filter_upwards with x
      rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
      ring
    _ = _ := by rw [integral_div, centered_gaussian_even_integral]

theorem gaussianEvenMoment_zero_zero : gaussianEvenMoment 0 0 = Real.sqrt Real.pi / 2 := by
  unfold gaussianEvenMoment subordinationGaussian
  norm_num only [Nat.mul_zero, pow_zero, one_mul, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero]
  simpa using integral_gaussian_Ioi (1 : ℝ)

theorem sourceGaussian_even_moments {v : ℝ} (hv : 0 ≤ v) :
    (∫ x : ℝ, x ^ 2 ∂sourceGaussian v) = v ∧
    (∫ x : ℝ, x ^ 4 ∂sourceGaussian v) = 3 * v ^ 2 := by
  have hmap : AEMeasurable (fun x : ℝ => Real.sqrt (2 * v) * x) sourceGaussianBase :=
    (by fun_prop : Measurable (fun x : ℝ => Real.sqrt (2 * v) * x)).aemeasurable
  have hhalf := centered_gaussian_half_recurrence 0
  have hquart := centered_gaussian_half_recurrence 1
  norm_num at hhalf hquart
  have hπ : Real.sqrt Real.pi ≠ 0 := by positivity
  have hs := Real.sq_sqrt (show 0 ≤ 2 * v by positivity)
  constructor
  · rw [sourceGaussian, integral_map hmap (by fun_prop)]
    simp_rw [mul_pow, integral_const_mul]
    rw [show (∫ x : ℝ, x ^ 2 ∂sourceGaussianBase) = _ from sourceGaussianBase_even_moment 1,
      hhalf, gaussianEvenMoment_zero_zero]
    rw [hs]
    field_simp
  · rw [sourceGaussian, integral_map hmap (by fun_prop)]
    simp_rw [mul_pow, integral_const_mul]
    rw [show (∫ x : ℝ, x ^ 4 ∂sourceGaussianBase) = _ from sourceGaussianBase_even_moment 2,
      hquart, hhalf, gaussianEvenMoment_zero_zero, show Real.sqrt (2 * v) ^ 4 = (2 * v) ^ 2 by
        rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hs]]
    field_simp

/-- Every nonnegative integer power is integrable under the scalar Gaussian
law, including the variance-zero law. -/
theorem sourceGaussian_power_integrable (v : ℝ) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (sourceGaussian v) := by
  have hscale : Measurable (fun x : ℝ => Real.sqrt (2 * v) * x) := by fun_prop
  have hk : Measurable (fun x : ℝ => x ^ k) := by fun_prop
  unfold sourceGaussian
  rw [integrable_map_measure hk.aestronglyMeasurable hscale.aemeasurable]
  have hf : Measurable (fun x : ℝ => Real.exp (-(x ^ 2)) / Real.sqrt Real.pi) := by fun_prop
  unfold sourceGaussianBase
  rw [integrable_withDensity_iff_integrable_smul' hf.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hi := integrable_rpow_mul_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num)
    (s := (k : ℝ)) (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _))
  simp only [Real.rpow_natCast, neg_one_mul] at hi
  apply (hi.const_mul ((Real.sqrt (2 * v)) ^ k / Real.sqrt Real.pi)).congr
  filter_upwards with x
  simp only [Function.comp_apply, ENNReal.toReal_ofReal (by positivity :
    0 ≤ Real.exp (-(x ^ 2)) / Real.sqrt Real.pi), smul_eq_mul, mul_pow]
  ring

/-- Pull the exact moments back through the given scalar Gaussian law. -/
theorem source_gaussian_observable_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : AEMeasurable X μ) {v : ℝ} (hv : 0 ≤ v)
    (hlaw : μ.map X = sourceGaussian v) :
    Integrable (fun ω => X ω ^ 2) μ ∧ Integrable (fun ω => X ω ^ 4) μ ∧
      (∫ ω, X ω ^ 2 ∂μ) = v ∧ (∫ ω, X ω ^ 4 ∂μ) = 3 * v ^ 2 := by
  have h₂ : Measurable (fun x : ℝ => x ^ 2) := by fun_prop
  have h₄ : Measurable (fun x : ℝ => x ^ 4) := by fun_prop
  constructor
  · exact (integrable_map_measure h₂.aestronglyMeasurable hX).mp
      (hlaw.symm ▸ sourceGaussian_power_integrable v 2)
  constructor
  · exact (integrable_map_measure h₄.aestronglyMeasurable hX).mp
      (hlaw.symm ▸ sourceGaussian_power_integrable v 4)
  constructor
  · rw [← integral_map hX h₂.aestronglyMeasurable, hlaw]
    exact (sourceGaussian_even_moments hv).1
  · rw [← integral_map hX h₄.aestronglyMeasurable, hlaw]
    exact (sourceGaussian_even_moments hv).2

end UV
