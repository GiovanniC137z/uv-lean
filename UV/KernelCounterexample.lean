import UV.Kernel
import UV.KernelCounterexampleComplex
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! A literal positive gapped Laplace measure whose continuation has nonreal
poles, as in prop:meromorphic-counterexample. -/

noncomputable section
open MeasureTheory Set Real Filter
open scoped ENNReal Topology

namespace UV

/-- The manuscript's sum ∑ₙ≥₁ 2⁻ⁿ δₙ, indexed from zero in Lean. -/
def gappedGeometricMeasure : Measure ℝ :=
  Measure.sum fun n : ℕ => ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) •
    Measure.dirac ((n + 1 : ℕ) : ℝ)

instance gappedGeometricMeasure_probability : IsProbabilityMeasure gappedGeometricMeasure := by
  constructor
  unfold gappedGeometricMeasure
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
  rw [ENNReal.tsum_geometric_add_one]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

theorem gappedGeometricMeasure_gap : gappedGeometricMeasure (Iio 1) = 0 := by
  unfold gappedGeometricMeasure
  rw [Measure.sum_apply _ measurableSet_Iio]
  apply ENNReal.tsum_eq_zero.mpr
  intro n
  rw [Measure.smul_apply]
  have hn : ((n + 1 : ℕ) : ℝ) ∉ Iio (1 : ℝ) := by
    simp only [mem_Iio, Nat.cast_add, Nat.cast_one]
    exact not_lt_of_ge (by linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n])
  rw [Measure.dirac_apply, indicator_of_notMem hn]
  simp

theorem gappedGeometricMeasure_support :
    ∀ᵐ τ : ℝ ∂gappedGeometricMeasure, 1 ≤ τ := by
  rw [ae_iff]
  have hs : {τ : ℝ | ¬1 ≤ τ} = Iio 1 := by ext τ; simp
  rw [hs]
  exact gappedGeometricMeasure_gap

theorem gappedGeometricLaplace_integrable {z : ℝ} (hz : 0 ≤ z) :
    Integrable (fun τ : ℝ => Real.exp (-τ * z)) gappedGeometricMeasure := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards [gappedGeometricMeasure_support] with τ hτ
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_one_iff.mpr
  nlinarith

theorem gappedGeometricLaplace_series {z : ℝ} (hz : 0 ≤ z) :
    laplace gappedGeometricMeasure z =
      ∑' n : ℕ, (Real.exp (-z) / 2) ^ (n + 1) := by
  have hi := gappedGeometricLaplace_integrable hz
  unfold laplace gappedGeometricMeasure at *
  rw [integral_sum_measure hi]
  apply tsum_congr
  intro n
  rw [integral_smul_measure, integral_dirac]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  have he : Real.exp (-((n + 1 : ℕ) : ℝ) * z) = Real.exp (-z) ^ (n + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he, div_pow, div_eq_mul_inv, inv_pow]
  ring

theorem gappedGeometricLaplace_exact {z : ℝ} (hz : 0 ≤ z) :
    laplace gappedGeometricMeasure z = (2 * Real.exp z - 1)⁻¹ := by
  have hexp : Real.exp (-z) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hq0 : 0 ≤ Real.exp (-z) / 2 := by positivity
  have hq1 : Real.exp (-z) / 2 < 1 := by linarith
  rw [gappedGeometricLaplace_series hz]
  simp_rw [pow_succ]
  rw [tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1, Real.exp_neg]
  have he : 1 ≤ Real.exp z := Real.one_le_exp_iff.mpr hz
  have hd : 2 * Real.exp z - 1 ≠ 0 := by linarith
  field_simp

theorem gappedGeometricLaplace_gap_bound {z : ℝ} (hz : 0 ≤ z) :
    laplace gappedGeometricMeasure z ≤ Real.exp (-z) := by
  unfold laplace
  calc
    _ ≤ ∫ _ : ℝ, Real.exp (-z) ∂gappedGeometricMeasure := by
      apply integral_mono_ae (gappedGeometricLaplace_integrable hz) (integrable_const _)
      filter_upwards [gappedGeometricMeasure_support] with τ hτ
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = _ := by simp

theorem gappedGeometricComplexLaplace_integrable {z : ℂ} (hz : 0 ≤ z.re) :
    Integrable (fun τ : ℝ => Complex.exp (-(τ : ℂ) * z)) gappedGeometricMeasure := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards [gappedGeometricMeasure_support] with τ hτ
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  apply Real.exp_le_one_iff.mpr
  nlinarith

theorem gappedGeometricComplexLaplace_exact {z : ℂ} (hz : 0 ≤ z.re) :
    (∫ τ : ℝ, Complex.exp (-(τ : ℂ) * z) ∂gappedGeometricMeasure) =
      (2 * Complex.exp z - 1)⁻¹ := by
  have hnorm : ‖Complex.exp (-z) / 2‖ < 1 := by
    rw [norm_div, Complex.norm_exp]
    norm_num only [Complex.norm_ofNat, Complex.neg_re]
    have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz)
    linarith
  have hi := gappedGeometricComplexLaplace_integrable hz
  have hseries : (∫ τ : ℝ, Complex.exp (-(τ : ℂ) * z) ∂gappedGeometricMeasure) =
      ∑' n : ℕ, (Complex.exp (-z) / 2) ^ (n + 1) := by
    unfold gappedGeometricMeasure at *
    rw [integral_sum_measure hi]
    apply tsum_congr
    intro n
    rw [integral_smul_measure, integral_dirac]
    simp only [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
      Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_ofNat]
    have he : Complex.exp (-(((n + 1 : ℕ) : ℝ) : ℂ) * z) =
        Complex.exp (-z) ^ (n + 1) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      simp only [Complex.ofReal_natCast]
      ring
    rw [he, div_pow, div_eq_mul_inv, inv_pow]
    ring
  rw [hseries]
  simp_rw [pow_succ]
  rw [tsum_mul_right, tsum_geometric_of_norm_lt_one hnorm, Complex.exp_neg]
  have hd : 2 * Complex.exp z - 1 ≠ 0 := by
    intro h
    have he : Complex.exp z = (1 / 2 : ℂ) := by linear_combination h / 2
    have hn : 1 ≤ ‖Complex.exp z‖ := by
      rw [Complex.norm_exp]
      exact Real.one_le_exp_iff.mpr hz
    rw [he] at hn
    norm_num at hn
  field_simp

theorem gappedGeometricContinuation_real {z : ℝ} (hz : 0 ≤ z) :
    gappedGeometricContinuation z = (laplace gappedGeometricMeasure z : ℂ) := by
  rw [gappedGeometricLaplace_exact hz]
  simp [gappedGeometricContinuation, Complex.ofReal_exp]

theorem gappedGeometricContinuation_complexLaplace {z : ℂ} (hz : 0 ≤ z.re) :
    gappedGeometricContinuation z =
      ∫ τ : ℝ, Complex.exp (-(τ : ℂ) * z) ∂gappedGeometricMeasure := by
  rw [gappedGeometricComplexLaplace_exact hz]
  rfl

/-- The named counterexample uses an actual positive normalized gapped measure,
and its actual complex Laplace transform has a nonreal meromorphic pole. -/
theorem gappedGeometric_counterexample :
    IsProbabilityMeasure gappedGeometricMeasure ∧
      gappedGeometricMeasure (Iio 1) = 0 ∧
      (∀ z : ℝ, 0 ≤ z → gappedGeometricContinuation z =
        (laplace gappedGeometricMeasure z : ℂ)) ∧
      MeromorphicOn gappedGeometricContinuation univ ∧
      ∃ z : ℂ, z ∈ Complex.slitPlane ∧ z.im ≠ 0 ∧
        meromorphicOrderAt gappedGeometricContinuation z < 0 := by
  refine ⟨inferInstance, gappedGeometricMeasure_gap,
    (fun z hz => gappedGeometricContinuation_real hz),
    gappedGeometricContinuation_meromorphic, gappedGeometricPole 1, ?_, ?_,
    gappedGeometricPole_order_negative 1⟩
  · exact gappedGeometricPole_mem_slitPlane (by norm_num)
  · exact gappedGeometricPole_nonreal (by norm_num)

end UV
