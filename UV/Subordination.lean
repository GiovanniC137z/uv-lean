import UV.KernelMeasure
import UV.SubordinationChange
import UV.SubordinationTilt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open MeasureTheory Set Real Filter
open scoped ENNReal Topology

namespace UV

/-- The elementary reciprocal Gaussian used to prove stable-half subordination. -/
def subordinationGaussian (b x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2 + b ^ 2 / x ^ 2))

theorem subordinationGaussian_integrable (b : ℝ) :
    IntegrableOn (subordinationGaussian b) (Ioi 0) := by
  refine ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).integrableOn).mono'
    (by unfold subordinationGaussian; fun_prop) ?_
  filter_upwards with x
  unfold subordinationGaussian
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_exp.mpr
  have h := div_nonneg (sq_nonneg b) (sq_nonneg x)
  nlinarith

theorem subordinationGaussian_inversion {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    subordinationGaussian b (b / x) = subordinationGaussian b x := by
  unfold subordinationGaussian
  congr 1
  field_simp
  ring

theorem subordinationGaussian_weighted_integrable {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => (b / x ^ 2) * subordinationGaussian b x) (Ioi 0) := by
  have hg : IntegrableOn (fun x : ℝ => b * subordinationGaussian b (b * x)) (Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff (subordinationGaussian b) 0 hb).mpr
      (by simpa only [mul_zero] using subordinationGaussian_integrable b)
    exact h.const_mul b
  have hi := (integrableOn_Ioi_comp_rpow_iff _ (p := -1) (by norm_num)).mpr hg
  apply hi.congr_fun _ measurableSet_Ioi
  intro x hx
  simp only [abs_neg, abs_one, one_mul, smul_eq_mul, Real.rpow_neg_one] at *
  rw [show b * x⁻¹ = b / x by ring, subordinationGaussian_inversion hb hx]
  rw [show (-1 : ℝ) - 1 = -(2 : ℝ) by ring, Real.rpow_neg hx.le, Real.rpow_two]
  ring

theorem subordinationGaussian_inversion_integral {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ in Ioi 0, (b / x ^ 2) * subordinationGaussian b x) =
      ∫ x : ℝ in Ioi 0, subordinationGaussian b x := by
  calc
    _ = ∫ x : ℝ in Ioi 0, (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
        (b * subordinationGaussian b (b * x ^ (-1 : ℝ))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [abs_neg, abs_one, one_mul, smul_eq_mul, Real.rpow_neg_one]
      rw [show b * x⁻¹ = b / x by ring, subordinationGaussian_inversion hb hx]
      rw [show (-1 : ℝ) - 1 = -(2 : ℝ) by ring, Real.rpow_neg hx.le, Real.rpow_two]
      ring
    _ = ∫ x : ℝ in Ioi 0, b * subordinationGaussian b (b * x) :=
      integral_comp_rpow_Ioi (fun x : ℝ => b * subordinationGaussian b (b * x))
        (p := -1) (by norm_num)
    _ = b * (b⁻¹ * ∫ x : ℝ in Ioi 0, subordinationGaussian b x) := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi _ 0 hb]
      simp only [mul_zero, smul_eq_mul]
    _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul]

theorem subordinationCore_rpow_change (μ x : ℝ) (hx : 0 < x) :
    (|(-2 : ℝ)| * x ^ ((-2 : ℝ) - 1)) • oqedDensityCore μ (x ^ (-2 : ℝ)) =
      2 * subordinationGaussian (μ / 2) (x / 2) := by
  have hp : (x ^ (-2 : ℝ)) ^ (-(3 : ℝ) / 2) = x ^ (3 : ℝ) := by
    rw [← Real.rpow_mul hx.le]
    congr 1
    ring
  have hxpow : x ^ (-2 : ℝ) = 1 / x ^ 2 := by
    rw [Real.rpow_neg hx.le, Real.rpow_two, one_div]
  unfold oqedDensityCore subordinationGaussian
  rw [hp, smul_eq_mul]
  have hprod : x ^ ((-2 : ℝ) - 1) * x ^ (3 : ℝ) = 1 := by
    rw [← Real.rpow_add hx]
    norm_num
  rw [← mul_assoc, mul_assoc |(-2 : ℝ)|, hprod, mul_one, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2), hxpow]
  congr 1
  congr 1
  field_simp
  ring

theorem subordinationCore_integral_change (μ : ℝ) :
    (∫ τ : ℝ in Ioi 0, oqedDensityCore μ τ) =
      4 * ∫ x : ℝ in Ioi 0, subordinationGaussian (μ / 2) x := by
  calc
    _ = ∫ x : ℝ in Ioi 0, (|(-2 : ℝ)| * x ^ ((-2 : ℝ) - 1)) •
        oqedDensityCore μ (x ^ (-2 : ℝ)) :=
      (integral_comp_rpow_Ioi (oqedDensityCore μ) (p := -2) (by norm_num)).symm
    _ = ∫ x : ℝ in Ioi 0, 2 * subordinationGaussian (μ / 2) (x / 2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      exact fun x hx => subordinationCore_rpow_change μ x hx
    _ = 4 * ∫ x : ℝ in Ioi 0, subordinationGaussian (μ / 2) x := by
      rw [integral_const_mul]
      have hs := integral_comp_mul_right_Ioi (subordinationGaussian (μ / 2)) 0
        (b := (2 : ℝ)⁻¹) (by norm_num)
      norm_num only [zero_mul, inv_inv, smul_eq_mul] at hs
      simp only [div_eq_mul_inv, one_mul] at hs ⊢
      rw [hs]
      ring

theorem subordinationGaussian_shift_identity (b x : ℝ) (hx : 0 < x) :
    (1 + b / x ^ 2) * Real.exp (-(subordinateShift b x) ^ 2) =
      Real.exp (2 * b) * (subordinationGaussian b x +
        (b / x ^ 2) * subordinationGaussian b x) := by
  have he : -(subordinateShift b x) ^ 2 = 2 * b + -(x ^ 2 + b ^ 2 / x ^ 2) := by
    unfold subordinateShift
    field_simp
    ring
  rw [he, Real.exp_add]
  unfold subordinationGaussian
  ring

theorem subordinationGaussian_integral_pos {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ in Ioi 0, subordinationGaussian b x) =
      Real.sqrt Real.pi / 2 * Real.exp (-(2 * b)) := by
  have heq := subordinateShift_gaussian_integral hb
  have hre : (∫ x : ℝ in Ioi 0, (1 + b / x ^ 2) *
      Real.exp (-(subordinateShift b x) ^ 2)) =
      Real.exp (2 * b) * ((∫ x : ℝ in Ioi 0, subordinationGaussian b x) +
        ∫ x : ℝ in Ioi 0, (b / x ^ 2) * subordinationGaussian b x) := by
    calc
      _ = ∫ x : ℝ in Ioi 0, Real.exp (2 * b) * (subordinationGaussian b x +
          (b / x ^ 2) * subordinationGaussian b x) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        exact fun x hx => subordinationGaussian_shift_identity b x hx
      _ = _ := by
        rw [integral_const_mul, integral_add (subordinationGaussian_integrable b)
          (subordinationGaussian_weighted_integrable hb)]
  rw [subordinationGaussian_inversion_integral hb, heq] at hre
  rw [Real.exp_neg]
  have hi : (∫ x : ℝ in Ioi 0, subordinationGaussian b x) =
      Real.sqrt Real.pi / (2 * Real.exp (2 * b)) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
      (ne_of_gt (Real.exp_pos (2 * b))))).mpr
    nlinarith
  rw [hi]
  ring

theorem subordinationGaussian_integral {b : ℝ} (hb : 0 ≤ b) :
    (∫ x : ℝ in Ioi 0, subordinationGaussian b x) =
      Real.sqrt Real.pi / 2 * Real.exp (-(2 * b)) := by
  rcases eq_or_lt_of_le hb with heq | hpos
  · subst b
    simp only [subordinationGaussian, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_div, add_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
    simpa only [neg_one_mul, div_one] using integral_gaussian_Ioi 1
  · exact subordinationGaussian_integral_pos hpos

theorem oqedDensityCore_integral {μ : ℝ} (hμ : 0 ≤ μ) :
    (∫ τ : ℝ in Ioi 0, oqedDensityCore μ τ) =
      2 * Real.sqrt Real.pi * Real.exp (-μ) := by
  rw [subordinationCore_integral_change, subordinationGaussian_integral (by positivity),
    show 2 * (μ / 2) = μ by ring]
  ring

theorem oqedDensity_integral {μ : ℝ} (hμ : 0 ≤ μ) :
    (∫ τ : ℝ in Ioi 0, oqedDensity μ τ) = 1 := by
  unfold oqedDensity
  rw [integral_const_mul, oqedDensityCore_integral hμ, Real.exp_neg]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos), ne_of_gt (Real.exp_pos μ)]

/-- The manuscript's actual tempered stable-half density is normalized. -/
theorem oqedMeasure_probability {μ : ℝ} (hμ : 0 ≤ μ) :
    IsProbabilityMeasure (oqedMeasure μ) := by
  constructor
  rw [oqedMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hi := oqedWeightedDensity_integrable μ (r := 0) (by norm_num)
  simp only [neg_zero, Real.rpow_zero, one_mul] at hi
  rw [← ofReal_integral_eq_lintegral_ofReal hi ?_, oqedDensity_integral hμ]
  · exact ENNReal.ofReal_one
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  exact oqedDensity_nonneg μ τ hτ.le

/-- Genuine square-root subordination of the literal density, including the
finite exponential-moment endpoint. -/
theorem oqedLaplace (μ z : ℝ) (hz : 0 ≤ μ ^ 2 + z) :
    laplace (oqedMeasure μ) z = Real.exp (μ - Real.sqrt (μ ^ 2 + z)) := by
  rw [oqedLaplace_eq_tilted_mass μ z hz,
    (oqedMeasure_probability (Real.sqrt_nonneg (μ ^ 2 + z))).measure_univ,
    ENNReal.toReal_one, mul_one]

theorem oqedLaplace_nonnegative (μ z : ℝ) (hz : 0 ≤ z) :
    laplace (oqedMeasure μ) z = Real.exp (μ - Real.sqrt (μ ^ 2 + z)) :=
  oqedLaplace μ z (by positivity)

theorem oqedExponentialMoment_exact (μ b : ℝ) (hb : b ≤ μ ^ 2) :
    (∫⁻ τ : ℝ, ENNReal.ofReal (Real.exp (b * τ)) ∂oqedMeasure μ) =
      ENNReal.ofReal (Real.exp (μ - Real.sqrt (μ ^ 2 - b))) := by
  have h := oqedMeasure_laplace_tilt_mass μ (-b) (by linarith)
  rw [(oqedMeasure_probability (Real.sqrt_nonneg (μ ^ 2 + -b))).measure_univ, mul_one] at h
  simpa only [neg_neg, sub_eq_add_neg] using h

theorem oqedExponentialDensity_tendsto_atTop (μ b : ℝ) (hb : μ ^ 2 < b) :
    Tendsto (fun τ : ℝ => Real.exp (b * τ) * oqedDensity μ τ) atTop atTop := by
  have hd : Tendsto (fun τ : ℝ => Real.exp (-(1 / (4 * τ)))) atTop (𝓝 1) := by
    have hi : Tendsto (fun τ : ℝ => (-(1 / 4 : ℝ)) * τ⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds.mul
        (tendsto_inv_atTop_zero : Tendsto (fun τ : ℝ => τ⁻¹) atTop (𝓝 0)))
    simpa only [Real.exp_zero, div_eq_mul_inv, mul_inv_rev, one_mul,
      neg_mul, mul_neg, mul_comm, Function.comp_def] using
      (Real.continuous_exp.continuousAt.tendsto.comp hi)
  have hg := (tendsto_exp_mul_div_rpow_atTop (3 / 2 : ℝ) (b - μ ^ 2)
    (by linarith)).atTop_mul_pos (by norm_num : (0 : ℝ) < 1) hd
  have hc : 0 < Real.exp μ / (2 * Real.sqrt Real.pi) := by positivity
  have h := hg.const_mul_atTop hc
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
  have he : Real.exp (b * τ) * Real.exp (-(μ ^ 2 * τ) - 1 / (4 * τ)) =
      Real.exp ((b - μ ^ 2) * τ) * Real.exp (-(1 / (4 * τ))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  unfold oqedDensity oqedDensityCore
  rw [show -(3 : ℝ) / 2 = -(3 / 2 : ℝ) by ring, Real.rpow_neg hτ.le]
  calc
    _ = (Real.exp μ / (2 * Real.sqrt Real.pi)) * (τ ^ (3 / 2 : ℝ))⁻¹ *
        (Real.exp ((b - μ ^ 2) * τ) * Real.exp (-(1 / (4 * τ)))) := by ring
    _ = _ := by
      rw [← he]
      ring

theorem oqedExponentialMoment_infinite (μ b : ℝ) (hb : μ ^ 2 < b) :
    (∫⁻ τ : ℝ, ENNReal.ofReal (Real.exp (b * τ)) ∂oqedMeasure μ) = ⊤ := by
  have htail := (oqedExponentialDensity_tendsto_atTop μ b hb).eventually_ge_atTop 1
  obtain ⟨c, hc⟩ := eventually_atTop.mp htail
  have hd : Measurable (fun τ : ℝ => ENNReal.ofReal (oqedDensity μ τ)) :=
    (oqedDensity_measurable μ).ennreal_ofReal
  have he : Measurable (fun τ : ℝ => ENNReal.ofReal (Real.exp (b * τ))) := by fun_prop
  unfold oqedMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ hd he]
  have hdom : (∫⁻ τ : ℝ in Ioi (max 0 c), (1 : ℝ≥0∞)) ≤
      ∫⁻ τ : ℝ in Ioi (max 0 c),
        ENNReal.ofReal (oqedDensity μ τ) * ENNReal.ofReal (Real.exp (b * τ)) := by
    apply setLIntegral_mono' measurableSet_Ioi
    intro τ hτ
    rw [← ENNReal.ofReal_mul (oqedDensity_nonneg μ τ (le_of_lt
      (lt_of_le_of_lt (le_max_left _ _) hτ)))]
    apply ENNReal.one_le_ofReal.mpr
    rw [mul_comm]
    exact hc τ (le_trans (le_max_right _ _) hτ.le)
  have hsub : Ioi (max (0 : ℝ) c) ⊆ Ioi 0 := by
    intro τ hτ
    exact (le_max_left (0 : ℝ) c).trans_lt (show max 0 c < τ from hτ)
  have ht := hdom.trans (lintegral_mono_set hsub)
  rw [setLIntegral_one, Real.volume_Ioi] at ht
  exact top_le_iff.mp ht

theorem oqedExponentialMoment_finite_iff (μ b : ℝ) :
    (∫⁻ τ : ℝ, ENNReal.ofReal (Real.exp (b * τ)) ∂oqedMeasure μ) < ⊤ ↔
      b ≤ μ ^ 2 := by
  constructor
  · intro h
    by_contra hb
    rw [oqedExponentialMoment_infinite μ b (lt_of_not_ge hb)] at h
    exact (lt_irrefl ⊤) h
  · exact oqedExponentialMoment_finite μ

end UV
