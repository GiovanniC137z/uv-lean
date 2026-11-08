import UV.Kernel
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal

namespace UV

/-- The positive stable-half heat density without its normalization constant. -/
def oqedDensityCore (μ τ : ℝ) : ℝ :=
  τ ^ (-(3 : ℝ) / 2) * Real.exp (-(μ ^ 2 * τ) - 1 / (4 * τ))

def oqedDensity (μ τ : ℝ) : ℝ :=
  (Real.exp μ / (2 * Real.sqrt Real.pi)) * oqedDensityCore μ τ

def oqedMeasure (μ : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun τ => ENNReal.ofReal (oqedDensity μ τ))

theorem inverseCore_change (r τ : ℝ) (hτ : 0 < τ) :
    ((-1 : ℝ) ^ 2 * τ ^ ((-1 : ℝ) - 1)) *
      ((τ ^ (-1 : ℝ)) ^ (r - 1 / 2) * Real.exp (-(1 / 4 : ℝ) * τ ^ (-1 : ℝ))) =
    τ ^ (-r - 3 / 2) * Real.exp (-(1 / (4 * τ))) := by
  norm_num only [neg_one_sq, one_mul]
  rw [← Real.rpow_mul hτ.le, ← mul_assoc, ← Real.rpow_add hτ]
  congr 1
  · congr 1
    ring
  · rw [Real.rpow_neg_one]
    congr 1
    field_simp

theorem inverseCore_integrable {r : ℝ} (hr : -(1 / 2 : ℝ) < r) :
    IntegrableOn (fun τ : ℝ => τ ^ (-r - 3 / 2) * Real.exp (-(1 / (4 * τ)))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := 1) (s := r - 1 / 2) (b := (1 / 4 : ℝ)) (by linarith) (by norm_num) (by norm_num)
  simp only [Real.rpow_one] at h
  have hi := (integrableOn_Ioi_comp_rpow_iff
    (fun x : ℝ => x ^ (r - 1 / 2) * Real.exp (-(1 / 4 : ℝ) * x))
    (p := -1) (by norm_num)).mpr h
  apply hi.congr_fun _ measurableSet_Ioi
  intro τ hτ
  simpa only [abs_neg, abs_one, one_mul, smul_eq_mul, neg_one_sq] using inverseCore_change r τ hτ

theorem inverseCore_integral {r : ℝ} (hr : -(1 / 2 : ℝ) < r) :
    (∫ τ : ℝ in Ioi 0, τ ^ (-r - 3 / 2) * Real.exp (-(1 / (4 * τ)))) =
      (1 / 4 : ℝ) ^ (-(r + 1 / 2)) * Real.Gamma (r + 1 / 2) := by
  calc
    _ = ∫ τ : ℝ in Ioi 0, (|(-1 : ℝ)| * τ ^ ((-1 : ℝ) - 1)) •
        ((τ ^ (-1 : ℝ)) ^ (r - 1 / 2) * Real.exp (-(1 / 4 : ℝ) * τ ^ (-1 : ℝ))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro τ hτ
      simpa only [abs_neg, abs_one, one_mul, smul_eq_mul, neg_one_sq] using
        (inverseCore_change r τ hτ).symm
    _ = ∫ x : ℝ in Ioi 0, x ^ (r - 1 / 2) * Real.exp (-(1 / 4 : ℝ) * x) :=
      integral_comp_rpow_Ioi
        (fun x : ℝ => x ^ (r - 1 / 2) * Real.exp (-(1 / 4 : ℝ) * x))
        (p := -1) (by norm_num)
    _ = _ := by
      have h := integral_rpow_mul_exp_neg_mul_rpow
        (p := 1) (q := r - 1 / 2) (b := (1 / 4 : ℝ))
        (by norm_num) (by linarith) (by norm_num)
      simpa only [Real.rpow_one, div_one, one_div_one, mul_one,
        show r - 1 / 2 + 1 = r + 1 / 2 by ring] using h

theorem oqedDensity_nonneg (μ τ : ℝ) (hτ : 0 ≤ τ) : 0 ≤ oqedDensity μ τ := by
  unfold oqedDensity oqedDensityCore
  positivity

theorem oqedWeightedDensity_integrable (μ : ℝ) {r : ℝ} (hr : -(1 / 2 : ℝ) < r) :
    IntegrableOn (fun τ : ℝ => τ ^ (-r) * oqedDensity μ τ) (Ioi 0) := by
  have h := (inverseCore_integrable hr).const_mul (Real.exp μ / (2 * Real.sqrt Real.pi))
  refine h.mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    unfold oqedDensity oqedDensityCore
    fun_prop
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hτ.le _) (oqedDensity_nonneg _ _ hτ.le))]
  unfold oqedDensity oqedDensityCore
  have he : Real.exp (-(μ ^ 2 * τ) - 1 / (4 * τ)) ≤ Real.exp (-(1 / (4 * τ))) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ μ ^ 2 * τ := mul_nonneg (sq_nonneg _) hτ.le
    linarith
  calc
    _ = (Real.exp μ / (2 * Real.sqrt Real.pi)) *
        (τ ^ (-r - 3 / 2) * Real.exp (-(μ ^ 2 * τ) - 1 / (4 * τ))) := by
      rw [sub_eq_add_neg (-r) (3 / 2 : ℝ), Real.rpow_add hτ]
      ring
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hτ.le _)) (by positivity)

/-- The inverse power is assigned infinity at zero, as explicitly stipulated in
the manuscript's extended-moment convention. -/
def extendedInverseMoment (ρ : Measure ℝ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ τ in Ici 0, if τ = 0 then ⊤ else ENNReal.ofReal (τ ^ (-r)) ∂ρ

theorem extendedInverseMoment_split (ρ : Measure ℝ) (r : ℝ) :
    extendedInverseMoment ρ r = ⊤ * ρ {0} + inverseMoment ρ r := by
  have hset : Ici (0 : ℝ) = {0} ∪ Ioi 0 := by
    ext x
    simp [le_iff_eq_or_lt, eq_comm]
  unfold extendedInverseMoment inverseMoment
  rw [hset, lintegral_union measurableSet_Ioi (by simp), lintegral_singleton]
  congr 1
  · simp
  · apply setLIntegral_congr_fun measurableSet_Ioi
    intro τ hτ
    simp only [if_neg (ne_of_gt (show 0 < τ from hτ))]

theorem extendedInverseMoment_lt_top_iff (ρ : Measure ℝ) (r : ℝ) :
    extendedInverseMoment ρ r < ⊤ ↔ ρ {0} = 0 ∧ inverseMoment ρ r < ⊤ := by
  rw [extendedInverseMoment_split]
  by_cases hzero : ρ {0} = 0
  · simp [hzero]
  · simp [ENNReal.top_mul hzero, hzero]

theorem inversePower_lower_order {r s τ : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hτ : 0 < τ) :
    τ ^ (-r) ≤ 1 + τ ^ (-s) := by
  by_cases hsmall : τ ≤ 1
  · have h := Real.rpow_le_rpow_of_exponent_ge hτ hsmall (neg_le_neg hrs)
    linarith
  · have h := Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge hsmall) (neg_nonpos.mpr hr)
    have := Real.rpow_nonneg hτ.le (-s)
    linarith

theorem inverseMoment_lower_order_bound (ρ : Measure ℝ) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    inverseMoment ρ r ≤ ρ (Ioi 0) + inverseMoment ρ s := by
  unfold inverseMoment
  calc
    _ ≤ ∫⁻ τ in Ioi 0, (1 + ENNReal.ofReal (τ ^ (-s))) ∂ρ := by
      apply setLIntegral_mono' measurableSet_Ioi
      intro τ hτ
      calc
        ENNReal.ofReal (τ ^ (-r)) ≤ ENNReal.ofReal (1 + τ ^ (-s)) :=
          ENNReal.ofReal_le_ofReal (inversePower_lower_order hr hrs hτ)
        _ = _ := by rw [ENNReal.ofReal_add (by norm_num) (Real.rpow_nonneg hτ.le _)]; simp
    _ = _ := by rw [lintegral_add_left measurable_const]; simp

theorem inverseMoment_lower_order_finite (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hs : inverseMoment ρ s < ⊤) :
    inverseMoment ρ r < ⊤ :=
  lt_of_le_of_lt (inverseMoment_lower_order_bound ρ hr hrs)
    (ENNReal.add_lt_top.mpr ⟨measure_lt_top _ _, hs⟩)

theorem oqedDensity_measurable (μ : ℝ) : Measurable (oqedDensity μ) := by
  unfold oqedDensity oqedDensityCore
  fun_prop

theorem oqedMeasure_no_atom (μ x : ℝ) : oqedMeasure μ {x} = 0 := by
  unfold oqedMeasure
  exact measure_singleton x

theorem oqedMeasure_nonnegative_support (μ : ℝ) : oqedMeasure μ (Iic 0) = 0 := by
  unfold oqedMeasure
  rw [withDensity_apply _ measurableSet_Iic]
  have hnull : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false]
    rintro ⟨h₁, h₂⟩
    linarith
  simp [Measure.restrict_restrict, measurableSet_Iic, hnull]

theorem oqedInverseMoment_eq (μ r : ℝ) :
    inverseMoment (oqedMeasure μ) r =
      ∫⁻ τ in Ioi (0 : ℝ), ENNReal.ofReal (τ ^ (-r) * oqedDensity μ τ) := by
  unfold inverseMoment oqedMeasure
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  simp only [inter_self]
  have hmeas : Measurable (fun τ : ℝ => ENNReal.ofReal (τ ^ (-r))) := by fun_prop
  rw [lintegral_withDensity_eq_lintegral_mul _ (oqedDensity_measurable μ).ennreal_ofReal hmeas]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro τ hτ
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (oqedDensity_nonneg μ τ hτ.le)]
  congr 1
  ring

theorem oqedInverseMoment_finite (μ : ℝ) {r : ℝ} (hr : -(1 / 2 : ℝ) < r) :
    inverseMoment (oqedMeasure μ) r < ⊤ := by
  rw [oqedInverseMoment_eq]
  apply (hasFiniteIntegral_iff_ofReal ?_).mp (oqedWeightedDensity_integrable μ hr).hasFiniteIntegral
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  exact mul_nonneg (Real.rpow_nonneg hτ.le _) (oqedDensity_nonneg μ τ hτ.le)

instance oqedMeasure_isFinite (μ : ℝ) : IsFiniteMeasure (oqedMeasure μ) := by
  unfold oqedMeasure
  apply isFiniteMeasure_withDensity
  have hi := oqedWeightedDensity_integrable μ (r := 0) (by norm_num)
  simp only [neg_zero, Real.rpow_zero, one_mul] at hi
  apply ne_of_lt ((hasFiniteIntegral_iff_ofReal ?_).mp hi.hasFiniteIntegral)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  exact oqedDensity_nonneg μ τ hτ.le

theorem oqedWeightedDensity_zero_integral {r : ℝ} (hr : -(1 / 2 : ℝ) < r) :
    (∫ τ : ℝ in Ioi 0, τ ^ (-r) * oqedDensity 0 τ) =
      (4 : ℝ) ^ r * Real.Gamma (r + 1 / 2) / Real.sqrt Real.pi := by
  have hp : (1 / 4 : ℝ) ^ (-(r + 1 / 2)) = (4 : ℝ) ^ r * 2 := by
    rw [Real.rpow_neg_eq_inv_rpow, show (1 / 4 : ℝ)⁻¹ = 4 by norm_num,
      Real.rpow_add (by norm_num), ← Real.sqrt_eq_rpow]
    norm_num
  calc
    _ = (1 / (2 * Real.sqrt Real.pi)) *
        ∫ τ : ℝ in Ioi 0, τ ^ (-r - 3 / 2) * Real.exp (-(1 / (4 * τ))) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro τ hτ
      unfold oqedDensity oqedDensityCore
      simp only [Real.exp_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul,
        neg_zero, zero_sub]
      rw [sub_eq_add_neg (-r) (3 / 2 : ℝ), Real.rpow_add hτ]
      ring
    _ = _ := by
      rw [inverseCore_integral hr, hp]
      ring

theorem oqedInverseMoment_zero {r : ℝ} (hr : -(1 / 2 : ℝ) < r) :
    inverseMoment (oqedMeasure 0) r =
      ENNReal.ofReal ((4 : ℝ) ^ r * Real.Gamma (r + 1 / 2) / Real.sqrt Real.pi) := by
  rw [oqedInverseMoment_eq, ← oqedWeightedDensity_zero_integral hr]
  symm
  apply ofReal_integral_eq_lintegral_ofReal (oqedWeightedDensity_integrable 0 hr)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  exact mul_nonneg (Real.rpow_nonneg hτ.le _) (oqedDensity_nonneg _ _ hτ.le)

theorem oqedMeasure_zero_probability : IsProbabilityMeasure (oqedMeasure 0) := by
  constructor
  rw [oqedMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h := oqedInverseMoment_zero (r := 0) (by norm_num)
  rw [oqedInverseMoment_eq] at h
  simpa only [neg_zero, Real.rpow_zero, one_mul, zero_add, Real.Gamma_one_half_eq,
    div_self (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)), ENNReal.ofReal_one] using h

theorem oqedDensity_pos (μ τ : ℝ) (hτ : 0 < τ) : 0 < oqedDensity μ τ := by
  unfold oqedDensity oqedDensityCore
  positivity

/-- Every positive-depth interval has positive measure, so tempering does not
create a positive support gap. -/
theorem oqedMeasure_no_positive_gap (μ ε : ℝ) (hε : 0 < ε) :
    0 < oqedMeasure μ (Ioo 0 ε) := by
  apply pos_iff_ne_zero.mpr
  unfold oqedMeasure
  intro hzero
  have hmeas : Measurable (fun τ : ℝ => ENNReal.ofReal (oqedDensity μ τ)) := by
    exact (oqedDensity_measurable μ).ennreal_ofReal
  have hnull := (withDensity_apply_eq_zero hmeas).mp hzero
  have hset : {x : ℝ | ENNReal.ofReal (oqedDensity μ x) ≠ 0} ∩ Ioo 0 ε = Ioo 0 ε := by
    apply inter_eq_right.mpr
    intro x hx
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (oqedDensity_pos μ x hx.1))
  rw [hset, Measure.restrict_apply measurableSet_Ioo,
    inter_eq_self_of_subset_left Ioo_subset_Ioi_self, Real.volume_Ioo] at hnull
  have : ε ≤ 0 := by simpa only [sub_zero, ENNReal.ofReal_eq_zero] using hnull
  linarith

theorem oqedDensity_tempering_bound (μ τ : ℝ) (hτ : 0 < τ) :
    oqedDensity μ τ ≤ Real.exp μ * oqedDensity 0 τ := by
  unfold oqedDensity oqedDensityCore
  simp only [Real.exp_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul,
    neg_zero, zero_sub]
  have he : Real.exp (-(μ ^ 2 * τ) - 1 / (4 * τ)) ≤ Real.exp (-(1 / (4 * τ))) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ μ ^ 2 * τ := mul_nonneg (sq_nonneg _) hτ.le
    linarith
  calc
    _ ≤ (Real.exp μ / (2 * Real.sqrt Real.pi)) *
        (τ ^ (-(3 : ℝ) / 2) * Real.exp (-(1 / (4 * τ)))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hτ.le _)) (by positivity)
    _ = _ := by ring

/-- A quantitative bound valid for every real tempering parameter. -/
theorem oqedInverseMoment_bound (μ : ℝ) {r : ℝ} (hr : -(1 / 2 : ℝ) < r) :
    inverseMoment (oqedMeasure μ) r ≤
      ENNReal.ofReal (Real.exp μ *
        ((4 : ℝ) ^ r * Real.Gamma (r + 1 / 2) / Real.sqrt Real.pi)) := by
  have hmeas : Measurable (fun τ : ℝ => ENNReal.ofReal (τ ^ (-r) * oqedDensity 0 τ)) := by
    unfold oqedDensity oqedDensityCore
    fun_prop
  have hbound : inverseMoment (oqedMeasure μ) r ≤
      ENNReal.ofReal (Real.exp μ) * inverseMoment (oqedMeasure 0) r := by
    rw [oqedInverseMoment_eq, oqedInverseMoment_eq,
      ← lintegral_const_mul _ hmeas]
    apply setLIntegral_mono' measurableSet_Ioi
    intro τ hτ
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg μ)]
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_left (oqedDensity_tempering_bound μ τ hτ)
      (Real.rpow_nonneg hτ.le (-r))
    nlinarith
  rw [oqedInverseMoment_zero hr, ← ENNReal.ofReal_mul (Real.exp_nonneg μ)] at hbound
  exact hbound

theorem oqedInverseMoment_zero_one : inverseMoment (oqedMeasure 0) 1 = 2 := by
  rw [oqedInverseMoment_zero (by norm_num)]
  have hg := Real.Gamma_nat_add_half 1
  norm_num at hg
  rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by ring, hg]
  norm_num [Real.rpow_one]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)]
  norm_num

theorem oqedInverseMoment_zero_two : inverseMoment (oqedMeasure 0) 2 = 12 := by
  rw [oqedInverseMoment_zero (by norm_num)]
  have hg := Real.Gamma_nat_add_half 2
  norm_num at hg
  rw [show (2 : ℝ) + 1 / 2 = 5 / 2 by ring, hg]
  norm_num
  field_simp [ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)]
  norm_num

theorem oqedInverseMoment_zero_three : inverseMoment (oqedMeasure 0) 3 = 120 := by
  rw [oqedInverseMoment_zero (by norm_num)]
  have hg := Real.Gamma_nat_add_half 3
  norm_num at hg
  rw [show (3 : ℝ) + 1 / 2 = 7 / 2 by ring, hg]
  norm_num
  field_simp [ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)]
  norm_num

/-- At the exponential-moment endpoint, tempering cancels exactly. -/
theorem oqedDensity_exponential_endpoint (μ τ : ℝ) :
    Real.exp (μ ^ 2 * τ) * oqedDensity μ τ = Real.exp μ * oqedDensity 0 τ := by
  unfold oqedDensity oqedDensityCore
  simp only [Real.exp_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul,
    neg_zero, zero_sub]
  calc
    _ = (Real.exp μ / (2 * Real.sqrt Real.pi)) * τ ^ (-(3 : ℝ) / 2) *
        (Real.exp (μ ^ 2 * τ) * Real.exp (-(μ ^ 2 * τ) - 1 / (4 * τ))) := by ring
    _ = _ := by
      rw [← Real.exp_add, show μ ^ 2 * τ + (-(μ ^ 2 * τ) - 1 / (4 * τ)) =
        -(1 / (4 * τ)) by ring]
      ring

/-- Every exponential tilt at or below the endpoint retains all inverse
moments in the stable-half range. -/
theorem oqedExponentialWeightedDensity_integrable (μ : ℝ) {b r : ℝ}
    (hb : b ≤ μ ^ 2) (hr : -(1 / 2 : ℝ) < r) :
    IntegrableOn (fun τ : ℝ => Real.exp (b * τ) * (τ ^ (-r) * oqedDensity μ τ))
      (Ioi 0) := by
  refine ((oqedWeightedDensity_integrable 0 hr).const_mul (Real.exp μ)).mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    unfold oqedDensity oqedDensityCore
    fun_prop
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  rw [Real.norm_of_nonneg (by
    exact mul_nonneg (Real.exp_nonneg _)
      (mul_nonneg (Real.rpow_nonneg hτ.le _) (oqedDensity_nonneg μ τ hτ.le)))]
  calc
    _ ≤ Real.exp (μ ^ 2 * τ) * (τ ^ (-r) * oqedDensity μ τ) := by
      apply mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hb hτ.le))
        (mul_nonneg (Real.rpow_nonneg hτ.le _) (oqedDensity_nonneg μ τ hτ.le))
    _ = _ := by
      rw [mul_left_comm (Real.exp (μ ^ 2 * τ)), oqedDensity_exponential_endpoint]
      ring

theorem oqedExponentialDensity_integrable (μ : ℝ) {b : ℝ} (hb : b ≤ μ ^ 2) :
    IntegrableOn (fun τ : ℝ => Real.exp (b * τ) * oqedDensity μ τ) (Ioi 0) := by
  simpa only [neg_zero, Real.rpow_zero, one_mul] using
    oqedExponentialWeightedDensity_integrable μ hb (r := 0) (by norm_num)

/-- Tilting at the endpoint produces exactly a multiple of the stable-half
probability measure. -/
theorem oqedMeasure_exponential_endpoint (μ : ℝ) :
    (oqedMeasure μ).withDensity (fun τ => ENNReal.ofReal (Real.exp (μ ^ 2 * τ))) =
      ENNReal.ofReal (Real.exp μ) • oqedMeasure 0 := by
  have hd : Measurable (fun τ : ℝ => ENNReal.ofReal (oqedDensity μ τ)) :=
    (oqedDensity_measurable μ).ennreal_ofReal
  have he : Measurable (fun τ : ℝ => ENNReal.ofReal (Real.exp (μ ^ 2 * τ))) := by
    fun_prop
  unfold oqedMeasure
  rw [← withDensity_mul _ hd he, ← withDensity_smul _ (oqedDensity_measurable 0).ennreal_ofReal]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  change ENNReal.ofReal (oqedDensity μ τ) * ENNReal.ofReal (Real.exp (μ ^ 2 * τ)) =
    ENNReal.ofReal (Real.exp μ) * ENNReal.ofReal (oqedDensity 0 τ)
  rw [← ENNReal.ofReal_mul (oqedDensity_nonneg μ τ hτ.le),
    ← ENNReal.ofReal_mul (Real.exp_nonneg μ)]
  congr 1
  rw [mul_comm, oqedDensity_exponential_endpoint]

theorem oqedExponentialMoment_endpoint (μ : ℝ) :
    (∫⁻ τ : ℝ, ENNReal.ofReal (Real.exp (μ ^ 2 * τ)) ∂oqedMeasure μ) =
      ENNReal.ofReal (Real.exp μ) := by
  have h := congrArg (fun ρ : Measure ℝ => ρ univ) (oqedMeasure_exponential_endpoint μ)
  dsimp only at h
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    Measure.smul_apply, (oqedMeasure_zero_probability).measure_univ] at h
  simpa only [smul_eq_mul, mul_one] using h

theorem oqedExponentialMoment_bound (μ : ℝ) {b : ℝ} (hb : b ≤ μ ^ 2) :
    (∫⁻ τ : ℝ, ENNReal.ofReal (Real.exp (b * τ)) ∂oqedMeasure μ) ≤
      ENNReal.ofReal (Real.exp μ) := by
  rw [← oqedExponentialMoment_endpoint μ]
  apply lintegral_mono_ae
  have ha : ∀ᵐ τ ∂oqedMeasure μ, τ ∈ Ioi (0 : ℝ) := by
    apply (withDensity_absolutelyContinuous _ _).ae_le
    exact ae_restrict_mem measurableSet_Ioi
  filter_upwards [ha] with τ hτ
  exact ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hb hτ.le))

theorem oqedExponentialMoment_finite (μ : ℝ) {b : ℝ} (hb : b ≤ μ ^ 2) :
    (∫⁻ τ : ℝ, ENNReal.ofReal (Real.exp (b * τ)) ∂oqedMeasure μ) < ⊤ :=
  lt_of_le_of_lt (oqedExponentialMoment_bound μ hb) ENNReal.ofReal_lt_top

end UV
