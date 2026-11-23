import UV.ContinueNetworkDirectional
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Uniform positive comparisons for the literal Schwinger parameters
and exact, extended endpoint integrals. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UV

def directionalEndpointMass (a T : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) T, ENNReal.ofReal (t ^ (a - 1))

/-- The endpoint factor retains its value also in the divergent regime. -/
theorem directionalEndpointMass_eq {a T : ℝ} (hT : 0 < T) :
    directionalEndpointMass a T =
      if 0 < a then ENNReal.ofReal (T ^ a / a) else ⊤ := by
  have hm : Measurable (fun t : ℝ => t ^ (a - 1)) := measurable_id.pow_const _
  have hn : 0 ≤ᵐ[volume.restrict (Ioo 0 T)] (fun t : ℝ => t ^ (a - 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact Real.rpow_nonneg ht.1.le _
  unfold directionalEndpointMass
  split_ifs with ha
  · have hI := (intervalIntegral.integrableOn_Ioo_rpow_iff hT).2
        (by linarith : -1 < a - 1)
    rw [← ofReal_integral_eq_lintegral_ofReal hI hn,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hT.le,
      integral_rpow (Or.inl (by linarith : -1 < a - 1)),
      sub_add_cancel, Real.zero_rpow ha.ne', sub_zero]
  · by_contra hfin
    have hI := (lintegral_ofReal_ne_top_iff_integrable
      hm.aestronglyMeasurable hn).mp hfin
    exact ha (by linarith [(intervalIntegral.integrableOn_Ioo_rpow_iff hT).mp hI])

theorem directionalEndpointMass_lt_top_iff {a T : ℝ} (hT : 0 < T) :
    directionalEndpointMass a T < ⊤ ↔ 0 < a := by
  rw [directionalEndpointMass_eq hT]
  split_ifs <;> simp_all

theorem directionalEndpointMass_ne_zero (a : ℝ) {T : ℝ} (hT : 0 < T) :
    directionalEndpointMass a T ≠ 0 := by
  rw [directionalEndpointMass_eq hT]
  split_ifs with ha
  · exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  · exact ENNReal.top_ne_zero

def directionalSchwingerWeight (ν z t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (t ^ (ν - 1) * Real.exp (-(t * z)))

def directionalSchwingerLine (ν z : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) 1, directionalSchwingerWeight ν z t

def directionalSchwingerLower (ν : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-1) / ν)

def directionalSchwingerUpper (ν : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp 1 * Real.Gamma ν)

theorem directionalSchwingerLower_ne_zero {ν : ℝ} (hν : 0 < ν) :
    directionalSchwingerLower ν ≠ 0 :=
  ENNReal.ofReal_ne_zero_iff.mpr (by positivity)

theorem directionalSchwingerUpper_ne_zero {ν : ℝ} (hν : 0 < ν) :
    directionalSchwingerUpper ν ≠ 0 :=
  ENNReal.ofReal_ne_zero_iff.mpr (by positivity)

private theorem directionalSchwinger_full_integrable {ν a : ℝ} (hν : 0 < ν) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (ν - 1) * Real.exp (-(a * t))) (Ioi 0) := by
  have hG := (integrableOn_Ioi_comp_mul_left_iff
    (fun t : ℝ => t ^ (ν - 1) * Real.exp (-t)) 0 ha).2 (by
      simpa only [mul_zero, mul_comm (Real.exp _)] using Real.GammaIntegral_convergent hν)
  apply (hG.const_mul (a ^ (ν - 1))⁻¹).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change (a ^ (ν - 1))⁻¹ * ((a * t) ^ (ν - 1) * Real.exp (-(a * t))) = _
  rw [Real.mul_rpow ha.le ht.le, ← mul_assoc, ← mul_assoc,
    inv_mul_cancel₀ (Real.rpow_pos_of_pos ha _).ne', one_mul]

/-- Uniform in the nonnegative squared routed momentum, including zero.
The lower comparison uses times below 1/(1+z), and the upper comparison
uses the exact full gamma integral at rate 1+z. -/
theorem directionalSchwingerLine_compare {ν z : ℝ} (hν : 0 < ν) (hz : 0 ≤ z) :
    directionalSchwingerLower ν * ENNReal.ofReal ((1 + z) ^ (-ν)) ≤
      directionalSchwingerLine ν z ∧
    directionalSchwingerLine ν z ≤
      directionalSchwingerUpper ν * ENNReal.ofReal ((1 + z) ^ (-ν)) := by
  let a : ℝ := 1 + z
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : 1 ≤ a := le_add_of_nonneg_right hz
  have ht1 : a⁻¹ ≤ 1 := (inv_le_one₀ ha).2 ha1
  have ht0 : 0 < a⁻¹ := inv_pos.mpr ha
  have hlo :
      directionalSchwingerLower ν * ENNReal.ofReal (a ^ (-ν)) =
        ENNReal.ofReal (Real.exp (-1)) * directionalEndpointMass ν a⁻¹ := by
    rw [directionalEndpointMass_eq ht0, if_pos hν, directionalSchwingerLower,
      Real.inv_rpow ha.le, ← Real.rpow_neg ha.le,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  constructor
  · change directionalSchwingerLower ν * ENNReal.ofReal (a ^ (-ν)) ≤ _
    rw [hlo, directionalEndpointMass, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc
      _ ≤ ∫⁻ t in Ioo 0 a⁻¹, directionalSchwingerWeight ν z t := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        rw [directionalSchwingerWeight, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [mul_comm (Real.exp (-1))]
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht.1.le _)
        apply Real.exp_le_exp.mpr
        have hta : t * a < 1 := by
          apply (lt_div_iff₀ ha).mp
          simpa only [one_div] using ht.2
        have htz := mul_le_mul_of_nonneg_left (by dsimp [a]; linarith : z ≤ a) ht.1.le
        linarith
      _ ≤ _ := lintegral_mono' (Measure.restrict_mono (Ioo_subset_Ioo le_rfl ht1) le_rfl) le_rfl
  · have hγ :
        (∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (ν - 1) * Real.exp (-(a * t)))) =
          ENNReal.ofReal (a ^ (-ν) * Real.Gamma ν) := by
      have hg := directionalSchwinger_full_integrable hν ha
      have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
          (fun t : ℝ => t ^ (ν - 1) * Real.exp (-(a * t))) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _)
      rw [← ofReal_integral_eq_lintegral_ofReal hg hn,
        Real.integral_rpow_mul_exp_neg_mul_Ioi hν ha, one_div,
        Real.inv_rpow ha.le, ← Real.rpow_neg ha.le]
    calc
      directionalSchwingerLine ν z ≤
          ∫⁻ t in Ioo 0 1, ENNReal.ofReal (Real.exp 1) *
            ENNReal.ofReal (t ^ (ν - 1) * Real.exp (-(a * t))) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        rw [directionalSchwingerWeight, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [← mul_assoc, mul_comm (Real.exp 1) (t ^ (ν - 1)), mul_assoc, ← Real.exp_add]
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by dsimp [a]; nlinarith [ht.2])) (Real.rpow_nonneg ht.1.le _)
      _ ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp 1) *
            ENNReal.ofReal (t ^ (ν - 1) * Real.exp (-(a * t))) :=
        lintegral_mono' (Measure.restrict_mono Ioo_subset_Ioi_self le_rfl) le_rfl
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hγ, directionalSchwingerUpper,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        change ENNReal.ofReal _ = ENNReal.ofReal (Real.exp 1 * Real.Gamma ν * a ^ (-ν))
        congr 1
        ring

end UV
