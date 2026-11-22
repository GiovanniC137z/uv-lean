import UV.VerifyVisitGamma
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The literal two-half Gaussian midpoint kernel with b = n + 1
measured normal coordinates and an arbitrary positive displacement law. -/

noncomputable section

open MeasureTheory Filter Set Real
open scoped ENNReal Topology

namespace UV.VerifyVisitCodimension

open UV.VerifyVisitGamma

abbrev NormalCoordinates (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))

def normalHalfLink (n : ℕ) (t : ℝ) (y : NormalCoordinates n) : ℝ :=
  (2 * Real.pi * t) ^ (-((n : ℝ) + 1) / 2) * Real.exp (-‖y‖ ^ (2 : ℕ) / (2 * t))

def normalGaussianMidpoint (n : ℕ) (t : ℝ) (μ : Measure (NormalCoordinates n)) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (normalHalfLink n t y * normalHalfLink n t y) ∂μ

def integratedGaussianMidpoint (n : ℕ) (T : ℝ) (μ : Measure (NormalCoordinates n)) : ℝ≥0∞ :=
  ∫⁻ t in Ioc 0 T, ENNReal.ofReal t⁻¹ * normalGaussianMidpoint n t μ

/-- Multiplying the two half-time kernels preserves exactly the
source's b-dimensional normal normalization. -/
theorem two_normal_half_links (n : ℕ) {t : ℝ} (ht : 0 < t) (y : NormalCoordinates n) :
    normalHalfLink n t y * normalHalfLink n t y =
      ((2 * Real.pi * t) ^ (n + 1))⁻¹ * Real.exp (-‖y‖ ^ (2 : ℕ) / t) := by
  have hB : 0 < 2 * Real.pi * t := mul_pos (mul_pos two_pos Real.pi_pos) ht
  unfold normalHalfLink
  rw [← pow_two, mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hB.le,
    show -((n : ℝ) + 1) / 2 * ((2 : ℕ) : ℝ) = -((n : ℝ) + 1) by push_cast; ring,
    Real.rpow_neg hB.le, ← Nat.cast_succ, Real.rpow_natCast, ← Real.exp_nat_mul]
  congr 2
  norm_num
  ring

theorem normal_gaussian_midpoint_eq (n : ℕ) {t : ℝ} (ht : 0 < t)
    (μ : Measure (NormalCoordinates n)) :
    normalGaussianMidpoint n t μ =
      ENNReal.ofReal (((2 * Real.pi * t) ^ (n + 1))⁻¹) *
        ∫⁻ y, ENNReal.ofReal (Real.exp (-‖y‖ ^ (2 : ℕ) / t)) ∂μ := by
  unfold normalGaussianMidpoint
  simp_rw [two_normal_half_links n ht, ENNReal.ofReal_mul
    (show 0 ≤ ((2 * Real.pi * t) ^ (n + 1))⁻¹ by positivity)]
  rw [lintegral_const_mul _ (by fun_prop)]

def normalMidpointCost (n : ℕ) (T : ℝ) (y : NormalCoordinates n) : ℝ≥0∞ :=
  if y = 0 then ⊤ else
    ENNReal.ofReal (((‖y‖ ^ (2 : ℕ)) ^ (n + 1))⁻¹) * upperGamma n (‖y‖ ^ (2 : ℕ) / T)

private theorem normal_midpoint_cost_measurable (n : ℕ) (T : ℝ) :
    Measurable (normalMidpointCost n T) := by
  unfold normalMidpointCost
  refine Measurable.ite (measurableSet_singleton _) measurable_const ?_
  exact (by fun_prop : Measurable (fun y : NormalCoordinates n =>
    ENNReal.ofReal (((‖y‖ ^ (2 : ℕ)) ^ (n + 1))⁻¹))).mul
    ((upper_gamma_antitone n).measurable.comp
      (show Measurable (fun y : NormalCoordinates n => ‖y‖ ^ (2 : ℕ) / T) by fun_prop))

private theorem normal_time_cost_point (n : ℕ) {T : ℝ} (hT : 0 < T) (y : NormalCoordinates n) :
    (∫⁻ t in Ioc (0 : ℝ) T, ENNReal.ofReal (normalTimeIntegrand n (‖y‖ ^ (2 : ℕ)) t)) =
        normalMidpointCost n T y := by
  by_cases hy : y = 0
  · subst y
    simpa [normalMidpointCost] using normal_time_zero_cost n hT
  · have hD : 0 < ‖y‖ ^ (2 : ℕ) := sq_pos_of_pos (norm_pos_iff.mpr hy)
    rw [normalMidpointCost, if_neg hy, normal_time_gamma_exact n hD hT]

set_option maxHeartbeats 700000 in
/-- The full normalized simultaneous heat readout is the weighted upper
incomplete Gamma cost, with an infinite coincident value. -/
theorem gaussian_midpoint_integrated_gamma (n : ℕ) {T : ℝ} (hT : 0 < T)
    (μ : Measure (NormalCoordinates n)) [SFinite μ] :
    integratedGaussianMidpoint n T μ =
      ENNReal.ofReal (((2 * Real.pi) ^ (n + 1))⁻¹) * ∫⁻ y, normalMidpointCost n T y ∂μ := by
  let c : ℝ := ((2 * Real.pi) ^ (n + 1))⁻¹
  have hc : 0 ≤ c := by unfold c; positivity
  let f : ℝ → NormalCoordinates n → ℝ≥0∞ := fun t y =>
    ENNReal.ofReal (normalTimeIntegrand n (‖y‖ ^ (2 : ℕ)) t)
  have hf : Measurable (Function.uncurry f) := by unfold f Function.uncurry normalTimeIntegrand; fun_prop
  have he (t : ℝ) (ht : 0 < t) :
      ENNReal.ofReal t⁻¹ * normalGaussianMidpoint n t μ =
        ENNReal.ofReal c * ∫⁻ y, f t y ∂μ := by
    have hf' : Measurable (f t) := by unfold f normalTimeIntegrand; fun_prop
    rw [normal_gaussian_midpoint_eq n ht μ, ← mul_assoc,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le),
      ← lintegral_const_mul _ (by fun_prop),
      ← lintegral_const_mul _ hf']
    apply lintegral_congr
    intro y
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hc]
    unfold normalTimeIntegrand c
    congr 1
    rw [mul_pow, pow_succ t (n + 1)]
    field_simp [ht.ne', Real.pi_ne_zero]
  calc
    _ = ∫⁻ t in Ioc (0 : ℝ) T, ENNReal.ofReal c * ∫⁻ y, f t y ∂μ := by
      unfold integratedGaussianMidpoint
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using he t ht.1
    _ = ENNReal.ofReal c * ∫⁻ t in Ioc (0 : ℝ) T, ∫⁻ y, f t y ∂μ :=
      lintegral_const_mul _ hf.lintegral_prod_right
    _ = _ := by
      rw [lintegral_lintegral_swap hf.aemeasurable]
      simp_rw [f, normal_time_cost_point n hT]
      rfl

/-- The positive inverse power used near coincidence. The separate
atom test retains the singular value at the origin. -/
def inverseNormalPower (n : ℕ) (y : NormalCoordinates n) : ℝ≥0∞ :=
  ENNReal.ofReal ((‖y‖ ^ (2 * (n + 1)))⁻¹)

private theorem inverse_normal_power_eq (n : ℕ) (y : NormalCoordinates n) :
    inverseNormalPower n y = ENNReal.ofReal (((‖y‖ ^ (2 : ℕ)) ^ (n + 1))⁻¹) := by
  rw [inverseNormalPower, pow_mul]

theorem gaussian_midpoint_finiteness_iff (n : ℕ) {T : ℝ} (hT : 0 < T)
    (μ : Measure (NormalCoordinates n)) [IsFiniteMeasure μ] :
    integratedGaussianMidpoint n T μ ≠ ⊤ ↔
      μ ({0} : Set (NormalCoordinates n)) = 0 ∧
        (∫⁻ y in Metric.closedBall (0 : NormalCoordinates n) 1, inverseNormalPower n y ∂μ) ≠ ⊤ := by
  let B := Metric.closedBall (0 : NormalCoordinates n) 1
  have hB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hI : Measurable (inverseNormalPower n) := by unfold inverseNormalPower; fun_prop
  have hM := normal_midpoint_cost_measurable n T
  have hγ0 : upperGamma n 0 ≠ ⊤ := upper_gamma_ne_top n le_rfl
  have hγ1 : 0 < upperGamma n (1 / T) := upper_gamma_pos n (div_pos one_pos hT)
  have hC : 0 < ENNReal.ofReal (((2 * Real.pi) ^ (n + 1))⁻¹) :=
    ENNReal.ofReal_pos.mpr (by positivity)
  have hh (y : NormalCoordinates n) (hy : y ≠ 0) : normalMidpointCost n T y =
      inverseNormalPower n y * upperGamma n (‖y‖ ^ (2 : ℕ) / T) := by
    rw [normalMidpointCost, if_neg hy, inverse_normal_power_eq]
  have htop : {y | normalMidpointCost n T y = ⊤} = ({0} : Set (NormalCoordinates n)) := by
    ext y
    by_cases hy : y = 0
    · simp [hy, normalMidpointCost]
    · simp only [mem_setOf_eq, mem_singleton_iff, hy, iff_false]
      rw [hh y hy, inverseNormalPower]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (upper_gamma_ne_top n (by positivity))
  rw [gaussian_midpoint_integrated_gamma n hT]
  constructor
  · intro hfin
    have hfin' : (∫⁻ y, normalMidpointCost n T y ∂μ) ≠ ⊤ := by
      intro himp
      exact hfin (by rw [himp, ENNReal.mul_top hC.ne'])
    refine ⟨by simpa only [htop] using measure_eq_top_of_lintegral_ne_top hM.aemeasurable hfin', ?_⟩
    have hbnd : upperGamma n (1 / T) * (∫⁻ y in B, inverseNormalPower n y ∂μ) ≤
        ∫⁻ y, normalMidpointCost n T y ∂μ := by
      rw [← lintegral_const_mul _ hI]
      calc
        _ ≤ ∫⁻ y in B, normalMidpointCost n T y ∂μ := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem hB] with y hy
          by_cases hy0 : y = 0
          · simp [normalMidpointCost, hy0]
          · have hy1 : ‖y‖ ≤ 1 := by simpa [B, Metric.mem_closedBall, dist_zero_right] using hy
            have hy2 : ‖y‖ ^ (2 : ℕ) ≤ 1 := by
              simpa using pow_le_pow_left₀ (norm_nonneg y) hy1 2
            rw [hh y hy0, mul_comm (upperGamma n (1 / T))]
            exact mul_le_mul_left' (upper_gamma_antitone n (div_le_div_of_nonneg_right hy2 hT.le)) _
        _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl
    change (∫⁻ y in B, inverseNormalPower n y ∂μ) ≠ ⊤
    intro ht
    rw [ht, ENNReal.mul_top hγ1.ne'] at hbnd
    exact hfin' (top_le_iff.mp hbnd)
  · rintro ⟨ha, hloc⟩
    have hfar : (∫⁻ y in Bᶜ, inverseNormalPower n y ∂μ) ≠ ⊤ := by
      refine ne_top_of_le_ne_top (measure_ne_top μ Bᶜ) ?_
      rw [← setLIntegral_one]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hB.compl] with y hy
      have hy1 : 1 ≤ ‖y‖ := by
        have hp : ¬ ‖y‖ ≤ 1 := by simpa [B, Metric.mem_closedBall, dist_zero_right] using hy
        exact le_of_lt (lt_of_not_ge hp)
      have hp : 1 ≤ ‖y‖ ^ (2 * (n + 1)) := one_le_pow₀ hy1
      unfold inverseNormalPower
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (inv_le_one_of_one_le₀ hp)
    have hi : (∫⁻ y, inverseNormalPower n y ∂μ) ≠ ⊤ := by
      rw [← lintegral_add_compl _ hB]
      exact ENNReal.add_ne_top.mpr ⟨hloc, hfar⟩
    have he : ∀ᵐ y ∂μ, y ≠ (0 : NormalCoordinates n) := by simpa [ae_iff] using ha
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top
      (ENNReal.mul_ne_top hi hγ0) ?_)
    rw [← lintegral_mul_const _ hI]
    apply lintegral_mono_ae
    filter_upwards [he] with y hy
    rw [hh y hy]
    exact mul_le_mul_left' (upper_gamma_antitone n (by positivity : 0 ≤ ‖y‖ ^ (2 : ℕ) / T)) _

end UV.VerifyVisitCodimension
