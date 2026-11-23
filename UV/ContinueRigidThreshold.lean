import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The scalar axial integrals in the rigid-source spectral threshold.
The normalized axial angular measure is `dz / 2` on `[-1, 1]`. -/

noncomputable section

open MeasureTheory Set Real Filter
open scoped Interval Topology ENNReal

namespace UV.ContinueRigidThreshold

/-- The real inverse hyperbolic tangent in its logarithmic form. -/
def rigidArctanh (u : ℝ) : ℝ := (log (1+u) - log (1-u))/2

/-- The quotient used in the manuscript, continuously filled at rest. -/
def rigidArctanhRatio (u : ℝ) : ℝ := if u = 0 then 1 else rigidArctanh u / u

/-- Axial averaging with the uniform probability density on `[-1, 1]`. -/
def axialAverage (f : ℝ → ℝ) : ℝ := (1/2 : ℝ) * ∫ z in (-1 : ℝ)..1, f z

private theorem affine_denominators_pos {u z : ℝ} (hu : 0 ≤ u) (hu1 : u < 1)
    (hz : z ∈ [[(-1 : ℝ),1]]) : 0 < 1-u*z ∧ 0 < 1+u*z := by
  rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hz
  have hl := mul_le_mul_of_nonneg_left hz.1 hu
  have hh := mul_le_mul_of_nonneg_left hz.2 hu
  constructor <;> linarith

private theorem axial_denominator_pos {u z : ℝ} (hu : 0 ≤ u) (hu1 : u < 1)
    (hz : z ∈ [[(-1 : ℝ),1]]) : 0 < 1-u^2*z^2 := by
  obtain ⟨hminus,hplus⟩ := affine_denominators_pos hu hu1 hz
  calc
    0 < (1-u*z)*(1+u*z) := mul_pos hminus hplus
    _ = _ := by ring

private theorem axial_continuous_inv {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    ContinuousOn (fun z : ℝ => (1-u*z)⁻¹) [[(-1 : ℝ),1]] := by
  have hc : Continuous (fun z : ℝ => 1-u*z) := by fun_prop
  exact hc.continuousOn.inv₀ (fun _ hz => (affine_denominators_pos hu hu1 hz).1.ne')

private theorem affine_log_derivative (u z : ℝ) (hz : 0 < 1-u*z) :
    HasDerivAt (fun y => log (1-u*y)) ((-u)/(1-u*z)) z := by
  have ha : HasDerivAt (fun y : ℝ => 1-u*y) (-u) z := by
    simpa using (hasDerivAt_const z (1:ℝ)).sub ((hasDerivAt_id z).const_mul u)
  simpa only [div_eq_mul_inv, mul_comm] using ha.log hz.ne'

private theorem axial_affine_inv_integral {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    (∫ z in (-1 : ℝ)..1, (1-u*z)⁻¹) = 2*rigidArctanhRatio u := by
  by_cases hzero : u = 0
  · subst u
    norm_num [rigidArctanhRatio, intervalIntegral.integral_const]
  · have hi := show IntervalIntegrable (fun z : ℝ => (1-u*z)⁻¹) volume (-1) 1 from
      (axial_continuous_inv hu hu1).intervalIntegrable
    have hd (z : ℝ) (hz : z ∈ [[(-1 : ℝ),1]]) :
        HasDerivAt (fun y => -log (1-u*y)/u) ((1-u*z)⁻¹) z := by
      have hp := (affine_denominators_pos hu hu1 hz).1
      have he := ((affine_log_derivative u z hp).neg).div_const u
      convert he using 1
      field_simp [hzero, hp.ne']
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi, rigidArctanhRatio, if_neg hzero,
      rigidArctanh]
    rw [mul_one, show 1-u*(-1)=1+u by ring]
    ring

private theorem axial_even_inverse_identity {u z : ℝ} (hu : 0 ≤ u) (hu1 : u < 1)
    (hz : z ∈ [[(-1 : ℝ),1]]) :
    (1-u^2*z^2)⁻¹ = (1/2 : ℝ)*((1-u*z)⁻¹ + (1-u*(-z))⁻¹) := by
  obtain ⟨hp,hm⟩ := affine_denominators_pos hu hu1 hz
  rw [show 1-u*(-z)=1+u*z by ring]
  field_simp [(axial_denominator_pos hu hu1 hz).ne', hp.ne', hm.ne']
  ring

private theorem axial_even_inv_integral {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    (∫ z in (-1 : ℝ)..1, (1-u^2*z^2)⁻¹) = 2*rigidArctanhRatio u := by
  have hi : IntervalIntegrable (fun z : ℝ => (1-u*z)⁻¹) volume (-1) 1 :=
    (axial_continuous_inv hu hu1).intervalIntegrable
  have hc : Continuous (fun z : ℝ => 1-u*(-z)) := by fun_prop
  have hj : IntervalIntegrable (fun z : ℝ => (1-u*(-z))⁻¹) volume (-1) 1 :=
    (hc.continuousOn.inv₀ (fun z hz => by
      rw [show 1-u*(-z)=1+u*z by ring]
      exact (affine_denominators_pos hu hu1 hz).2.ne')).intervalIntegrable
  have hneg : (∫ z in (-1 : ℝ)..1, (1-u*(-z))⁻¹) = ∫ z in (-1 : ℝ)..1, (1-u*z)⁻¹ := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg (f := fun z : ℝ => (1-u*z)⁻¹) (a := -1) (b := 1))
  calc
    _ = ∫ z in (-1 : ℝ)..1, (1/2 : ℝ)*((1-u*z)⁻¹ + (1-u*(-z))⁻¹) := by
      apply intervalIntegral.integral_congr
      exact fun _ hz => axial_even_inverse_identity hu hu1 hz
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi hj, hneg,
        axial_affine_inv_integral hu hu1]
      ring

/-- The exact averaged symmetrized Coulomb-minus-transverse factor. -/
theorem axial_energy_factor {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    axialAverage (fun z => (1-u^2)/(1-u^2*z^2)) = (1-u^2)*rigidArctanhRatio u := by
  unfold axialAverage
  simp only [div_eq_mul_inv]
  rw [intervalIntegral.integral_const_mul, axial_even_inv_integral hu hu1]
  ring

/-- The angular energy factor before the two reflected directions are
averaged together. Its transverse subtraction uses one moving denominator. -/
def unsymmetrizedEnergyFactor (u z : ℝ) : ℝ := 1-u^2*(1-z^2)/(1-u*z)

theorem axial_energy_symmetrization {u z : ℝ} (hu : 0 ≤ u) (hu1 : u < 1)
    (hz : z ∈ [[(-1 : ℝ),1]]) :
    (unsymmetrizedEnergyFactor u z + unsymmetrizedEnergyFactor u (-z))/2 =
      (1-u^2)/(1-u^2*z^2) := by
  obtain ⟨hminus,hplus⟩ := affine_denominators_pos hu hu1 hz
  unfold unsymmetrizedEnergyFactor
  rw [show 1-u*(-z)=1+u*z by ring]
  field_simp [(axial_denominator_pos hu hu1 hz).ne', hminus.ne', hplus.ne']
  ring

private theorem axial_reciprocal_average_ge_one {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    1 ≤ rigidArctanhRatio u := by
  have hd (z : ℝ) : 1-u^2*z^2 ≤ 1 := by nlinarith [mul_nonneg (sq_nonneg u) (sq_nonneg z)]
  have hc : Continuous (fun z : ℝ => 1-u^2*z^2) := by fun_prop
  have hi : IntervalIntegrable (fun z : ℝ => (1-u^2*z^2)⁻¹) volume (-1) 1 :=
    (hc.continuousOn.inv₀ (fun _ hz => (axial_denominator_pos hu hu1 hz).ne')).intervalIntegrable
  have hc' : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume (-1) 1 :=
    continuous_const.intervalIntegrable _ _
  have hLe := intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1) hc' hi (fun z hz => by
    have hU : z ∈ [[(-1 : ℝ),1]] := by rwa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact (one_le_inv₀ (axial_denominator_pos hu hu1 hU)).2 (hd z))
  rw [axial_even_inv_integral hu hu1, intervalIntegral.integral_const] at hLe
  norm_num at hLe
  linarith

/-- The prescribed scalar threshold from the completed displacement. -/
def rigidThreshold (core e a u : ℝ) : ℝ := core + e^2/(8*π^2*a) * (1-u^2)*rigidArctanhRatio u

/-- The displayed closed-form charge threshold is strictly positive at
all real charges and all subluminal speeds when the core is positive. -/
theorem rigidThreshold_pos (core e a u : ℝ) (hc : 0 < core) (ha : 0 < a)
    (hu : 0 ≤ u) (hu1 : u < 1) : 0 < rigidThreshold core e a u := by
  have hsq : 0 ≤ 1-u^2 := by nlinarith [sq_nonneg u, mul_nonneg hu (sub_nonneg.mpr hu1.le)]
  have hr : 0 ≤ rigidArctanhRatio u := zero_le_one.trans (axial_reciprocal_average_ge_one hu hu1)
  unfold rigidThreshold
  positivity

/-- The extension used for a source at rest gives precisely the full
Coulomb energy added to its prescribed core. -/
theorem rigidThreshold_at_rest (core e a : ℝ) :
    rigidThreshold core e a 0 = core + e^2/(8*π^2*a) := by
  norm_num [rigidThreshold, rigidArctanhRatio]

/-- The inverse-tangent quotient really tends to one at rest. -/
theorem rigidArctanhRatio_rest_limit : Tendsto rigidArctanhRatio (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have hp : HasDerivAt (fun z : ℝ => log (1+z)) 1 0 := by
    have hd : HasDerivAt (fun z : ℝ => 1+z) 1 0 := by simpa using (hasDerivAt_id (0:ℝ)).const_add 1
    simpa using hd.log (by norm_num)
  have hm : HasDerivAt (fun z : ℝ => log (1-z)) (-1) 0 := by
    simpa using affine_log_derivative 1 0 (by norm_num)
  have hdiff : HasDerivAt rigidArctanh 1 0 := by
    simpa [rigidArctanh] using (hp.sub hm).div_const 2
  have hs := hasDerivAt_iff_tendsto_slope.mp hdiff
  apply hs.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hn : u ≠ 0 := fun h => hu (Set.mem_singleton_iff.mpr h)
  simp [slope, rigidArctanhRatio, rigidArctanh, hn, div_eq_mul_inv, mul_comm]

/-- The normalized scalar measure itself has exactly unit mass. -/
def normalizedAxialMeasure : Measure ℝ := (1/2 : ℝ≥0∞) • volume.restrict (Icc (-1 : ℝ) 1)

theorem normalizedAxialMeasure_probability : IsProbabilityMeasure normalizedAxialMeasure := by
  constructor
  unfold normalizedAxialMeasure
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

theorem axialAverage_eq_integral (f : ℝ → ℝ) :
    axialAverage f = ∫ z, f z ∂normalizedAxialMeasure := by
  unfold normalizedAxialMeasure axialAverage
  rw [integral_smul_measure, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  simp only [smul_eq_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]

/-- Averaging the original one-denominator energy expression gives the
same normalized closed form as the pointwise symmetrization. -/
theorem axial_unsymmetrized_energy_average {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    axialAverage (unsymmetrizedEnergyFactor u) = (1-u^2)*rigidArctanhRatio u := by
  have hc : Continuous (fun z : ℝ => u^2*(1-z^2)) := by fun_prop
  have hiC : ContinuousOn (unsymmetrizedEnergyFactor u) [[(-1 : ℝ),1]] := by
    change ContinuousOn (fun z => 1-u^2*(1-z^2)/(1-u*z)) [[(-1 : ℝ),1]]
    simp only [div_eq_mul_inv]
    exact continuous_const.continuousOn.sub (hc.continuousOn.mul (axial_continuous_inv hu hu1))
  have hnegC : ContinuousOn (fun z : ℝ => 1-u*(-z)) [[(-1 : ℝ),1]] := by fun_prop
  have hcNeg : Continuous (fun z : ℝ => u^2*(1-(-z)^2)) := by fun_prop
  have hjC : ContinuousOn (fun z => unsymmetrizedEnergyFactor u (-z)) [[(-1 : ℝ),1]] := by
    simp only [unsymmetrizedEnergyFactor, div_eq_mul_inv]
    refine continuous_const.continuousOn.sub (hcNeg.continuousOn.mul (hnegC.inv₀ (fun z hz => ?_)))
    rw [show 1-u*(-z)=1+u*z by ring]
    exact (affine_denominators_pos hu hu1 hz).2.ne'
  have hi : IntervalIntegrable (unsymmetrizedEnergyFactor u) volume (-1) 1 := hiC.intervalIntegrable
  have hj : IntervalIntegrable (fun z => unsymmetrizedEnergyFactor u (-z)) volume (-1) 1 := hjC.intervalIntegrable
  have hneg : (∫ z in (-1 : ℝ)..1, unsymmetrizedEnergyFactor u (-z)) =
      ∫ z in (-1 : ℝ)..1, unsymmetrizedEnergyFactor u z := by
    simpa only [neg_neg] using (intervalIntegral.integral_comp_neg
      (f := unsymmetrizedEnergyFactor u) (a := -1) (b := 1))
  have he : (∫ z in (-1 : ℝ)..1, (1-u^2)/(1-u^2*z^2)) =
      ∫ z in (-1 : ℝ)..1, unsymmetrizedEnergyFactor u z := by
    calc
      _ = ∫ z in (-1 : ℝ)..1, (unsymmetrizedEnergyFactor u z + unsymmetrizedEnergyFactor u (-z))/2 := by
        apply intervalIntegral.integral_congr
        exact fun _ hz => (axial_energy_symmetrization hu hu1 hz).symm
      _ = _ := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_add hi hj, hneg]
        ring
  rw [← axial_energy_factor hu hu1, axialAverage, axialAverage, he]

private theorem axial_affine_inv_sq_integral {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    (∫ z in (-1 : ℝ)..1, ((1-u*z)^2)⁻¹) = 2/(1-u^2) := by
  by_cases hzero : u = 0
  · subst u
    norm_num [intervalIntegral.integral_const]
  · have hC : ContinuousOn (fun z : ℝ => ((1-u*z)^2)⁻¹) [[(-1 : ℝ),1]] := by
      simpa only [inv_pow] using (axial_continuous_inv hu hu1).pow 2
    have hi : IntervalIntegrable (fun z : ℝ => ((1-u*z)^2)⁻¹) volume (-1) 1 := hC.intervalIntegrable
    have hd (z : ℝ) (hz : z ∈ [[(-1 : ℝ),1]]) :
        HasDerivAt (fun y => (1-u*y)⁻¹/u) (((1-u*z)^2)⁻¹) z := by
      have hp := (affine_denominators_pos hu hu1 hz).1
      have hbase : HasDerivAt (fun y : ℝ => 1-u*y) (-u) z := by
        simpa using (hasDerivAt_const z (1:ℝ)).sub ((hasDerivAt_id z).const_mul u)
      have h := ((hasDerivAt_inv hp.ne').comp z hbase).div_const u
      unfold Function.comp at h
      convert h using 1
      field_simp [hzero, hp.ne']
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi, mul_one, show 1-u*(-1)=1+u by ring]
    have hM : 1-u ≠ 0 := by linarith
    have hP : 1+u ≠ 0 := by linarith
    have hQ : 1-u^2 ≠ 0 := by
      rw [show 1-u^2=(1-u)*(1+u) by ring]
      exact mul_ne_zero hM hP
    field_simp [hM,hP,hQ,hzero]
    ring

/-- Occupation density without the constant charge and angular measure. -/
def axialOccupationFactor (u z : ℝ) : ℝ := u^2*(1-z^2)/(1-u*z)^2

/-- Integration of the two-denominator axial occupation term gives the
second displayed inverse-tangent coefficient. -/
theorem axial_occupation_average {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    axialAverage (axialOccupationFactor u) = 2*(rigidArctanhRatio u-1) := by
  have hC : ContinuousOn (fun z : ℝ => ((1-u*z)^2)⁻¹) [[(-1 : ℝ),1]] := by
    simpa only [inv_pow] using (axial_continuous_inv hu hu1).pow 2
  have hs : IntervalIntegrable (fun z : ℝ => ((1-u*z)^2)⁻¹) volume (-1) 1 := hC.intervalIntegrable
  have hi : IntervalIntegrable (fun z : ℝ => (1-u*z)⁻¹) volume (-1) 1 :=
    (axial_continuous_inv hu hu1).intervalIntegrable
  have h1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (-1) 1 := continuous_const.intervalIntegrable _ _
  have he : (∫ z in (-1 : ℝ)..1, axialOccupationFactor u z) =
      ∫ z in (-1 : ℝ)..1, -(1-u^2)*((1-u*z)^2)⁻¹ + 2*(1-u*z)⁻¹ - 1 := by
    apply intervalIntegral.integral_congr
    intro z hz
    unfold axialOccupationFactor
    field_simp [(affine_denominators_pos hu hu1 hz).1.ne']
    ring
  unfold axialAverage
  rw [he, intervalIntegral.integral_sub ((hs.const_mul _).add (hi.const_mul _)) h1,
    intervalIntegral.integral_add (hs.const_mul _) (hi.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    axial_affine_inv_sq_integral hu hu1, axial_affine_inv_integral hu hu1,
    intervalIntegral.integral_const]
  have hQ : 1-u^2 ≠ 0 := by
    rw [show 1-u^2=(1-u)*(1+u) by ring]
    exact mul_ne_zero (by linarith) (by linarith)
  simp only [smul_eq_mul]
  field_simp [hQ]
  ring

/-- Restores the original charge factor and the total solid angle `4π`. -/
theorem rigid_alpha_closed_form (e u : ℝ) (hu : 0 ≤ u) (hu1 : u < 1) :
    e^2/(2*(2*π)^3) * (4*π*axialAverage (axialOccupationFactor u)) =
      e^2/(2*π^2)*(rigidArctanhRatio u-1) := by
  rw [axial_occupation_average hu hu1]
  field_simp [pi_ne_zero]
  ring

/-- The scalar energy tends to its exact resting value. -/
theorem rigidThreshold_rest_limit (core e a : ℝ) :
    Tendsto (rigidThreshold core e a) (𝓝[≠] (0 : ℝ)) (𝓝 (core + e^2/(8*π^2*a))) := by
  have h : Tendsto (fun u : ℝ => 1-u^2) (𝓝[≠] (0:ℝ)) (𝓝 1) := by
    have hh : Continuous (fun u : ℝ => 1-u^2) := by fun_prop
    have h0 : ContinuousAt (fun u : ℝ => 1-u^2) (0:ℝ) := hh.continuousAt
    simpa using h0.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [rigidThreshold, mul_one] using
    (((h.const_mul (e^2/(8*π^2*a))).mul rigidArctanhRatio_rest_limit).const_add core)

end UV.ContinueRigidThreshold
