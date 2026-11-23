import UV.ContinueRigidSphereAxial

/-! Closed angular factors of the physical rigid-source spectral threshold. -/

noncomputable section

open MeasureTheory Set Real Filter
open scoped ENNReal Interval RealInnerProductSpace Topology

namespace UV.ContinueRigidLaw

open UV.SectorPlane UV.ContinueRigidThreshold

private theorem axialSolidAngle_eq_normalized :
    axialSolidAngle = ENNReal.ofReal (4*π) • normalizedAxialMeasure := by
  rw [axialSolidAngle, normalizedAxialMeasure, smul_smul]
  congr 1
  have h : (1/2 : ℝ≥0∞) = ENNReal.ofReal (1/2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
    norm_num
  rw [h, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 4*π)]
  congr 1
  ring

theorem integral_axialProjection (a : Direction) {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ n, f (axialProjection a n) ∂solidAngle) = (4*π) * axialAverage f := by
  rw [← integral_map (continuous_axialProjection a).measurable.aemeasurable
      hf.aestronglyMeasurable, map_axialProjection_solidAngle, axialSolidAngle_eq_normalized,
    integral_smul_measure, ENNReal.toReal_ofReal (by positivity : 0 ≤ 4*π),
    ← axialAverage_eq_integral, smul_eq_mul]

private def movingAxis (v : Spatial) (hv : v ≠ 0) : Direction :=
  ⟨‖v‖⁻¹ • v, by
    have hp := norm_pos_iff.mpr hv
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hp.le),
      inv_mul_cancel₀ hp.ne']⟩

private theorem speed_mul_axialProjection (v : Spatial) (hv : v ≠ 0) (n : Direction) :
    ‖v‖ * axialProjection (movingAxis v hv) n = ⟪v, (n : Spatial)⟫ := by
  have hp := norm_pos_iff.mpr hv
  unfold axialProjection
  change ‖v‖ * ⟪‖v‖⁻¹ • v, (n : Spatial)⟫ = _
  rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]

theorem angular_soft_exponent_closed (e : ℝ) {v : Spatial} (hv : ‖v‖ < 1) :
    (∫ n, angularWeight e v n ∂solidAngle) =
      e^2/(2*π^2)*(rigidArctanhRatio ‖v‖-1) := by
  by_cases h₀ : v = 0
  · subst v
    simp [angularWeight, rigidArctanhRatio]
  let a := movingAxis v h₀
  let k := e^2/(2*(2*π)^3)
  have hmeas : Measurable (axialOccupationFactor ‖v‖) := by
    unfold axialOccupationFactor
    fun_prop
  have he (n : Direction) :
      angularWeight e v n = k * axialOccupationFactor ‖v‖ (axialProjection a n) := by
    have hh := speed_mul_axialProjection v h₀ n
    unfold angularWeight doppler axialOccupationFactor
    change k * (‖v‖^2 - ⟪v, (n : Spatial)⟫^2) / (1-⟪v, (n : Spatial)⟫)^2 = _
    rw [← hh]
    change k * (‖v‖^2 - (‖v‖*axialProjection a n)^2) / (1-‖v‖*axialProjection a n)^2 = _
    rw [mul_div_assoc]
    congr 2
    ring
  rw [integral_congr_ae (ae_of_all _ he), integral_const_mul, integral_axialProjection a hmeas,
    axial_occupation_average (norm_nonneg v) hv]
  dsimp [k]
  field_simp [pi_ne_zero]
  ring

/-- The Coulomb-minus-transverse factor on actual unit spatial directions. -/
def angularEnergyFactor (v : Spatial) (n : Direction) : ℝ :=
  1 - (‖v‖^2 - ⟪v, (n : Spatial)⟫^2) / doppler v n

theorem angular_energy_factor_closed {v : Spatial} (hv : ‖v‖ < 1) :
    (∫ n, angularEnergyFactor v n ∂solidAngle)/(4*π) =
      (1-‖v‖^2)*rigidArctanhRatio ‖v‖ := by
  by_cases h₀ : v = 0
  · subst v
    have he : angularEnergyFactor (0 : Spatial) = fun _ ↦ 1 := by
      funext n
      simp [angularEnergyFactor]
    rw [he, integral_const, smul_eq_mul, mul_one, measureReal_def, solidAngle_mass,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 4*π), div_self (by positivity)]
    simp [rigidArctanhRatio]
  let a := movingAxis v h₀
  have hmeas : Measurable (unsymmetrizedEnergyFactor ‖v‖) := by
    unfold unsymmetrizedEnergyFactor
    fun_prop
  have he (n : Direction) :
      angularEnergyFactor v n = unsymmetrizedEnergyFactor ‖v‖ (axialProjection a n) := by
    have hh := speed_mul_axialProjection v h₀ n
    unfold angularEnergyFactor doppler unsymmetrizedEnergyFactor
    rw [← hh]
    change 1 - (‖v‖^2 - (‖v‖*axialProjection a n)^2) / (1-‖v‖*axialProjection a n) = _
    congr 3
    ring
  rw [integral_congr_ae (ae_of_all _ he), integral_axialProjection a hmeas,
    axial_unsymmetrized_energy_average (norm_nonneg v) hv]
  exact mul_div_cancel_left₀ _ (by positivity : (4*π : ℝ) ≠ 0)

end UV.ContinueRigidLaw
