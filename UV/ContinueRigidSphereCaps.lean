import UV.ContinueRigidSphereCone

/-! Actual spherical-cap mass from Cartesian slices of the unit-ball cone. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Real Filter
open scoped ENNReal Interval Pointwise RealInnerProductSpace

namespace UV.ContinueRigidLaw

open UV.SectorPlane

private def capNormDirection (n : Metric.sphere (0 : Spatial) 1) : Direction :=
  ⟨n.1, mem_sphere_zero_iff_norm.1 n.2⟩

private theorem continuous_capNormDirection : Continuous capNormDirection :=
  continuous_subtype_val.subtype_mk _

private theorem solidAngle_eq_toSphere {U : Set Direction} (hU : MeasurableSet U) :
    solidAngle U = ((volume : Measure Spatial).toSphere) (capNormDirection ⁻¹' U) :=
  Measure.map_apply continuous_capNormDirection.measurable hU

private theorem axisCone_eq_smul (a : Direction) (t : ℝ) :
    axisCone a t = (Ioo (0:ℝ) 1) • ((Subtype.val : Metric.sphere (0 : Spatial) 1 → Spatial) ''
      (capNormDirection ⁻¹' (axialProjection a ⁻¹' Ioi t))) := by
  ext x
  constructor
  · rintro ⟨hx,hcut⟩
    have hx₀ : x ≠ 0 := by
      rintro rfl
      simp at hcut
    have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx₀
    let n : Metric.sphere (0 : Spatial) 1 := ⟨‖x‖⁻¹ • x, by
      apply mem_sphere_zero_iff_norm.2
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hp.le), inv_mul_cancel₀ hp.ne']⟩
    apply Set.mem_smul.2
    refine ⟨‖x‖, ⟨hp,hx⟩, (n : Spatial), ⟨n, ?_, rfl⟩, ?_⟩
    · change t < ⟪(a:Spatial), ‖x‖⁻¹ • x⟫
      rw [real_inner_smul_right, ← div_eq_inv_mul, lt_div_iff₀ hp]
      exact hcut
    · change ‖x‖ • (‖x‖⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ hp.ne', one_smul]
  · intro hx
    obtain ⟨r,hr,_,⟨n,hn,rfl⟩,rfl⟩ := Set.mem_smul.mp hx
    have hp : 0 < r := hr.1
    have hn' : t < ⟪(a : Spatial), (n : Spatial)⟫ := hn
    change ‖r • (n : Spatial)‖ < 1 ∧ t*‖r • (n : Spatial)‖ < ⟪(a : Spatial), r • (n : Spatial)⟫
    rw [norm_smul, mem_sphere_zero_iff_norm.mp n.property, Real.norm_eq_abs, abs_of_pos hp,
      mul_one, real_inner_smul_right]
    exact ⟨hr.2, by simpa only [mul_comm t r] using mul_lt_mul_of_pos_left hn' hp⟩

/-- A positive-height spatial spherical cap has its exact solid angle. -/
theorem solidAngle_axial_cap (a : Direction) {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    solidAngle (axialProjection a ⁻¹' Ioi t) = ENNReal.ofReal (2*π*(1-t)) := by
  have hm : MeasurableSet (axialProjection a ⁻¹' Ioi t) :=
    (continuous_axialProjection a).measurable measurableSet_Ioi
  rw [solidAngle_eq_toSphere hm, Measure.toSphere_apply'
    _ (continuous_capNormDirection.measurable hm), ← axisCone_eq_smul, axisCone_volume a ht ht₁,
    finrank_euclideanSpace_fin]
  calc
    _ = ENNReal.ofReal 3 * ENNReal.ofReal ((2*π/3)*(1-t)) := by norm_num
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
      congr 1
      ring

end UV.ContinueRigidLaw
