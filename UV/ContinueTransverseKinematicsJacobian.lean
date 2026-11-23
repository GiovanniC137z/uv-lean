import UV.ContinueTransverseKinematicsChart
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-! The Lebesgue change of variables from axial momentum and positive
spatial radius to the two independent denominators. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Set

private def restAxialRadialDerivative (t : ℝ) (z : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![2 * (z.1 + t / 2), -2 * z.2; 2 * (z.1 - t / 2), -2 * z.2]).toContinuousLinearMap

private theorem rest_axial_radial_hasFDerivAt (m t : ℝ) (z : ℝ × ℝ) :
    HasFDerivAt (restAxialRadialNormals m t) (restAxialRadialDerivative t z) z := by
  unfold restAxialRadialDerivative
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  have ha := hasFDerivAt_fst (𝕜 := ℝ) (p := z)
  have hr := (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).pow 2
  have h₁ := ((((ha.add_const (t / 2)).pow 2).sub hr).sub_const (m ^ 2))
  have h₂ := ((((ha.sub_const (t / 2)).pow 2).sub hr).sub_const (m ^ 2))
  convert h₁.prodMk h₂ using 2 <;> simp [sub_eq_add_neg, mul_comm]
  all_goals
    apply ContinuousLinearMap.ext
    intro v
    simp
    ring_nf
    simp

private theorem rest_axial_radial_derivative_det (t : ℝ) (z : ℝ × ℝ) :
    (restAxialRadialDerivative t z).det = -4 * t * z.2 := by
  unfold restAxialRadialDerivative
  rw [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin, Matrix.det_fin_two_of]
  ring

theorem rest_axial_radial_fderiv_det (m t : ℝ) (z : ℝ × ℝ) :
    (fderiv ℝ (restAxialRadialNormals m t) z).det = -4 * t * z.2 := by
  rw [(rest_axial_radial_hasFDerivAt m t z).fderiv, rest_axial_radial_derivative_det]

theorem rest_normal_inverse_fderiv_abs_det (m : ℝ) {t : ℝ} (ht : t ≠ 0) (Y : ℝ × ℝ)
    (hY : 0 < restNormalRadiusSq m t Y) :
    |(fderiv ℝ (restNormalInverse m t) Y).det| =
      1 / (4 * |t| * Real.sqrt (restNormalRadiusSq m t Y)) := by
  let e := symmetricRestNormalChart m t ht
  let z := restNormalInverse m t Y
  let B := restAxialRadialDerivative t z
  have hr : 0 < z.2 := Real.sqrt_pos.2 hY
  have hB : B.det ≠ 0 := by
    rw [rest_axial_radial_derivative_det]
    exact mul_ne_zero (mul_ne_zero (by norm_num) ht) hr.ne'
  let L := B.toContinuousLinearEquivOfDetNeZero hB
  have hderiv : HasFDerivAt e (L : ℝ × ℝ →L[ℝ] ℝ × ℝ) (e.symm Y) :=
    rest_axial_radial_hasFDerivAt m t z
  have hderivInv : HasFDerivAt (restNormalInverse m t) (L.symm : ℝ × ℝ →L[ℝ] ℝ × ℝ) Y :=
    e.hasFDerivAt_symm hY hderiv
  have hdet : (L.symm : ℝ × ℝ →L[ℝ] ℝ × ℝ).det * B.det = 1 :=
    LinearEquiv.det_symm_mul_det L.toLinearEquiv
  rw [hderivInv.fderiv, (eq_div_iff hB).mpr hdet, rest_axial_radial_derivative_det,
    abs_div, abs_mul, abs_mul, abs_of_pos hr]
  norm_num [z, restNormalInverse]

/-- The spatial radial factor r² and the inverse two-normal determinant
combine to the exact factor r/(4|t|), for any radial and axial integrand. -/
theorem rest_normal_radial_integral {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℝ) {t : ℝ} (ht : t ≠ 0) (G : ℝ × ℝ → V) :
    (∫ z in {z : ℝ × ℝ | 0 < z.2}, z.2 ^ 2 • G z) =
      ∫ Y in {Y : ℝ × ℝ | 0 < restNormalRadiusSq m t Y},
        (Real.sqrt (restNormalRadiusSq m t Y) / (4 * |t|)) • G (restNormalInverse m t Y) := by
  let e := symmetricRestNormalChart m t ht
  let h := fun z : ℝ × ℝ => z.2 ^ 2 • G z
  have hd (Y : ℝ × ℝ) (hY : Y ∈ e.symm.source) :
      HasFDerivAt e.symm (fderiv ℝ (restNormalInverse m t) Y) Y :=
    ((rest_normal_inverse_contDiffAt (n := 1) m t Y hY).differentiableAt le_rfl).hasFDerivAt
  have hi := integral_target_eq_integral_abs_det_fderiv_smul volume hd h
  change (∫ z in {z : ℝ × ℝ | 0 < z.2}, z.2 ^ 2 • G z) =
    ∫ Y in {Y : ℝ × ℝ | 0 < restNormalRadiusSq m t Y},
      |(fderiv ℝ (restNormalInverse m t) Y).det| •
        (Real.sqrt (restNormalRadiusSq m t Y) ^ 2 • G (restNormalInverse m t Y)) at hi
  rw [hi]
  apply setIntegral_congr_fun e.open_target.measurableSet
  intro Y hY
  dsimp only
  have hr : 0 < Real.sqrt (restNormalRadiusSq m t Y) := Real.sqrt_pos.2 hY
  rw [rest_normal_inverse_fderiv_abs_det m ht Y hY, smul_smul]
  congr 1
  field_simp [hr.ne', abs_ne_zero.mpr ht]

end UV.SectorPlane
