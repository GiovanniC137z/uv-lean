import UV.ContinueTransverseSphere
import UV.ContinueTransverseKinematicsJacobian

/-! Exact transformation of the intrinsic four-momentum integral
to simultaneous shell normals for the symmetric rest routing. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Real Set
open scoped Topology

/-- Spatial polar density divided by the absolute two-normal Jacobian.
The factor for the sphere area is kept in the integral identity. -/
def restNormalMeasureFactor (m t : ℝ) (Y : ℝ × ℝ) : ℝ :=
  (restNormalInverse m t Y).2 / (4 * |t|)

theorem cone_spatial_mean_rest_multiplier (m t : ℝ)
    (f : MassiveMomentum → ℂ) (G : ℝ × ℝ → ℂ) (z : ℝ × ℝ) :
    coneSpatialMean (fun q => f q * G (symmetricRestNormals m t q)) z =
      coneSpatialMean f z * G (restAxialRadialNormals m t z) := by
  unfold coneSpatialMean
  have he (u : ConeSpatialSphere) :
      symmetricRestNormals m t (z.1,z.2 • (u : Spatial)) = restAxialRadialNormals m t z :=
    rest_axial_radial_normals_eq m t ⟨u.val,cone_spatial_direction_norm u⟩ z
  simp_rw [he,integral_mul_const,Complex.real_smul]
  ring

/-- If the multiplier is supported in the positive-radius chart target, its
four-momentum pairing is the exact flat two-normal integral with the
spherical mean of the full Cartesian test and the Jacobian factor. -/
theorem symmetric_rest_normal_integral (m t : ℝ) (ht : t ≠ 0)
    {f : MassiveMomentum → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
    {G : ℝ × ℝ → ℂ} (hG : Continuous G)
    (hgs : ∀ Y, restNormalRadiusSq m t Y ≤ 0 → G Y = 0) :
    (∫ q : MassiveMomentum, f q * G (symmetricRestNormals m t q)) =
      (4 * π) • ∫ Y : ℝ × ℝ, restNormalMeasureFactor m t Y •
        (coneSpatialMean f (restNormalInverse m t Y) * G Y) := by
  have hN : Continuous (symmetricRestNormals m t) := by
    unfold symmetricRestNormals
    exact (shiftedD_contDiff (n := 1) _ _).continuous.prodMk (shiftedD_contDiff (n := 1) _ _).continuous
  have hfG : Continuous (fun q : MassiveMomentum => f q * G (symmetricRestNormals m t q)) :=
    hf.mul (hG.comp hN)
  have hfs : HasCompactSupport (fun q : MassiveMomentum => f q * G (symmetricRestNormals m t q)) := hs.mul_right
  rw [cone_axial_spatial_integral hfG hfs]
  simp_rw [cone_spatial_mean_rest_multiplier]
  have hsour : univ ×ˢ Ioi (0 : ℝ) = {z : ℝ × ℝ | 0 < z.2} := by ext z; simp
  rw [hsour, rest_normal_radial_integral m ht]
  congr 1
  calc
    _ = ∫ Y in {Y | 0 < restNormalRadiusSq m t Y}, restNormalMeasureFactor m t Y •
          (coneSpatialMean f (restNormalInverse m t Y) * G Y) := by
        have ho : IsOpen {Y | 0 < restNormalRadiusSq m t Y} :=
          (symmetricRestNormalChart m t ht).open_target
        refine setIntegral_congr_fun ho.measurableSet fun Y hY => ?_
        have hr : 0 < restNormalRadiusSq m t Y := hY
        rw [rest_normal_inverse_right m ht hr.le]
        rfl
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro Y hY
      have hn : ¬ 0 < restNormalRadiusSq m t Y := hY
      rw [hgs Y (le_of_not_gt hn),mul_zero,smul_zero]

end UV.SectorPlane
