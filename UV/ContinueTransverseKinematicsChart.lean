import UV.ContinueTransverseKinematics
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-! Simultaneous normal coordinates for the two rest-routed shells. The
positive radial branch is independent of the retained norm-one direction. -/

noncomputable section

namespace UV.SectorPlane

open Set MeasureTheory
open scoped ContDiff

def restAxialRadialNormals (m t : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  ((z.1 + t / 2) ^ 2 - z.2 ^ 2 - m ^ 2, (z.1 - t / 2) ^ 2 - z.2 ^ 2 - m ^ 2)

theorem rest_axial_radial_normals_eq (m t : ℝ) (u : UnitVector Spatial) (z : ℝ × ℝ) :
    symmetricRestNormals m t (z.1, z.2 • u.val) = restAxialRadialNormals m t z := by
  rw [symmetric_rest_normals_eval]
  simp [restAxialRadialNormals, norm_smul, u.property, Real.norm_eq_abs, sq_abs]

def restNormalAxial (t : ℝ) (Y : ℝ × ℝ) : ℝ := (Y.1 - Y.2) / (2 * t)

def restNormalRadiusSq (m t : ℝ) (Y : ℝ × ℝ) : ℝ :=
  restNormalAxial t Y ^ 2 + (t / 2) ^ 2 - m ^ 2 - (Y.1 + Y.2) / 2

def restNormalInverse (m t : ℝ) (Y : ℝ × ℝ) : ℝ × ℝ :=
  (restNormalAxial t Y, Real.sqrt (restNormalRadiusSq m t Y))

theorem rest_normal_axial_forward (m : ℝ) {t : ℝ} (ht : t ≠ 0) (z : ℝ × ℝ) :
    restNormalAxial t (restAxialRadialNormals m t z) = z.1 := by
  unfold restNormalAxial restAxialRadialNormals
  dsimp only
  field_simp [ht]
  ring

theorem rest_normal_radius_sq_forward (m : ℝ) {t : ℝ} (ht : t ≠ 0) (z : ℝ × ℝ) :
    restNormalRadiusSq m t (restAxialRadialNormals m t z) = z.2 ^ 2 := by
  rw [restNormalRadiusSq, rest_normal_axial_forward m ht]
  unfold restAxialRadialNormals
  ring

theorem rest_normal_inverse_left (m : ℝ) {t : ℝ} (ht : t ≠ 0) {z : ℝ × ℝ} (hr : 0 ≤ z.2) :
    restNormalInverse m t (restAxialRadialNormals m t z) = z := by
  unfold restNormalInverse
  rw [rest_normal_axial_forward m ht, rest_normal_radius_sq_forward m ht, Real.sqrt_sq hr]

theorem rest_normal_inverse_right (m : ℝ) {t : ℝ} (ht : t ≠ 0) {Y : ℝ × ℝ}
    (hR : 0 ≤ restNormalRadiusSq m t Y) :
    restAxialRadialNormals m t (restNormalInverse m t Y) = Y := by
  apply Prod.ext <;> dsimp only [restAxialRadialNormals, restNormalInverse]
  all_goals
    rw [Real.sq_sqrt hR, restNormalRadiusSq, restNormalAxial]
    field_simp [ht]
    ring

/-- The inverse reconstructs the actual momentum using the normalized
radius of that point and the positive radial branch. -/
theorem rest_normal_momentum_reconstruction (m : ℝ) {t : ℝ} (ht : t ≠ 0)
    (q : MassiveMomentum) (hq : q.2 ≠ 0) :
    let z := restNormalInverse m t (symmetricRestNormals m t q)
    (z.1, z.2 • (restRadialUnit q.2 hq).val) = q := by
  have he := rest_axial_radial_normals_eq m t (restRadialUnit q.2 hq) (q.1, ‖q.2‖)
  rw [show ((q.1, ‖q.2‖).1, (q.1, ‖q.2‖).2 • (restRadialUnit q.2 hq).val) = q from
    Prod.ext rfl (rest_radial_unit_recovers q.2 hq)] at he
  change ((restNormalInverse m t (symmetricRestNormals m t q)).1,
    (restNormalInverse m t (symmetricRestNormals m t q)).2 • (restRadialUnit q.2 hq).val) = q
  rw [he, rest_normal_inverse_left m ht (norm_nonneg q.2)]
  exact Prod.ext rfl (rest_radial_unit_recovers q.2 hq)

theorem rest_normal_inverse_origin (m t : ℝ) :
    restNormalInverse m t 0 = (0, Real.sqrt ((t / 2) ^ 2 - m ^ 2)) := by
  simp [restNormalInverse, restNormalRadiusSq, restNormalAxial]

/-- On the positive radial branch this is an actual change of normal
coordinates, with a smooth inverse at every point of its open target. -/
def symmetricRestNormalChart (m t : ℝ) (ht : t ≠ 0) :
    OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) where
  toFun := restAxialRadialNormals m t
  invFun := restNormalInverse m t
  source := {z | 0 < z.2}
  target := {Y | 0 < restNormalRadiusSq m t Y}
  map_source' z hz := by
    change 0 < restNormalRadiusSq m t (restAxialRadialNormals m t z)
    rw [rest_normal_radius_sq_forward m ht]
    exact sq_pos_of_pos hz
  map_target' _ hY := Real.sqrt_pos.2 hY
  left_inv' _ hz := rest_normal_inverse_left m ht (le_of_lt hz)
  right_inv' _ hY := rest_normal_inverse_right m ht (le_of_lt hY)
  open_source := isOpen_lt continuous_const continuous_snd
  open_target := isOpen_lt continuous_const (by unfold restNormalRadiusSq restNormalAxial; fun_prop)
  continuousOn_toFun := Continuous.continuousOn (by unfold restAxialRadialNormals; fun_prop)
  continuousOn_invFun := Continuous.continuousOn (by
    unfold restNormalInverse restNormalRadiusSq restNormalAxial
    fun_prop)

theorem rest_normal_inverse_contDiffAt {n : WithTop ℕ∞} (m t : ℝ) (Y : ℝ × ℝ)
    (hY : 0 < restNormalRadiusSq m t Y) : ContDiffAt ℝ n (restNormalInverse m t) Y := by
  have hA : ContDiff ℝ n (restNormalAxial t) := by unfold restNormalAxial; fun_prop
  have hR : ContDiff ℝ n (restNormalRadiusSq m t) := by unfold restNormalRadiusSq restNormalAxial; fun_prop
  exact hA.contDiffAt.prodMk (hR.contDiffAt.sqrt hY.ne')

theorem rest_normal_strip {m t : ℝ} (hm : 0 < m) (ht : 2 * m < |t|) :
    ∃ b > 0, ∀ Y : ℝ × ℝ, |Y.1| ≤ b → |Y.2| ≤ b →
      0 < restNormalRadiusSq m t Y ∧ |restNormalAxial t Y| ≤ |t| / 4 := by
  have ht₀ : 0 < |t| := by linarith
  let R := (t / 2) ^ 2 - m ^ 2
  let b := min (R / 2) (t ^ 2 / 4)
  have hR : 0 < R := by
    have hsq := mul_pos (show 0 < |t| / 2 - m by linarith) (show 0 < |t| / 2 + m by positivity)
    dsimp only [R]
    rw [div_pow, ← sq_abs t, ← div_pow]
    nlinarith only [hsq]
  have hb : 0 < b := lt_min (half_pos hR) (div_pos (sq_pos_of_ne_zero (abs_pos.mp ht₀)) (by norm_num))
  refine ⟨b, hb, fun Y h₁ h₂ => ⟨?_, ?_⟩⟩
  · have hbR : b ≤ R / 2 := min_le_left _ _
    have hsum : (Y.1 + Y.2) / 2 ≤ b := by linarith [le_abs_self Y.1, le_abs_self Y.2]
    unfold restNormalRadiusSq
    dsimp [R] at hbR hR
    nlinarith only [hR, hbR, hsum, sq_nonneg (restNormalAxial t Y)]
  · have hbT : b ≤ t ^ 2 / 4 := min_le_right _ _
    have hΔ : |Y.1 - Y.2| ≤ 2 * b := (abs_sub _ _).trans (by linarith)
    rw [restNormalAxial, abs_div, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num),
      div_le_iff₀ (by positivity)]
    nlinarith only [hΔ, hbT, sq_abs t]

theorem rest_normal_strip_running_signs {m t : ℝ} (hm : 0 < m) (ht : 2 * m < t) :
    ∃ b > 0, ∀ (Y : ℝ × ℝ) (u : UnitVector Spatial), |Y.1| ≤ b → |Y.2| ≤ b →
      let z := restNormalInverse m t Y
      let q : MassiveMomentum := (z.1, z.2 • u.val)
      0 < z.2 ∧ symmetricRestNormals m t q = Y ∧
        axialSign (q + axialTransfer (t / 2)).1 = 1 ∧
        axialSign (q + axialTransfer (-(t / 2))).1 = -1 := by
  have ht₀ : 0 < t := by linarith
  obtain ⟨b, hb, h⟩ := rest_normal_strip hm (by rwa [abs_of_pos ht₀])
  refine ⟨b, hb, fun Y u h₁ h₂ => ?_⟩
  obtain ⟨hR, ha⟩ := h Y h₁ h₂
  rw [abs_of_pos ht₀] at ha
  have hplus : 0 < restNormalAxial t Y + t / 2 := by
    linarith [neg_le_abs (restNormalAxial t Y)]
  have hminus : restNormalAxial t Y + -(t / 2) < 0 := by
    linarith [le_abs_self (restNormalAxial t Y)]
  refine ⟨Real.sqrt_pos.2 hR, ?_, ?_⟩
  · rw [rest_axial_radial_normals_eq, rest_normal_inverse_right m ht₀.ne' hR.le]
  · simp [axial_transfer_coordinates, restNormalInverse, axialSign, hplus, hminus, hminus.not_gt]

end UV.SectorPlane
