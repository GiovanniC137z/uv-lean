import UV.ContinueShiftedShellGeometry
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! The two symmetric rest-routing normals on the intrinsic Lorentzian
momentum chart of a locked sector plane. The two test directions are the
original axial unit and the normalized spatial radius of the same point. -/

noncomputable section

namespace UV.SectorPlane

open scoped RealInnerProductSpace

def symmetricRestNormals (m t : ℝ) (q : MassiveMomentum) : ℝ × ℝ :=
  (shiftedD m (axialTransfer (t / 2)) q, shiftedD m (axialTransfer (-(t / 2))) q)

theorem shiftedD_hasFDerivAt (m : ℝ) (c q : MassiveMomentum) :
    HasFDerivAt (shiftedD m c) (2 • coneCovector (q + c)) q := by
  have h := (shell_square_hasFDerivAt (q + c)).comp q
    (((ContinuousLinearMap.id ℝ MassiveMomentum).hasFDerivAt (x := q)).add_const c)
  simpa only [ContinuousLinearMap.comp_id] using h.sub_const (m ^ 2)

/-- The radial direction has a literal Euclidean spatial norm of one. -/
def restRadialUnit (p : Spatial) (hp : p ≠ 0) : UnitVector Spatial :=
  ⟨‖p‖⁻¹ • p, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp)]⟩

theorem rest_radial_unit_inner (p : Spatial) (hp : p ≠ 0) :
    ⟪p, (restRadialUnit p hp).val⟫ = ‖p‖ := by
  rw [restRadialUnit, real_inner_smul_right, real_inner_self_eq_norm_sq, pow_two,
    ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp), one_mul]

theorem rest_radial_unit_recovers (p : Spatial) (hp : p ≠ 0) :
    ‖p‖ • (restRadialUnit p hp).val = p := by
  rw [restRadialUnit, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hp), one_smul]

theorem symmetric_rest_normals_eval (m t : ℝ) (q : MassiveMomentum) :
    symmetricRestNormals m t q =
      ((q.1 + t / 2) ^ 2 - ‖q.2‖ ^ 2 - m ^ 2,
        (q.1 - t / 2) ^ 2 - ‖q.2‖ ^ 2 - m ^ 2) := by
  simp [symmetricRestNormals, axial_transfer_coordinates, shiftedD, massiveD, shellSquare, sub_eq_add_neg]

theorem symmetric_rest_shell_radius_pos {m t : ℝ} (hm : 0 < m) (ht : 2 * m < |t|)
    (q : MassiveMomentum) (hq : symmetricRestNormals m t q = 0) : 0 < ‖q.2‖ := by
  have ht₀ : t ≠ 0 := abs_pos.mp (by linarith)
  have h := ((symmetric_rest_shell_intersection m t ht₀ q).mp
    ⟨congrArg Prod.fst hq, congrArg Prod.snd hq⟩).2
  have hpos : 0 < (|t| / 2) ^ 2 - m ^ 2 := by
    have he := mul_pos (show 0 < |t| / 2 - m by linarith) (show 0 < |t| / 2 + m by positivity)
    nlinarith only [he]
  rw [div_pow, sq_abs, ← div_pow, ← h] at hpos
  exact lt_of_le_of_ne (norm_nonneg _) fun hzero => by simp [← hzero] at hpos

/-- Rows are the two routed shell differentials. Columns are the actual
unit axial direction and the Euclidean lift of the normalized radius. -/
def symmetricRestUnitDifferential (m t : ℝ) (q : MassiveMomentum) (hq : q.2 ≠ 0) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![fderiv ℝ (shiftedD m (axialTransfer (t / 2))) q (WithLp.ofLp coneAxialUnit.val),
       fderiv ℝ (shiftedD m (axialTransfer (t / 2))) q
        (WithLp.ofLp (coneSpatialUnit (restRadialUnit q.2 hq)).val);
     fderiv ℝ (shiftedD m (axialTransfer (-(t / 2)))) q (WithLp.ofLp coneAxialUnit.val),
       fderiv ℝ (shiftedD m (axialTransfer (-(t / 2)))) q
        (WithLp.ofLp (coneSpatialUnit (restRadialUnit q.2 hq)).val)]

theorem symmetric_rest_unit_differential_eval (m t : ℝ) (q : MassiveMomentum) (hq : q.2 ≠ 0) :
    symmetricRestUnitDifferential m t q hq =
      !![2 * (q.1 + t / 2), -2 * ‖q.2‖; 2 * (q.1 - t / 2), -2 * ‖q.2‖] := by
  have h (v : ℝ) := (shiftedD_hasFDerivAt m (axialTransfer v) q).fderiv
  simp only [symmetricRestUnitDifferential, h]
  simp [coneCovector_apply, coneAxialUnit, coneSpatialUnit,
    axial_transfer_coordinates, rest_radial_unit_inner, sub_eq_add_neg, mul_add]

theorem symmetric_rest_unit_jacobian (m t : ℝ) (q : MassiveMomentum) (hq : q.2 ≠ 0) :
    (symmetricRestUnitDifferential m t q hq).det = -4 * t * ‖q.2‖ := by
  rw [symmetric_rest_unit_differential_eval, Matrix.det_fin_two]
  change 2 * (q.1 + t / 2) * (-2 * ‖q.2‖) - (-2 * ‖q.2‖) * (2 * (q.1 - t / 2)) = _
  ring

/-- The common shell is everywhere transverse above the sum threshold. -/
theorem symmetric_rest_shell_normals_independent {m t : ℝ} (hm : 0 < m) (ht : 2 * m < |t|)
    (q : MassiveMomentum) (hq : symmetricRestNormals m t q = 0) :
    LinearIndependent ℝ ![fderiv ℝ (shiftedD m (axialTransfer (t / 2))) q,
      fderiv ℝ (shiftedD m (axialTransfer (-(t / 2)))) q] := by
  have ht₀ : t ≠ 0 := abs_pos.mp (by linarith)
  have hr := symmetric_rest_shell_radius_pos hm ht q hq
  let u := restRadialUnit q.2 (norm_ne_zero_iff.mp hr.ne')
  have hax := ((symmetric_rest_shell_intersection m t ht₀ q).mp
    ⟨congrArg Prod.fst hq, congrArg Prod.snd hq⟩).1
  have hd (v : ℝ) := (shiftedD_hasFDerivAt m (axialTransfer v) q).fderiv
  have haxeval (v : ℝ) : fderiv ℝ (shiftedD m (axialTransfer v)) q
      (WithLp.ofLp coneAxialUnit.val) = 2 * v := by
    rw [hd]
    simp [coneCovector_apply, coneAxialUnit, axial_transfer_coordinates, hax]
  have hradeval (v : ℝ) : fderiv ℝ (shiftedD m (axialTransfer v)) q
      (WithLp.ofLp (coneSpatialUnit u).val) = -2 * ‖q.2‖ := by
    rw [hd]
    simp [coneCovector_apply, coneSpatialUnit, axial_transfer_coordinates, u,
      rest_radial_unit_inner]
  apply LinearIndependent.pair_iff.mpr
  intro a b h
  have haxlin := congrArg (fun d : MassiveMomentum →L[ℝ] ℝ =>
    d (WithLp.ofLp coneAxialUnit.val)) h
  have hradlin := congrArg (fun d : MassiveMomentum →L[ℝ] ℝ =>
    d (WithLp.ofLp (coneSpatialUnit u).val)) h
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.zero_apply, smul_eq_mul, haxeval, hradeval] at haxlin hradlin
  have hdiff : (a - b) * t = 0 := by linarith only [haxlin,
    show (a - b) * t = a * (2 * (t / 2)) + b * (2 * -(t / 2)) by ring]
  have hsum : (a + b) * ‖q.2‖ = 0 := by linarith only [hradlin,
    show a * (-2 * ‖q.2‖) + b * (-2 * ‖q.2‖) = -2 * ((a + b) * ‖q.2‖) by ring]
  have h₁ := (mul_eq_zero.mp hdiff).resolve_right ht₀
  have h₂ := (mul_eq_zero.mp hsum).resolve_right hr.ne'
  exact ⟨by linarith, by linarith⟩

theorem symmetric_rest_shell_abs_jacobian {m t : ℝ} (hm : 0 < m) (ht : 2 * m < |t|)
    (q : MassiveMomentum) (hq : symmetricRestNormals m t q = 0) :
    let hrad := symmetric_rest_shell_radius_pos hm ht q hq
    |(symmetricRestUnitDifferential m t q (norm_ne_zero_iff.mp hrad.ne')).det| =
      4 * |t| * Real.sqrt ((t / 2) ^ 2 - m ^ 2) := by
  have ht₀ : t ≠ 0 := abs_pos.mp (by linarith)
  have hs := ((symmetric_rest_shell_intersection m t ht₀ q).mp
    ⟨congrArg Prod.fst hq, congrArg Prod.snd hq⟩).2
  dsimp only
  rw [symmetric_rest_unit_jacobian, abs_mul, abs_mul, abs_norm, ← hs,
    Real.sqrt_sq (norm_nonneg _)]
  norm_num

end UV.SectorPlane
