import UV.ContinueStableMassivePV

/-! A globally Lipschitz replacement of the running axial sign that
coincides with it near both positive-mass shell sheets. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Set
open scoped NNReal

/-- This interpolation is used only in the shell test. The final pairing
keeps the original axial sign throughout the momentum space. -/
def massiveRunningClip (m t : ℝ) : ℝ := max (-1) (min 1 (t * (m / 2)⁻¹))

def massiveRunningTest (m : ℝ) (f : MassiveMomentum → ℝ) (q : MassiveMomentum) : ℝ :=
  massiveRunningClip m q.1 * f q

def massiveRunningCorrection (m : ℝ) (q : MassiveMomentum) : ℝ :=
  axialSign q.1 - massiveRunningClip m q.1

theorem massive_running_clip_norm_le_one (m t : ℝ) : ‖massiveRunningClip m t‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem massive_running_clip_lipschitz {m : ℝ} (hm : 0 < m) :
    LipschitzWith ((m / 2)⁻¹).toNNReal (massiveRunningClip m) := by
  have hl : LipschitzWith ((m / 2)⁻¹).toNNReal (fun t : ℝ => t * (m / 2)⁻¹) := by
    apply LipschitzWith.of_dist_le_mul
    intro t u
    rw [Real.dist_eq, Real.dist_eq, ← sub_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (m / 2)⁻¹),
      Real.coe_toNNReal _ (by positivity), mul_comm]
  exact (hl.const_min 1).const_max (-1)

theorem massive_running_clip_eq_axial_sign {m t : ℝ} (hm : 0 < m) (ht : m / 2 ≤ |t|) :
    massiveRunningClip m t = axialSign t := by
  have hpos : 0 < m / 2 := by positivity
  by_cases h : 0 < t
  · rw [abs_of_pos h] at ht
    have he : 1 ≤ t * (m / 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]
      exact ht
    rw [massiveRunningClip, min_eq_left he, max_eq_right (by norm_num)]
    simp only [axialSign, if_pos h]
  · rw [abs_of_nonpos (le_of_not_gt h)] at ht
    have hs : t < 0 := by linarith
    have he : t * (m / 2)⁻¹ ≤ -1 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hpos]
      linarith
    rw [massiveRunningClip, min_eq_right (he.trans (by norm_num)), max_eq_left he]
    simp [axialSign, h, hs]

theorem massive_axial_sign_measurable : Measurable axialSign := by
  unfold axialSign
  apply Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const

theorem massive_running_correction_measurable {m : ℝ} (hm : 0 < m) :
    Measurable (massiveRunningCorrection m) :=
  (massive_axial_sign_measurable.comp measurable_fst).sub
    (((massive_running_clip_lipschitz hm).continuous.comp continuous_fst).measurable)

theorem massive_running_axial_sign_norm_le_one (t : ℝ) : ‖axialSign t‖ ≤ 1 := by
  by_cases h : t = 0
  · simp [h, axialSign]
  · rw [Real.norm_eq_abs, axialSign_abs h]

theorem massive_running_correction_norm_le (m : ℝ) (q : MassiveMomentum) :
    ‖massiveRunningCorrection m q‖ ≤ 2 := by
  exact (norm_sub_le _ _).trans
    ((add_le_add (massive_running_axial_sign_norm_le_one q.1)
      (massive_running_clip_norm_le_one m q.1)).trans_eq (by norm_num))

/-- The correction's support has a uniform gap to the massive denominator zero. -/
theorem massive_running_correction_gap {m : ℝ} (hm : 0 < m) {q : MassiveMomentum}
    (hq : massiveRunningCorrection m q ≠ 0) : m ^ 2 / 2 ≤ |massiveD m q| := by
  have h : |q.1| < m / 2 := by
    by_contra! hp
    exact hq (sub_eq_zero.mpr (massive_running_clip_eq_axial_sign hm hp).symm)
  have ht : q.1 ^ 2 ≤ (m / 2) ^ 2 := by
    rw [← sq_abs q.1]
    exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr h.le
  have hD : massiveD m q ≤ -(m ^ 2 / 2) := by
    unfold massiveD shellSquare
    linarith [sq_nonneg ‖q.2‖, sq_nonneg m]
  rw [abs_of_nonpos (hD.trans (neg_nonpos.mpr (by positivity)))]
  linarith

theorem massive_running_test_hasCompactSupport (m : ℝ) {f : MassiveMomentum → ℝ}
    (hs : HasCompactSupport f) : HasCompactSupport (massiveRunningTest m f) :=
  hs.mul_left (f := fun q : MassiveMomentum => massiveRunningClip m q.1)

theorem massive_running_test_lipschitz {m : ℝ} (hm : 0 < m)
    {f : MassiveMomentum → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hs : HasCompactSupport f) :
    ∃ K : ℝ≥0, LipschitzWith K (massiveRunningTest m f) := by
  obtain ⟨C, hC⟩ := hf.continuous.bounded_above_of_compact_support hs
  let B : ℝ≥0 := (max C 0).toNNReal
  let K : ℝ≥0 := ((m / 2)⁻¹).toNNReal
  let g (q : MassiveMomentum) := massiveRunningClip m q.1
  have hg : LipschitzWith K g := by
    simpa only [mul_one] using (massive_running_clip_lipschitz hm).comp LipschitzWith.prod_fst
  have hB (q : MassiveMomentum) : ‖f q‖ ≤ B := by
    rw [show (B : ℝ) = max C 0 from Real.coe_toNNReal _ (le_max_right _ _)]
    exact (hC q).trans (le_max_left _ _)
  refine ⟨L + B * K, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  change dist (g x * f x) (g y * f y) ≤ _
  rw [dist_eq_norm, show g x * f x - g y * f y =
    g x * (f x - f y) + f y * (g x - g y) by ring]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul, NNReal.coe_add, NNReal.coe_mul, add_mul]
  exact add_le_add
    (by simpa only [one_mul] using (mul_le_mul (massive_running_clip_norm_le_one m x.1)
      (hf.norm_sub_le x y) (norm_nonneg _) zero_le_one))
    (by simpa only [mul_assoc] using (mul_le_mul (hB y)
      (hg.norm_sub_le x y) (norm_nonneg _) B.coe_nonneg))

/-- The running numerator retains the two axial shell weights with
opposite signs and does not select a physical sheet. -/
def massiveSignedShellTest (m : ℝ) (f : MassiveMomentum → ℝ) : ℝ :=
  (∫ p : Spatial, f (shellFrequency m p, p) / (2 * shellFrequency m p)) -
    ∫ p : Spatial, f (-shellFrequency m p, p) / (2 * shellFrequency m p)

theorem massive_running_test_fullShellTest {m : ℝ} (hm : 0 < m) (f : MassiveMomentum → ℝ) :
    fullShellTest m (massiveRunningTest m f) = massiveSignedShellTest m f := by
  have hmω (p : Spatial) : m ≤ shellFrequency m p := by
    apply (sq_le_sq₀ hm.le (by unfold shellFrequency; positivity)).mp
    rw [shell_frequency_square]
    nlinarith [sq_nonneg ‖p‖]
  have hpos (p : Spatial) : massiveRunningClip m (shellFrequency m p) = 1 := by
    have h := hm.trans_le (hmω p)
    rw [massive_running_clip_eq_axial_sign hm (by rw [abs_of_pos h]; linarith [hmω p])]
    simp only [axialSign, if_pos h]
  have hneg (p : Spatial) : massiveRunningClip m (-shellFrequency m p) = -1 := by
    have h := hm.trans_le (hmω p)
    have hn : -shellFrequency m p < 0 := neg_lt_zero.mpr h
    rw [massive_running_clip_eq_axial_sign hm (by rw [abs_neg, abs_of_pos h]; linarith [hmω p])]
    simp only [axialSign, if_neg hn.not_gt, if_pos hn]
  unfold fullShellTest massiveSignedShellTest
  simp_rw [massiveRunningTest, hpos, hneg, one_mul, neg_one_mul, neg_div, integral_neg, sub_eq_add_neg]

end UV.SectorPlane
