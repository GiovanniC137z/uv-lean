import UV.ContinueRestThresholdScalar

/-! Positive unequal masses at the sum threshold in one sector plane.
The translated rest chart puts the common shell at zero radius and
keeps the original symmetric transfer and normalized axial unit. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology UV.SectorPlane

variable {E : Type*} [NormedAddCommGroup E]

/-- Recenter the symmetric routing at its actual threshold point. -/
def thresholdRestCenter (m₁ m₂ : ℝ) : MassiveMomentum :=
  axialTransfer ((m₁ - m₂) / 2)

theorem threshold_rest_translate_plus (m₁ m₂ : ℝ) (q : MassiveMomentum) :
    q + thresholdRestCenter m₁ m₂ + axialTransfer ((m₁ + m₂) / 2) = q + axialTransfer m₁ := by
  apply Prod.ext
  · simp [thresholdRestCenter, axial_transfer_coordinates, Prod.fst_add]
    ring
  · simp [thresholdRestCenter, axial_transfer_coordinates, Prod.snd_add]

theorem threshold_rest_translate_minus (m₁ m₂ : ℝ) (q : MassiveMomentum) :
    q + thresholdRestCenter m₁ m₂ + axialTransfer (-((m₁ + m₂) / 2)) = q + axialTransfer (-m₂) := by
  apply Prod.ext
  · simp [thresholdRestCenter, axial_transfer_coordinates, Prod.fst_add]
    ring
  · simp [thresholdRestCenter, axial_transfer_coordinates, Prod.snd_add]

theorem symmetric_unequal_threshold_intersection {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (q : MassiveMomentum) :
    (shiftedD m₁ (axialTransfer ((m₁ + m₂) / 2)) q = 0 ∧
      shiftedD m₂ (axialTransfer (-((m₁ + m₂) / 2))) q = 0) ↔ q = thresholdRestCenter m₁ m₂ := by
  rw [symmetric_rest_shell_coordinates m₁ m₂ _ (by positivity)]
  have hx : (m₁ ^ 2 - m₂ ^ 2) / (2 * (m₁ + m₂)) = (m₁ - m₂) / 2 := by
    field_simp [show m₁ + m₂ ≠ 0 by positivity]
    ring
  rw [hx, thresholdRestCenter, axial_transfer_coordinates]
  simp only [sub_self, zero_mul, zero_div, pow_eq_zero_iff (by norm_num : 2 ≠ 0), norm_eq_zero]
  exact ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

/-- Each running direction on the threshold strip is the normalized
positive or negative ray of the same fixed carrier unit. -/
theorem Plane.unequal_threshold_running_units [NormedSpace ℝ E] (diamond : Plane E)
    {m₁ m₂ x : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hx : |x| ≤ min m₁ m₂ / 2) :
    let h₁ := (threshold_axial_signs hm₁ (hx.trans (by gcongr; exact min_le_left _ _))).1.ne'
    let h₂ := (threshold_axial_signs hm₂ (hx.trans (by gcongr; exact min_le_right _ _))).2.ne
    (diamond.runningUnit (x + m₁) h₁ : E) = (diamond.poleUnit : E) ∧
      (diamond.runningUnit (x - m₂) h₂ : E) = -(diamond.poleUnit : E) := by
  have h₁ : |x| ≤ m₁ / 2 := hx.trans (by linarith [min_le_left m₁ m₂])
  have h₂ : |x| ≤ m₂ / 2 := hx.trans (by linarith [min_le_right m₁ m₂])
  exact ⟨(diamond.rest_threshold_running_units hm₁ h₁).1, (diamond.rest_threshold_running_units hm₂ h₂).2⟩

def Plane.unequalThresholdNearGap (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) (m₁ m₂ r : ℝ) : ℂ :=
  diamond.restThresholdNearPlus ε₁ h m₁ r - diamond.restThresholdNearMinus ε₂ h m₂ r

theorem Plane.unequal_threshold_gap_re_pos (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (r : ℝ) :
    0 < (diamond.unequalThresholdNearGap ε₁ ε₂ h m₁ m₂ r).re := by
  simp only [Plane.unequalThresholdNearGap, Plane.restThresholdNearPlus, Plane.restThresholdNearMinus,
    Complex.sub_re, Complex.ofReal_re]
  linarith only [diamond.rest_threshold_root_re_strict ε₁ h hm₁ r,
    diamond.rest_threshold_root_re_strict ε₂ h hm₂ r, rest_threshold_mass_le_radius_root hm₁ r,
    rest_threshold_mass_le_radius_root hm₂ r]

theorem Plane.unequal_threshold_gap_ne_zero (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (r : ℝ) :
    diamond.unequalThresholdNearGap ε₁ ε₂ h m₁ m₂ r ≠ 0 := by
  intro hz
  have hp := diamond.unequal_threshold_gap_re_pos ε₁ ε₂ h hm₁ hm₂ r
  simp [hz] at hp

/-- The compensated radial coefficient for the unequal-mass chart. -/
def Plane.unequalThresholdRadialCoefficient (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) (m₁ m₂ r : ℝ) : ℂ :=
  (↑(r ^ 2) : ℂ) / diamond.unequalThresholdNearGap ε₁ ε₂ h m₁ m₂ r

/-- The exact limiting radial weight and a uniform norm bound. -/
def unequalThresholdRadialWeight (m₁ m₂ r : ℝ) : ℝ :=
  let A := Real.sqrt (m₁ ^ 2 + r ^ 2) + m₁
  let B := Real.sqrt (m₂ ^ 2 + r ^ 2) + m₂
  A * B / (A + B)

private theorem unequal_threshold_weight_pos {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (r : ℝ) :
    0 < unequalThresholdRadialWeight m₁ m₂ r := by
  unfold unequalThresholdRadialWeight
  positivity

private theorem threshold_single_radius_identity {m : ℝ} (hm : 0 < m) (r : ℝ) :
    Real.sqrt (m ^ 2 + r ^ 2) - m = r ^ 2 / (Real.sqrt (m ^ 2 + r ^ 2) + m) := by
  apply (eq_div_iff (by positivity)).mpr
  nlinarith only [Real.sq_sqrt (show 0 ≤ m ^ 2 + r ^ 2 by positivity)]

private theorem unequal_threshold_weight_identity {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (r : ℝ) :
    r ^ 2 = unequalThresholdRadialWeight m₁ m₂ r *
      ((Real.sqrt (m₁ ^ 2 + r ^ 2) - m₁) + (Real.sqrt (m₂ ^ 2 + r ^ 2) - m₂)) := by
  rw [threshold_single_radius_identity hm₁ r, threshold_single_radius_identity hm₂ r]
  unfold unequalThresholdRadialWeight
  field_simp
  ring

theorem Plane.unequal_threshold_radial_coefficient_bound (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (r : ℝ) :
    ‖diamond.unequalThresholdRadialCoefficient ε₁ ε₂ h m₁ m₂ r‖ ≤ unequalThresholdRadialWeight m₁ m₂ r := by
  let d := diamond.unequalThresholdNearGap ε₁ ε₂ h m₁ m₂ r
  have hd : 0 < ‖d‖ := norm_pos_iff.mpr (diamond.unequal_threshold_gap_ne_zero ε₁ ε₂ h hm₁ hm₂ r)
  have hre : (Real.sqrt (m₁ ^ 2 + r ^ 2) - m₁) + (Real.sqrt (m₂ ^ 2 + r ^ 2) - m₂) ≤ d.re := by
    simp only [d, Plane.unequalThresholdNearGap, Plane.restThresholdNearPlus, Plane.restThresholdNearMinus,
      Complex.sub_re, Complex.ofReal_re]
    linarith only [diamond.rest_threshold_root_re_lower ε₁ h m₁ r, diamond.rest_threshold_root_re_lower ε₂ h m₂ r]
  rw [Plane.unequalThresholdRadialCoefficient, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (sq_nonneg r)]
  apply (div_le_iff₀ hd).mpr
  exact (unequal_threshold_weight_identity hm₁ hm₂ r).trans_le
    (mul_le_mul_of_nonneg_left (hre.trans (Complex.re_le_norm d)) (unequal_threshold_weight_pos hm₁ hm₂ r).le)

theorem Plane.unequal_threshold_radial_coefficient_tendsto (diamond : Plane E) (ε₁ ε₂ : Evolution)
    {m₁ m₂ r : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hr : r ≠ 0) :
    Tendsto (fun h => diamond.unequalThresholdRadialCoefficient ε₁ ε₂ h m₁ m₂ r)
      poleBoundaryHeights (𝓝 (↑(unequalThresholdRadialWeight m₁ m₂ r) : ℂ)) := by
  have hF : poleBoundaryHeights ≤ Filter.comap Subtype.val (𝓝 (0 : ℝ)) :=
    Filter.comap_mono nhdsWithin_le_nhds
  have h₁ := (diamond.rest_threshold_root_tendsto ε₁ hm₁ r).mono_left hF
  have h₂ := (diamond.rest_threshold_root_tendsto ε₂ hm₂ r).mono_left hF
  let S := (Real.sqrt (m₁ ^ 2 + r ^ 2) - m₁) + (Real.sqrt (m₂ ^ 2 + r ^ 2) - m₂)
  have hS : 0 < S := by
    dsimp only [S]
    rw [threshold_single_radius_identity hm₁ r, threshold_single_radius_identity hm₂ r]
    exact add_pos (div_pos (sq_pos_of_ne_zero hr) (by positivity))
      (div_pos (sq_pos_of_ne_zero hr) (by positivity))
  have hd : Tendsto (fun h => diamond.unequalThresholdNearGap ε₁ ε₂ h m₁ m₂ r)
      poleBoundaryHeights (𝓝 (S : ℂ)) := by
    convert (h₁.sub_const (m₁ : ℂ)).sub (h₂.const_sub (m₂ : ℂ)) using 2
    dsimp [S]
    push_cast
    ring
  have H := (show Tendsto (fun _ : Height => (↑(r ^ 2) : ℂ)) poleBoundaryHeights
    (𝓝 (↑(r ^ 2) : ℂ)) from tendsto_const_nhds).div hd (Complex.ofReal_ne_zero.mpr hS.ne')
  convert H using 1
  rw [← Complex.ofReal_div]
  apply congrArg (fun x : ℝ => 𝓝 (x : ℂ))
  exact ((div_eq_iff hS.ne').mpr (unequal_threshold_weight_identity hm₁ hm₂ r)).symm

theorem unequal_threshold_radial_weight_continuous {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    Continuous (unequalThresholdRadialWeight m₁ m₂) := by
  let A (r : ℝ) := Real.sqrt (m₁ ^ 2 + r ^ 2) + m₁
  let B (r : ℝ) := Real.sqrt (m₂ ^ 2 + r ^ 2) + m₂
  have hA : Continuous A := by unfold A; fun_prop
  have hB : Continuous B := by unfold B; fun_prop
  exact (hA.mul hB).div (hA.add hB) (fun r => by dsimp [A, B]; positivity)

theorem unequal_threshold_radial_weight_integrable {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (R : ℝ) :
    IntegrableOn (unequalThresholdRadialWeight m₁ m₂) (Icc 0 R) :=
  (unequal_threshold_radial_weight_continuous hm₁ hm₂).continuousOn.integrableOn_compact isCompact_Icc

end UV.SectorPlane
