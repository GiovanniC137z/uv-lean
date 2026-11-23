import UV.ContinueRestThresholdRoots

/-! Separation of the two near poles and the compensating three-dimensional
radial weight at the degenerate equal-mass rest threshold. -/

noncomputable section

namespace UV.SectorPlane

open Complex

variable {E : Type*} [NormedAddCommGroup E]

theorem Plane.rest_threshold_root_im_ne_zero (diamond : Plane E) (ε : Evolution)
    (h : Height) {m : ℝ} (hm : 0 < m) (r : ℝ) :
    (diamond.restThresholdRoot ε h m r).im ≠ 0 := by
  have hη : diamond.eta ε ≠ 0 := by
    intro he
    have hs := diamond.eta_sq ε
    simp [he] at hs
  rw [diamond.rest_threshold_root_im ε h hm r]
  exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hη h.property.ne'))
    (mul_ne_zero (by norm_num) (diamond.rest_threshold_root_re_pos ε h hm r).ne')

theorem Plane.rest_threshold_root_re_strict (diamond : Plane E) (ε : Evolution)
    (h : Height) {m : ℝ} (hm : 0 < m) (r : ℝ) :
    Real.sqrt (m ^ 2 + r ^ 2) < (diamond.restThresholdRoot ε h m r).re := by
  have hh := congrArg Complex.re (diamond.rest_threshold_root_sq ε h m r)
  rw [pow_two, Complex.mul_re] at hh
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero] at hh
  have hi := sq_pos_of_ne_zero (diamond.rest_threshold_root_im_ne_zero ε h hm r)
  apply (Real.sqrt_lt (by positivity) (diamond.rest_threshold_root_re_pos ε h hm r).le).2
  nlinarith only [hh, hi]

theorem rest_threshold_mass_le_radius_root {m : ℝ} (hm : 0 < m) (r : ℝ) :
    m ≤ Real.sqrt (m ^ 2 + r ^ 2) := by
  apply (Real.le_sqrt hm.le (by positivity)).2
  linarith only [sq_nonneg r]

theorem Plane.rest_threshold_near_separation_re (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) (m r : ℝ) :
    2 * (Real.sqrt (m ^ 2 + r ^ 2) - m) ≤
      (diamond.restThresholdNearPlus ε₁ h m r - diamond.restThresholdNearMinus ε₂ h m r).re := by
  simp only [Plane.restThresholdNearPlus, Plane.restThresholdNearMinus, Complex.sub_re,
    Complex.ofReal_re]
  linarith only [diamond.rest_threshold_root_re_lower ε₁ h m r,
    diamond.rest_threshold_root_re_lower ε₂ h m r]

theorem Plane.rest_threshold_near_separation_re_pos (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) {m : ℝ} (hm : 0 < m) (r : ℝ) :
    0 < (diamond.restThresholdNearPlus ε₁ h m r - diamond.restThresholdNearMinus ε₂ h m r).re := by
  simp only [Plane.restThresholdNearPlus, Plane.restThresholdNearMinus, Complex.sub_re,
    Complex.ofReal_re]
  linarith only [diamond.rest_threshold_root_re_strict ε₁ h hm r,
    diamond.rest_threshold_root_re_strict ε₂ h hm r, rest_threshold_mass_le_radius_root hm r]

theorem Plane.rest_threshold_near_separation_ne_zero (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) {m : ℝ} (hm : 0 < m) (r : ℝ) :
    diamond.restThresholdNearPlus ε₁ h m r - diamond.restThresholdNearMinus ε₂ h m r ≠ 0 := by
  intro hz
  have hp := diamond.rest_threshold_near_separation_re_pos ε₁ ε₂ h hm r
  simp [hz] at hp

theorem Plane.rest_threshold_radial_separation (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) {m : ℝ} (hm : 0 < m) (r : ℝ) :
    r ^ 2 * ‖(diamond.restThresholdNearPlus ε₁ h m r -
      diamond.restThresholdNearMinus ε₂ h m r)⁻¹‖ ≤
      (Real.sqrt (m ^ 2 + r ^ 2) + m) / 2 := by
  set R := Real.sqrt (m ^ 2 + r ^ 2)
  let d := diamond.restThresholdNearPlus ε₁ h m r - diamond.restThresholdNearMinus ε₂ h m r
  have hd : 0 < ‖d‖ := norm_pos_iff.mpr (diamond.rest_threshold_near_separation_ne_zero ε₁ ε₂ h hm r)
  have hR : 0 ≤ (R + m) / 2 := by positivity
  have hs : R ^ 2 = m ^ 2 + r ^ 2 := Real.sq_sqrt (by positivity)
  have he : 2 * (R - m) ≤ ‖d‖ :=
    (diamond.rest_threshold_near_separation_re ε₁ ε₂ h m r).trans (Complex.re_le_norm _)
  change r ^ 2 * ‖d⁻¹‖ ≤ _
  rw [norm_inv, ← div_eq_mul_inv]
  apply (div_le_iff₀ hd).2
  calc
    r ^ 2 = (R + m) / 2 * (2 * (R - m)) := by nlinarith only [hs]
    _ ≤ (R + m) / 2 * ‖d‖ := mul_le_mul_of_nonneg_left he hR

theorem Plane.rest_threshold_remote_plus_norm_lower (diamond : Plane E) (ε : Evolution)
    (h : Height) {m x : ℝ} (hm : 0 < m) (hx : |x| ≤ m / 2) (r : ℝ) :
    3 * m / 2 ≤ ‖(x : ℂ) + (m : ℂ) + diamond.restThresholdRoot ε h m r‖ := by
  apply le_trans _ (Complex.re_le_norm _)
  simp only [Complex.add_re, Complex.ofReal_re]
  linarith only [(abs_le.mp hx).1, diamond.rest_threshold_root_re_lower ε h m r,
    rest_threshold_mass_le_radius_root hm r]

theorem Plane.rest_threshold_remote_minus_norm_lower (diamond : Plane E) (ε : Evolution)
    (h : Height) {m x : ℝ} (hm : 0 < m) (hx : |x| ≤ m / 2) (r : ℝ) :
    3 * m / 2 ≤ ‖(x : ℂ) - (m : ℂ) - diamond.restThresholdRoot ε h m r‖ := by
  apply le_trans _ ((neg_le_abs _).trans (Complex.abs_re_le_norm _))
  simp only [Complex.sub_re, Complex.ofReal_re]
  linarith only [(abs_le.mp hx).2, diamond.rest_threshold_root_re_lower ε h m r,
    rest_threshold_mass_le_radius_root hm r]

theorem Plane.rest_threshold_product_axial_partial_fractions (diamond : Plane E)
    (ε₁ ε₂ : Evolution) (h : Height) {m : ℝ} (hm : 0 < m) (x r : ℝ) :
    let a := diamond.restThresholdNearPlus ε₁ h m r
    let b := diamond.restThresholdNearMinus ε₂ h m r
    let A := (x : ℂ) + (m : ℂ) + diamond.restThresholdRoot ε₁ h m r
    let B := (x : ℂ) - (m : ℂ) - diamond.restThresholdRoot ε₂ h m r
    (diamond.shiftedShellCoefficient ε₁ h (restAxialRadialNormals m (2 * m) (x, r)).1)⁻¹ *
      (diamond.shiftedShellCoefficient ε₂ h (restAxialRadialNormals m (2 * m) (x, r)).2)⁻¹ =
      (A * B)⁻¹ * (a - b)⁻¹ * (((x : ℂ) - a)⁻¹ - ((x : ℂ) - b)⁻¹) := by
  dsimp only
  rw [diamond.rest_threshold_near_plus_factor ε₁ h m (x, r),
    diamond.rest_threshold_near_minus_factor ε₂ h m (x, r)]
  let a := diamond.restThresholdNearPlus ε₁ h m r
  let b := diamond.restThresholdNearMinus ε₂ h m r
  let A := (x : ℂ) + (m : ℂ) + diamond.restThresholdRoot ε₁ h m r
  let B := (x : ℂ) - (m : ℂ) - diamond.restThresholdRoot ε₂ h m r
  have hd : a - b ≠ 0 := diamond.rest_threshold_near_separation_ne_zero ε₁ ε₂ h hm r
  have ha : (x : ℂ) - a ≠ 0 := fun hz => by
    have hi := congrArg Complex.im hz
    simp only [a, Plane.restThresholdNearPlus, Complex.sub_im, Complex.ofReal_im,
      sub_zero, zero_sub, Complex.zero_im, neg_eq_zero] at hi
    exact diamond.rest_threshold_root_im_ne_zero ε₁ h hm r hi
  have hb : (x : ℂ) - b ≠ 0 := fun hz => by
    have hi := congrArg Complex.im hz
    simp only [b, Plane.restThresholdNearMinus, Complex.sub_im, Complex.ofReal_im,
      zero_sub, neg_neg, Complex.zero_im] at hi
    exact diamond.rest_threshold_root_im_ne_zero ε₂ h hm r hi
  change (((x : ℂ) - a) * A)⁻¹ * (((x : ℂ) - b) * B)⁻¹ = _
  rw [inv_sub_inv ha hb, show (↑x : ℂ) - b - (↑x - a) = a - b by ring]
  simp only [div_eq_mul_inv, mul_inv]
  calc
    _ = A⁻¹ * B⁻¹ * ((a - b)⁻¹ * (a - b)) * (((x : ℂ) - a)⁻¹ * ((x : ℂ) - b)⁻¹) := by
      rw [inv_mul_cancel₀ hd, mul_one]
      ring
    _ = _ := by ring

end UV.SectorPlane
