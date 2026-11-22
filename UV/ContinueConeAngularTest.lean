import UV.ContinueConeAngularLaw
import UV.ContinueCarrierConeBounds

/-! Uniform test bound for the simple pole in the normalized cone
coordinate. Subtract the test's value at the regular angular shell. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Set Real
open scoped Interval NNReal

private theorem cone_angular_weight_integral :
    (∫ θ in (0 : ℝ)..π, coneAngularWeight θ) = 1 := by
  have h := cone_angular_density_integral (fun _ : ℝ => (1 : ℝ))
  simpa only [smul_eq_mul, mul_one, coneAngularWeight, cone_angular_density_mass_one] using h

theorem cone_angular_test_norm_le {g : ℝ → ℂ} {L : ℝ≥0} (hg : LipschitzWith L g)
    {η t : ℝ} (hη : η ^ 2 = 1) (ht : 0 < t) :
    ‖∫ θ in (0 : ℝ)..π, coneAngularWeight θ • (g (cos θ) * coneAngularPole η t θ)‖ ≤
      2 * ‖g 0‖ + L := by
  let P := coneAngularPole η t
  let w := coneAngularWeight
  let D (θ : ℝ) := w θ • ((g (cos θ) - g 0) * P θ)
  have hP : Continuous P := coneAngularPole_continuous ht hη
  have hw : Continuous w := (continuous_const.sub continuous_cos).div_const π
  have hD : Continuous D := hw.smul (((hg.continuous.comp continuous_cos).sub continuous_const).mul hP)
  have hwP : Continuous (fun θ => w θ • P θ) := hw.smul hP
  have hw₀ (θ : ℝ) : 0 ≤ w θ := div_nonneg (sub_nonneg.mpr (cos_le_one θ)) pi_pos.le
  have hBound (θ : ℝ) : ‖D θ‖ ≤ (L : ℝ) * w θ := by
    let z : ℂ := (cos θ : ℂ) + Complex.I * ((η * t : ℝ) : ℂ)
    have hRe : z.re = cos θ := by simp [z, Complex.mul_re, -Complex.ofReal_cos]
    have hZ : z ≠ 0 := by
      intro hz
      have hzIm : η * t = 0 := by simpa [z, Complex.mul_im, -Complex.ofReal_cos] using congrArg Complex.im hz
      have hη₀ : η ≠ 0 := by intro h; simp [h] at hη
      exact (mul_ne_zero hη₀ ht.ne') hzIm
    have hCos : |cos θ| ≤ ‖z‖ := hRe ▸ Complex.abs_re_le_norm z
    have hAbs : |cos θ| * ‖P θ‖ ≤ 1 := by
      change |cos θ| * ‖z⁻¹‖ ≤ 1
      rw [norm_inv, ← div_eq_mul_inv, div_le_one (norm_pos_iff.mpr hZ)]
      exact hCos
    have hLip : ‖g (cos θ) - g 0‖ ≤ (L : ℝ) * |cos θ| := by
      simpa only [Real.norm_eq_abs, sub_zero, Real.dist_eq] using hg.norm_sub_le (cos θ) 0
    unfold D
    rw [norm_smul, norm_mul, Real.norm_of_nonneg (hw₀ θ), mul_comm (L : ℝ)]
    apply mul_le_mul_of_nonneg_left _ (hw₀ θ)
    calc
      _ ≤ ((L : ℝ) * |cos θ|) * ‖P θ‖ := mul_le_mul_of_nonneg_right hLip (norm_nonneg _)
      _ ≤ (L : ℝ) := by
        rw [mul_assoc]
        exact mul_le_of_le_one_right L.coe_nonneg hAbs
  have hDI : ‖∫ θ in (0 : ℝ)..π, D θ‖ ≤ (L : ℝ) := by
    calc
      _ ≤ ∫ θ in (0 : ℝ)..π, ‖D θ‖ := intervalIntegral.norm_integral_le_integral_norm pi_pos.le
      _ ≤ ∫ θ in (0 : ℝ)..π, (L : ℝ) * w θ :=
        intervalIntegral.integral_mono pi_pos.le (hD.norm.intervalIntegrable _ _)
          ((continuous_const.mul hw).intervalIntegrable _ _) hBound
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, cone_angular_weight_integral, mul_one]
  have hSplit (θ : ℝ) : w θ • (g (cos θ) * P θ) = g 0 * (w θ • P θ) + D θ := by
    simp only [D, Complex.real_smul]
    ring
  change ‖∫ θ in (0 : ℝ)..π, w θ • (g (cos θ) * P θ)‖ ≤ _
  simp_rw [hSplit]
  rw [intervalIntegral.integral_add ((continuous_const.mul hwP).intervalIntegrable _ _)
    (hD.intervalIntegrable _ _), intervalIntegral.integral_const_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ hDI)
  change ‖g 0 * coneAngularFirst η t‖ ≤ _
  rw [norm_mul, coneAngularFirst_eq_closed ht hη, mul_comm 2]
  exact mul_le_mul_of_nonneg_left (coneFirstClosed_norm_le hη t) (norm_nonneg _)

/-- The simple pole carries the integrable radial majorant r once the
normalized angular test has a uniform Lipschitz bound. -/
theorem cone_angular_simple_radial_norm_le {g : ℝ → ℂ} {L : ℝ≥0} (hg : LipschitzWith L g)
    {η h r : ℝ} (hη : η ^ 2 = 1) (hh : 0 < h) (hr : 0 < r) :
    ‖(r : ℂ) * (∫ θ in (0 : ℝ)..π, coneAngularWeight θ •
      (g (cos θ) * coneAngularPole η (h / r ^ 2) θ))‖ ≤ r * (2 * ‖g 0‖ + L) := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
  exact mul_le_mul_of_nonneg_left
    (cone_angular_test_norm_le hg hη (div_pos hh (sq_pos_of_pos hr))) hr.le

end UV.SectorPlane
