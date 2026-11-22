import UV.ContinueConeAngularSquare
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! The change from the polar angle to the real shell invariant on
the Euclidean unit sphere, including the normalized density. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Set Real
open scoped Interval

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem cone_cos_image : cos '' Ioo 0 π = Ioo (-1 : ℝ) 1 := by
  ext u
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    have ha := cos_lt_cos_of_nonneg_of_le_pi hθ.1.le le_rfl hθ.2
    have hb := cos_lt_cos_of_nonneg_of_le_pi le_rfl hθ.2.le hθ.1
    exact ⟨by simpa only [cos_pi] using ha, by simpa only [cos_zero] using hb⟩
  · intro hu
    refine ⟨arccos u, ⟨arccos_pos.mpr hu.2, ?_⟩, cos_arccos hu.1.le hu.2.le⟩
    simpa only [arccos_neg_one] using arccos_lt_arccos (x := -1) (y := u)
      (le_refl (-1 : ℝ)) hu.1 hu.2.le

/-- The normalized pushforward of the polar test to the variable
U = 2ω₀² − 1. The endpoint values may be assigned arbitrarily. -/
theorem cone_angular_density_integral (f : ℝ → F) :
    (∫ θ in (0 : ℝ)..π, ((1 - cos θ) / π : ℝ) • f (cos θ)) =
      ∫ u in Ioo (-1 : ℝ) 1, ((1 - u) / (π * sqrt (1 - u ^ 2))) • f u := by
  have hInj : InjOn cos (Ioo (0 : ℝ) π) := injOn_cos.mono Ioo_subset_Icc_self
  have hC := integral_image_eq_integral_abs_deriv_smul (s := Ioo (0 : ℝ) π)
    (f := cos) (f' := fun θ => -sin θ) measurableSet_Ioo
    (fun θ _ => (hasDerivAt_cos θ).hasDerivWithinAt) hInj
    (fun u => ((1 - u) / (π * sqrt (1 - u ^ 2))) • f u)
  rw [cone_cos_image] at hC
  rw [intervalIntegral.integral_of_le pi_pos.le, integral_Ioc_eq_integral_Ioo, hC]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hs := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  rw [abs_neg, abs_of_pos hs, ← sin_sq, sqrt_sq hs.le, smul_smul]
  congr 1
  field_simp [pi_ne_zero, hs.ne']


theorem cone_angular_density_mass_one :
    (∫ u in Ioo (-1 : ℝ) 1, (1 - u) / (π * sqrt (1 - u ^ 2))) = 1 := by
  have h := cone_angular_density_integral (fun _ : ℝ => (1 : ℝ))
  simp only [smul_eq_mul, mul_one] at h
  rw [← h, intervalIntegral.integral_div, intervalIntegral.integral_sub
    (continuous_const.intervalIntegrable _ _) (continuous_cos.intervalIntegrable _ _),
    intervalIntegral.integral_const, integral_cos]
  simp [pi_ne_zero]


/-- The full polar angle on the axial-positive-radius half-plane induces
the weighted cosine chart. Squared sine is its two-sphere area factor. -/
theorem cone_polar_angular_integral {f : ℝ → F} (hf : Continuous f) :
    (∫ θ in Ioo (0 : ℝ) π, sin θ ^ 2 • f (cos θ ^ 2 - sin θ ^ 2)) =
      (π / 2) • ∫ θ in (0 : ℝ)..π, ((1 - cos θ) / π : ℝ) • f (cos θ) := by
  let g (θ : ℝ) := sin θ ^ 2 • f (cos θ ^ 2 - sin θ ^ 2)
  let H (θ : ℝ) := ((1 - cos θ) / π : ℝ) • f (cos θ)
  have hg : Continuous g := (continuous_sin.pow 2).smul
    (hf.comp ((continuous_cos.pow 2).sub (continuous_sin.pow 2)))
  have hRight : (∫ θ in (π / 2)..π, g θ) = ∫ θ in (0 : ℝ)..(π / 2), g θ := by
    have h : (∫ θ in (0 : ℝ)..(π / 2), g (π - θ)) = ∫ θ in (π / 2)..π, g θ := by
      rw [intervalIntegral.integral_comp_sub_left, sub_zero, sub_half]
    rw [← h]
    simp only [g, sin_pi_sub, cos_pi_sub, neg_sq]
  have hPoint (θ : ℝ) : g θ = (π / 2) • H (2 * θ) := by
    unfold g H
    have hCos : cos θ ^ 2 - sin θ ^ 2 = 2 * cos θ ^ 2 - 1 := by
      linarith only [sin_sq_add_cos_sq θ]
    rw [cos_two_mul, smul_smul, hCos]
    congr 1
    field_simp [pi_ne_zero]
    nlinarith only [sin_sq_add_cos_sq θ]
  change (∫ θ in Ioo (0 : ℝ) π, g θ) = _
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le pi_pos.le]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable 0 (π / 2)) (hg.intervalIntegrable (π / 2) π), hRight]
  simp_rw [hPoint, intervalIntegral.integral_smul, intervalIntegral.integral_comp_mul_left H
    (c := 2) (by norm_num)]
  have hπ : 2 * (π / 2) = π := by ring
  rw [mul_zero, hπ, smul_smul, ← add_smul]
  congr 1
  ring

/-- The manuscript's literal reciprocal-square density integral. -/
theorem cone_angular_square_density {t η : ℝ} (ht : 0 < t) (hη : η ^ 2 = 1) :
    (∫ u in Ioo (-1 : ℝ) 1, ((1 - u) / (π * sqrt (1 - u ^ 2))) •
      (((u : ℂ) + Complex.I * ((η * t : ℝ) : ℂ))⁻¹) ^ 2) =
      (Complex.I * (η : ℂ) - (t : ℂ)) / ((sqrt (1 + t ^ 2)) ^ 3 : ℝ) := by
  rw [← cone_angular_density_integral]
  exact cone_angular_square_cos ht hη

end UV.SectorPlane
