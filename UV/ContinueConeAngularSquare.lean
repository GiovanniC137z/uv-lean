import UV.ContinueConeAngularMoments
import UV.ResumeStableRemainder

/-! The positive-height simple and squared pole averages at the
massless cone, with both values of the prescribed sign. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Set Real
open scoped Interval

private theorem integral_reflection_average {f : ℝ → ℂ} (hf : Continuous f) :
    (∫ θ in (0 : ℝ)..π, f θ) =
      ∫ θ in (0 : ℝ)..π, (f θ + f (π - θ)) / 2 := by
  have hRef : (∫ θ in (0 : ℝ)..π, f (π - θ)) = ∫ θ in (0 : ℝ)..π, f θ := by
    rw [intervalIntegral.integral_comp_sub_left, sub_self, sub_zero]
  have hg : Continuous (fun θ => f (π - θ)) :=
    hf.comp (continuous_const.sub continuous_id)
  simp_rw [div_eq_mul_inv, mul_comm _ ((2 : ℂ)⁻¹)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _), hRef]
  ring

private theorem angular_denominator_ne_zero (u : ℝ) {t η : ℝ} (ht : 0 < t)
    (hη : η ^ 2 = 1) : (u : ℂ) + Complex.I * ((η * t : ℝ) : ℂ) ≠ 0 := by
  intro h
  have hIm := congrArg Complex.im h
  have hProd : η * t = 0 := by simpa [Complex.mul_im] using hIm
  have hη₀ : η ≠ 0 := by intro hz; simp [hz] at hη
  exact (mul_ne_zero hη₀ ht.ne') hProd

private theorem angular_inverse_eq (u : ℝ) {t η : ℝ} (ht : 0 < t) (hη : η ^ 2 = 1) :
    ((u : ℂ) + Complex.I * ((η * t : ℝ) : ℂ))⁻¹ =
      ((u : ℂ) - Complex.I * ((η * t : ℝ) : ℂ)) * (((u ^ 2 + t ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hp : 0 < u ^ 2 + t ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg u) (sq_pos_of_pos ht)
  have hηC : (η : ℂ) ^ 2 = 1 := by exact_mod_cast hη
  have hd : (u : ℂ) + Complex.I * ((η : ℂ) * (t : ℂ)) ≠ 0 := by
    simpa only [Complex.ofReal_mul] using angular_denominator_ne_zero u ht hη
  have hn : (u : ℂ) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hp.ne'
  simp only [Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_mul]
  apply (mul_left_inj' hd).mp
  rw [inv_mul_cancel₀ hd]
  field_simp [hn]
  ring_nf
  rw [Complex.I_sq, hηC]
  ring

private theorem continuous_angular_inverse {t η : ℝ} (ht : 0 < t) (hη : η ^ 2 = 1) :
    Continuous (fun θ : ℝ => ((cos θ : ℂ) + Complex.I * ((η * t : ℝ) : ℂ))⁻¹) :=
  ((Complex.continuous_ofReal.comp continuous_cos).add continuous_const).inv₀
    fun θ => angular_denominator_ne_zero (cos θ) ht hη

/-- Normalized angular resolvent, with the cosine coordinate carrying
the density factor of the four-dimensional cone. -/
theorem cone_angular_resolvent_cos {t η : ℝ} (ht : 0 < t) (hη : η ^ 2 = 1) :
    (∫ θ in (0 : ℝ)..π, ((1 - cos θ) / π : ℝ) •
      ((cos θ : ℂ) + Complex.I * ((η * t : ℝ) : ℂ))⁻¹) =
      ((t : ℂ) - Complex.I * (η : ℂ)) / (sqrt (1 + t ^ 2) : ℂ) - 1 := by
  let f (θ : ℝ) : ℂ := ((1 - cos θ) / π : ℝ) •
    ((cos θ : ℂ) + Complex.I * ((η * t : ℝ) : ℂ))⁻¹
  let q (θ : ℝ) := (cos θ ^ 2 + t ^ 2)⁻¹
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
  have hx (θ : ℝ) : 0 < cos θ ^ 2 + t ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos ht)
  have hq : Continuous q :=
    ((continuous_cos.pow 2).add continuous_const).inv₀ fun θ => (hx θ).ne'
  have hqc : Continuous (fun θ : ℝ => (q θ : ℂ)) := Complex.continuous_ofReal.comp hq
  have hf : Continuous f := ((continuous_const.sub continuous_cos).div_const π).smul
    (continuous_angular_inverse ht hη)
  let C : ℂ := ((t : ℂ) ^ 2 - Complex.I * ((η * t : ℝ) : ℂ)) / (π : ℂ)
  have hpt (θ : ℝ) : (f θ + f (π - θ)) / 2 = C * (q θ : ℂ) - (π : ℂ)⁻¹ := by
    unfold f C q
    rw [cos_pi_sub, angular_inverse_eq (cos θ) ht hη, angular_inverse_eq (-cos θ) ht hη,
      neg_sq]
    simp only [Complex.real_smul]
    have hn : (cos θ : ℂ) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by exact_mod_cast (hx θ).ne'
    simp only [Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_neg]
    field_simp [hpi, hn]
    ring
  change (∫ θ in (0 : ℝ)..π, f θ) = _
  rw [integral_reflection_average hf]
  simp_rw [hpt]
  rw [intervalIntegral.integral_sub ((continuous_const.mul hqc).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_const]
  rw [show (∫ θ in (0 : ℝ)..π, q θ) = π / (t * sqrt (1 + t ^ 2)) from
      cone_angular_first_moment ht]
  unfold C
  simp only [sub_zero, Complex.real_smul]
  push_cast
  have hS : (sqrt (1 + t ^ 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sqrt_pos.mpr (by positivity)).ne'
  field_simp [hpi, Complex.ofReal_ne_zero.mpr ht.ne', hS]

/-- Exact normalized angular mean of the squared literal pole inverse. -/
theorem cone_angular_square_cos {t η : ℝ} (ht : 0 < t) (hη : η ^ 2 = 1) :
    (∫ θ in (0 : ℝ)..π, ((1 - cos θ) / π : ℝ) •
      (((cos θ : ℂ) + Complex.I * ((η * t : ℝ) : ℂ))⁻¹) ^ 2) =
      (Complex.I * (η : ℂ) - (t : ℂ)) / ((sqrt (1 + t ^ 2)) ^ 3 : ℝ) := by
  let f (θ : ℝ) : ℂ := ((1 - cos θ) / π : ℝ) •
    (((cos θ : ℂ) + Complex.I * ((η * t : ℝ) : ℂ))⁻¹) ^ 2
  let q (θ : ℝ) := (cos θ ^ 2 + t ^ 2)⁻¹
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
  have hx (θ : ℝ) : 0 < cos θ ^ 2 + t ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos ht)
  have hq : Continuous q :=
    ((continuous_cos.pow 2).add continuous_const).inv₀ fun θ => (hx θ).ne'
  have hqc : Continuous (fun θ : ℝ => (q θ : ℂ)) := Complex.continuous_ofReal.comp hq
  have hf : Continuous f := ((continuous_const.sub continuous_cos).div_const π).smul
    ((continuous_angular_inverse ht hη).pow 2)
  let C : ℂ := (1 + 2 * Complex.I * ((η * t : ℝ) : ℂ)) / (π : ℂ)
  let B : ℂ := (2 * (t : ℂ) ^ 2 * (1 + Complex.I * ((η * t : ℝ) : ℂ))) / (π : ℂ)
  have hηC : (η : ℂ) ^ 2 = 1 := by exact_mod_cast hη
  have hpt (θ : ℝ) : (f θ + f (π - θ)) / 2 =
      C * (q θ : ℂ) - B * (q θ : ℂ) ^ 2 := by
    unfold f C B q
    rw [cos_pi_sub, angular_inverse_eq (cos θ) ht hη, angular_inverse_eq (-cos θ) ht hη,
      neg_sq]
    simp only [Complex.real_smul]
    have hn : (cos θ : ℂ) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by exact_mod_cast (hx θ).ne'
    simp only [Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_neg]
    field_simp [hpi, hn]
    ring_nf
    rw [Complex.I_sq, hηC]
    ring
  change (∫ θ in (0 : ℝ)..π, f θ) = _
  rw [integral_reflection_average hf]
  simp_rw [hpt]
  rw [intervalIntegral.integral_sub ((continuous_const.mul hqc).intervalIntegrable _ _)
      ((continuous_const.mul (hqc.pow 2)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp_rw [← Complex.ofReal_pow, intervalIntegral.integral_ofReal]
  rw [show (∫ θ in (0 : ℝ)..π, q θ) = π / (t * sqrt (1 + t ^ 2)) from
      cone_angular_first_moment ht,
    show (∫ θ in (0 : ℝ)..π, q θ ^ 2) =
      π * (1 + 2 * t ^ 2) / (2 * t ^ 3 * (sqrt (1 + t ^ 2)) ^ 3) from
      cone_angular_second_moment ht]
  let S := (sqrt (1 + t ^ 2) : ℂ)
  have hS : S ≠ 0 := Complex.ofReal_ne_zero.mpr (sqrt_pos.mpr (by positivity)).ne'
  have hS2 : S ^ 2 = 1 + (t : ℂ) ^ 2 := by
    change (sqrt (1 + t ^ 2) : ℂ) ^ 2 = _
    exact_mod_cast (sq_sqrt (show 0 ≤ 1 + t ^ 2 by positivity))
  unfold C B
  push_cast
  change (1 + 2 * Complex.I * ((η : ℂ) * (t : ℂ))) / (π : ℂ) *
        ((π : ℂ) / ((t : ℂ) * S)) -
      2 * (t : ℂ) ^ 2 * (1 + Complex.I * ((η : ℂ) * (t : ℂ))) / (π : ℂ) *
        ((π : ℂ) * (1 + 2 * (t : ℂ) ^ 2) / (2 * (t : ℂ) ^ 3 * S ^ 3)) = _ / S ^ 3
  field_simp [hpi, Complex.ofReal_ne_zero.mpr ht.ne', hS]
  ring_nf
  rw [hS2]
  ring

end UV.SectorPlane
