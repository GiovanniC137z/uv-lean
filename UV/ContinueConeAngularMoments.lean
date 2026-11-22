import UV.ResumeConeSquareRadial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! The two real moments of the angular resolvent on the cone sphere. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Set Filter Real
open scoped Interval Topology

private theorem integral_quarter_reciprocal {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (∫ θ in (0 : ℝ)..(π / 4), (A ^ 2 * cos θ ^ 2 + B ^ 2 * sin θ ^ 2)⁻¹) =
      arctan (B / A) / (A * B) := by
  have hI (θ : ℝ) (hθ : θ ∈ uIcc 0 (π / 4)) : cos θ ≠ 0 := by
    rw [uIcc_of_le (by positivity)] at hθ
    exact (cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, pi_pos], by linarith [hθ.2, pi_pos]⟩).ne'
  have hd (θ : ℝ) (hθ : θ ∈ uIcc 0 (π / 4)) :
      HasDerivAt (fun θ => arctan (B / A * tan θ) / (A * B))
        (A ^ 2 * cos θ ^ 2 + B ^ 2 * sin θ ^ 2)⁻¹ θ := by
    have H := (((hasDerivAt_arctan (B / A * tan θ)).comp θ
      ((hasDerivAt_tan (hI θ hθ)).const_mul (B / A))).div_const (A * B))
    convert H using 1
    rw [tan_eq_sin_div_cos]
    have hpos : 0 < A ^ 2 * cos θ ^ 2 + B ^ 2 * sin θ ^ 2 :=
      add_pos_of_pos_of_nonneg (mul_pos (sq_pos_of_pos hA) (sq_pos_of_ne_zero (hI θ hθ)))
        (by positivity)
    field_simp [hI θ hθ, hA.ne', hB.ne', hpos.ne']
  have hc : ContinuousOn (fun θ => (A ^ 2 * cos θ ^ 2 + B ^ 2 * sin θ ^ 2)⁻¹)
      (uIcc 0 (π / 4)) := by
    apply ((continuous_const.mul (continuous_cos.pow 2)).add
      (continuous_const.mul (continuous_sin.pow 2))).continuousOn.inv₀
    intro θ hθ
    have hp : 0 < A ^ 2 * cos θ ^ 2 + B ^ 2 * sin θ ^ 2 :=
      add_pos_of_pos_of_nonneg (mul_pos (sq_pos_of_pos hA) (sq_pos_of_ne_zero (hI θ hθ)))
        (by positivity)
    exact hp.ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]
  simp [tan_pi_div_four]

private theorem integral_cos_reciprocal_half {t : ℝ} (ht : 0 < t) :
    (∫ θ in (0 : ℝ)..(π / 2), (cos θ ^ 2 + t ^ 2)⁻¹) =
      π / (2 * (t * sqrt (1 + t ^ 2))) := by
  let A := sqrt (1 + t ^ 2)
  have hA : 0 < A := sqrt_pos.mpr (by positivity)
  have hA2 : A ^ 2 = 1 + t ^ 2 := sq_sqrt (by positivity)
  let f (θ : ℝ) := (cos θ ^ 2 + t ^ 2)⁻¹
  have hc : Continuous f := by
    exact ((continuous_cos.pow 2).add continuous_const).inv₀ fun θ =>
      (add_pos_of_nonneg_of_pos (sq_nonneg (cos θ)) (sq_pos_of_pos ht)).ne'
  have hf (θ : ℝ) : f θ = (A ^ 2 * cos θ ^ 2 + t ^ 2 * sin θ ^ 2)⁻¹ := by
    unfold f
    rw [hA2]
    congr 1
    nlinarith only [congrArg (fun x : ℝ => t ^ 2 * x) (sin_sq_add_cos_sq θ)]
  have hf' (θ : ℝ) : f (π / 2 - θ) = (t ^ 2 * cos θ ^ 2 + A ^ 2 * sin θ ^ 2)⁻¹ := by
    rw [hf, cos_pi_div_two_sub, sin_pi_div_two_sub, add_comm]
  have hRight : (∫ θ in (π / 4)..(π / 2), f θ) =
      ∫ θ in (0 : ℝ)..(π / 4), f (π / 2 - θ) := by
    rw [intervalIntegral.integral_comp_sub_left, sub_zero, show π / 2 - π / 4 = π / 4 by ring]
  change (∫ θ in (0 : ℝ)..(π / 2), f θ) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 (π / 4)) (hc.intervalIntegrable (π / 4) (π / 2)), hRight]
  simp_rw [hf', hf]
  have hInv : A / t = (t / A)⁻¹ := by simp [div_eq_mul_inv, mul_comm]
  rw [integral_quarter_reciprocal hA ht, integral_quarter_reciprocal ht hA, hInv]
  rw [arctan_inv_of_pos (div_pos ht hA)]
  change arctan (t / A) / (A * t) + (π / 2 - arctan (t / A)) / (t * A) =
    π / (2 * (t * A))
  rw [mul_comm A t, ← add_div]
  ring

theorem cone_angular_first_moment {t : ℝ} (ht : 0 < t) :
    (∫ θ in (0 : ℝ)..π, (cos θ ^ 2 + t ^ 2)⁻¹) =
      π / (t * sqrt (1 + t ^ 2)) := by
  let f (θ : ℝ) := (cos θ ^ 2 + t ^ 2)⁻¹
  have hc : Continuous f := by
    exact ((continuous_cos.pow 2).add continuous_const).inv₀ fun θ =>
      (add_pos_of_nonneg_of_pos (sq_nonneg (cos θ)) (sq_pos_of_pos ht)).ne'
  have hRight : (∫ θ in (π / 2)..π, f θ) = ∫ θ in (0 : ℝ)..(π / 2), f θ := by
    rw [← show (∫ θ in (0 : ℝ)..(π / 2), f (π - θ)) = ∫ θ in (π / 2)..π, f θ by
      rw [intervalIntegral.integral_comp_sub_left, sub_zero, sub_half]
    ]
    simp only [f, cos_pi_sub, neg_sq]
  change (∫ θ in (0 : ℝ)..π, f θ) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 (π / 2)) (hc.intervalIntegrable (π / 2) π), hRight]
  dsimp [f]
  rw [integral_cos_reciprocal_half ht]
  ring


theorem cone_angular_second_moment {t : ℝ} (ht : 0 < t) :
    (∫ θ in (0 : ℝ)..π, ((cos θ ^ 2 + t ^ 2)⁻¹) ^ 2) =
      π * (1 + 2 * t ^ 2) / (2 * t ^ 3 * (sqrt (1 + t ^ 2)) ^ 3) := by
  let f (θ : ℝ) := (cos θ ^ 2 + t ^ 2)⁻¹
  have hp (θ : ℝ) : 0 < cos θ ^ 2 + t ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg (cos θ)) (sq_pos_of_pos ht)
  have hc : Continuous f :=
    ((continuous_cos.pow 2).add continuous_const).inv₀ fun θ => (hp θ).ne'
  let g (θ : ℝ) := sin θ * cos θ / (cos θ ^ 2 + t ^ 2)
  have hderiv (θ : ℝ) : HasDerivAt g
      ((1 + 2 * t ^ 2) * f θ - (2 * t ^ 2 * (1 + t ^ 2)) * f θ ^ 2) θ := by
    have H := ((hasDerivAt_sin θ).mul (hasDerivAt_cos θ)).div
      (((hasDerivAt_cos θ).pow 2).add_const (t ^ 2)) (hp θ).ne'
    convert H using 1
    simp only [f, Pi.mul_apply, Pi.pow_apply, Nat.reduceSubDiff, pow_one, Nat.cast_ofNat]
    field_simp [(hp θ).ne']
    linear_combination (cos θ ^ 2 + t ^ 2 - 2 * cos θ ^ 2) * (sin_sq_add_cos_sq θ)
  have hcont : Continuous (fun θ => (1 + 2 * t ^ 2) * f θ -
      (2 * t ^ 2 * (1 + t ^ 2)) * f θ ^ 2) :=
    (continuous_const.mul hc).sub (continuous_const.mul (hc.pow 2))
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => hderiv θ) (hcont.intervalIntegrable 0 π)
  rw [intervalIntegral.integral_sub ((continuous_const.mul hc).intervalIntegrable 0 π)
    ((continuous_const.mul (hc.pow 2)).intervalIntegrable 0 π),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at H
  have hgZero : g π - g 0 = 0 := by simp [g]
  rw [hgZero] at H
  have hM : (∫ θ in (0 : ℝ)..π, f θ) = π / (t * sqrt (1 + t ^ 2)) :=
    cone_angular_first_moment ht
  rw [hM] at H
  have hA : 0 < sqrt (1 + t ^ 2) := sqrt_pos.mpr (by positivity)
  have hA2 : (sqrt (1 + t ^ 2)) ^ 2 = 1 + t ^ 2 := sq_sqrt (by positivity)
  change (∫ θ in (0 : ℝ)..π, f θ ^ 2) = _
  apply (mul_right_inj' (show 2 * t ^ 2 * (1 + t ^ 2) ≠ 0 by positivity)).mp
  have hEq : 2 * t ^ 2 * (1 + t ^ 2) * (∫ θ in (0 : ℝ)..π, f θ ^ 2) =
      (1 + 2 * t ^ 2) * (π / (t * sqrt (1 + t ^ 2))) := by linarith only [H]
  rw [hEq]
  calc
    _ = 2 * t ^ 2 * (sqrt (1 + t ^ 2)) ^ 2 *
          (π * (1 + 2 * t ^ 2) / (2 * t ^ 3 * (sqrt (1 + t ^ 2)) ^ 3)) := by
            field_simp [ht.ne', hA.ne']
    _ = _ := by rw [hA2]

end UV.SectorPlane
