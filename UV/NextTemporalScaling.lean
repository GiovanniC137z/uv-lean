import UV.NextTemporalRay

/-! Exact variable changes for the actual two-resolvent temporal coefficient.
Conjugation holds on the full slot matrices and the complete common trace. -/

noncomputable section
open Complex Filter Matrix MeasureTheory Set
open scoped Topology Matrix Matrix.Norms.Elementwise

namespace UV
variable {d : ℕ} {Sector : Type*}

theorem temporal_hermitian_real_smul {H : TemporalMatrix d} (hH : H.IsHermitian) (a : ℝ) :
    ((a : ℂ) • H).IsHermitian := by
  change ((a : ℂ) • H)ᴴ = (a : ℂ) • H
  rw [Matrix.conjTranspose_smul, hH.eq]
  simp

private theorem temporalFrequency_mul (b : Bool) (a u : ℝ) :
    furtherTemporalFrequency b (a * u) = (a : ℂ) * furtherTemporalFrequency b u := by
  cases b <;> simp [furtherTemporalFrequency, temporalCarrierFrequency] <;> ring

theorem temporalResolvent_scale (b : Bool) {H : TemporalMatrix d} (hH : H.IsHermitian)
    {a u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    furtherTemporalResolvent H (furtherTemporalFrequency b (a * u)) =
      ((a⁻¹ : ℝ) : ℂ) • furtherTemporalResolvent (((a⁻¹ : ℝ) : ℂ) • H) (furtherTemporalFrequency b u) := by
  have han : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have he : furtherTemporalPencil H (furtherTemporalFrequency b (a * u)) =
      (a : ℂ) • furtherTemporalPencil (((a⁻¹ : ℝ) : ℂ) • H) (furtherTemporalFrequency b u) := by
    simp [furtherTemporalPencil, temporalFrequency_mul, smul_add, smul_smul, han]
  unfold furtherTemporalResolvent
  rw [he]
  simpa [Units.smul_def, Units.mk0, Complex.ofReal_inv] using Matrix.inv_smul' (furtherTemporalPencil (((a⁻¹ : ℝ) : ℂ) • H) (furtherTemporalFrequency b u))
    (Units.mk0 (a : ℂ) han) ((isUnit_iff_isUnit_det _).mp
    (furtherTemporalPencil_isUnit_of_im_ne_zero (temporal_hermitian_real_smul hH _)
      (furtherTemporalFrequency_im_ne_zero b hu)))

theorem temporalCoefficient_scale (b : Bool) {A B : TemporalMatrix d}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (C Q : TemporalMatrix d)
    {a u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    ((a : ℂ) ^ 2) * furtherTemporalCoefficient A B C Q (furtherTemporalFrequency b (a * u)) =
      furtherTemporalCoefficient (((a⁻¹ : ℝ) : ℂ) • A) (((a⁻¹ : ℝ) : ℂ) • B)
        ((a : ℂ) • C) Q (furtherTemporalFrequency b u) := by
  unfold furtherTemporalCoefficient
  rw [temporalResolvent_scale b hA ha hu, temporalResolvent_scale b hB ha hu]
  have han : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  simp [smul_smul, mul_sub, pow_two, han, mul_assoc]

/-- Exact change of the frequency interval under the source's positive energy
scale. This preserves the ordinary common contact-minus-bubble trace. -/
theorem temporalBand_scale (b : Bool) {A B : TemporalMatrix d}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (C Q : TemporalMatrix d)
    {a : ℝ} (ha : 0 < a) :
    furtherTemporalBand b ⟨((a⁻¹ : ℝ) : ℂ) • A, temporal_hermitian_real_smul hA _⟩
      ⟨((a⁻¹ : ℝ) : ℂ) • B, temporal_hermitian_real_smul hB _⟩ ((a : ℂ) • C) Q =
      a * ∫ ω in Icc a (2 * a), ‖furtherTemporalCoefficient A B C Q (furtherTemporalFrequency b ω)‖ := by
  let f := fun ω => ‖furtherTemporalCoefficient A B C Q (furtherTemporalFrequency b ω)‖
  have hs : (∫ u in Icc (1 : ℝ) 2, f (a * u)) = a⁻¹ * ∫ ω in Icc a (2 * a), f ω := by
    have he := intervalIntegral.integral_comp_mul_left (a := 1) (b := 2) f ha.ne'
    rw [mul_one] at he
    rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2),
      intervalIntegral.integral_of_le (show a ≤ a * 2 by nlinarith),
      ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc, smul_eq_mul] at he
    simpa only [mul_comm a 2] using he
  calc
    _ = ∫ u in Icc (1 : ℝ) 2, a ^ 2 * f (a * u) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro u hu
      change ‖furtherTemporalCoefficient (((a⁻¹ : ℝ) : ℂ) • A) (((a⁻¹ : ℝ) : ℂ) • B)
        ((a : ℂ) • C) Q (furtherTemporalFrequency b u)‖ = a ^ 2 * f (a * u)
      rw [← temporalCoefficient_scale b hA hB C Q ha (zero_lt_one.trans_le hu.1), norm_mul,
        norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    _ = _ := by
      rw [integral_const_mul, hs, ← mul_assoc, pow_two, mul_assoc a a a⁻¹, mul_inv_cancel₀ ha.ne', mul_one]

end UV
