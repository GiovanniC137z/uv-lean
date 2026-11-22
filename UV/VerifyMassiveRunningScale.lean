import UV.ExtendStablePole

/-! Principal square-root scaling connects the literal stable-half
transport to the unscaled kernel `exp(-sqrt z)` in the general
finite-height scalar-line prescription. -/

noncomputable section

namespace UV.SectorPlane

open UV.Carrier

theorem principalSqrt_nonnegative_scale_sq (a : ℝ) (ha : 0 ≤ a) (z : ℂ) :
    principalSqrt (((a ^ 2 : ℝ) : ℂ) * z) = (a : ℂ) * principalSqrt z := by
  have hzero : principalSqrt 0 = 0 := by
    simpa only [Real.sqrt_zero, Complex.ofReal_zero] using
      principalSqrt_ofReal (show 0 ≤ (0 : ℝ) from le_rfl)
  by_cases h₀ : a = 0
  · simp [h₀, hzero]
  by_cases hz : z = 0
  · simp [hz, hzero]
  have hp := sq_pos_of_ne_zero h₀
  have hn : ((a ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have he : principalSqrt (((a ^ 2 : ℝ) : ℂ) * z) =
      principalSqrt ((a ^ 2 : ℝ) : ℂ) * principalSqrt z := by
    unfold principalSqrt
    rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hn hz), Complex.log_ofReal_mul hp hz,
      Complex.ofReal_log hp.le, add_mul, Complex.exp_add, ← Complex.cpow_def_of_ne_zero hn,
      ← Complex.cpow_def_of_ne_zero hz]
  rw [he, principalSqrt_ofReal hp.le, Real.sqrt_sq ha]

variable {E : Type*} [NormedAddCommGroup E]

/-- This equality uses the actual positive height and sector–evolution
sign, for every real shell invariant including the null cone. -/
theorem Plane.stable_half_numerator_scalar_argument (diamond : Plane E) (ε : Evolution)
    (h : Height) {a : ℝ} (ha : 0 ≤ a) (w : ℝ) :
    diamond.stableHalfNumerator ε h a w =
      directed (Complex.exp (-principalSqrt (-(a : ℂ) ^ 2 *
        diamond.shiftedShellCoefficient ε h w))) := by
  have he : -(a : ℂ) ^ 2 * diamond.shiftedShellCoefficient ε h w =
      ((a ^ 2 : ℝ) : ℂ) * -(diamond.shiftedShellCoefficient ε h w) := by
    push_cast
    ring
  rw [he, principalSqrt_nonnegative_scale_sq a ha, Plane.stableHalfNumerator, neg_mul]

end UV.SectorPlane
