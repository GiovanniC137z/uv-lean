import UV.ExtendNativeHolonomyResponse
import UV.Subordination
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-! Exact normal-circle heat trace and its proper-time winding integrals. -/

noncomputable section
open MeasureTheory Set

namespace UV.ExtendNativeHolonomy

variable {E : Type} [NormedAddCommGroup E]

def shiftedNormalHeatTerm (C : NormalCircle E) (s θ : ℝ) (n : ℤ) : ℝ :=
  Real.exp (-(s * ((2 * Real.pi * n + θ) / C.length) ^ 2))

def windingNormalHeatTerm (C : NormalCircle E) (s θ : ℝ) (w : ℤ) : ℂ :=
  Complex.exp ((↑(-(w : ℝ) ^ 2 * C.length ^ 2 / (4 * s) : ℝ) : ℂ) +
    (↑((w : ℝ) * θ) : ℂ) * Complex.I)

/-- Exact shifted Poisson identity, including its winding phase and the
normal-circle trace normalization. -/
theorem normal_heatTrace_poisson (C : NormalCircle E) {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    (↑(∑' n : ℤ, shiftedNormalHeatTerm C s θ n) : ℂ) =
      (↑(C.length / Real.sqrt (4 * Real.pi * s)) : ℂ) *
        ∑' w : ℤ, windingNormalHeatTerm C s θ w := by
  let a : ℝ := C.length ^ 2 / (4 * Real.pi * s)
  let z : ℝ := θ / (2 * Real.pi)
  let b : ℂ := (↑z : ℂ) * Complex.I
  have hA : 0 < 4 * Real.pi * s := mul_pos (mul_pos (by norm_num) Real.pi_pos) hs
  have hL := C.length_pos
  have ha : 0 < a := div_pos (sq_pos_of_pos hL) hA
  have hAst := Complex.tsum_exp_neg_quadratic (a := (a : ℂ))
    (by simpa only [Complex.ofReal_re] using ha) b
  have hleft (w : ℤ) :
      Complex.exp (-↑Real.pi * (a : ℂ) * (w : ℂ) ^ 2 + 2 * ↑Real.pi * b * (w : ℂ)) =
        windingNormalHeatTerm C s θ w := by
    unfold windingNormalHeatTerm
    congr 1
    simp only [a, b, z, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_intCast, Complex.ofReal_neg]
    push_cast
    have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    have hπ' : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  have hI : Complex.I * b = -(z : ℂ) := by
    dsimp [b]
    rw [show Complex.I * ((z : ℂ) * Complex.I) = (z : ℂ) * Complex.I ^ 2 by ring,
      Complex.I_sq]
    ring
  have hright (n : ℤ) :
      Complex.exp (-↑Real.pi / (a : ℂ) * ((n : ℂ) + Complex.I * b) ^ 2) =
        ↑(shiftedNormalHeatTerm C s θ (-n)) := by
    rw [hI]
    unfold shiftedNormalHeatTerm
    rw [Complex.ofReal_exp]
    congr 1
    simp only [a, z, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_intCast, Complex.ofReal_neg, Int.cast_neg, Complex.ofReal_add]
    push_cast
    have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    have hπ' : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hL' : (C.length : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
    field_simp
    ring
  simp_rw [hleft, hright] at hAst
  have hpref :
      1 / (a : ℂ) ^ (1 / 2 : ℂ) = ↑(Real.sqrt (4 * Real.pi * s) / C.length) := by
    rw [← Complex.ofReal_ofNat (n := 2), ← Complex.ofReal_one, ← Complex.ofReal_div,
      ← Complex.ofReal_cpow ha.le, ← Real.sqrt_eq_rpow]
    change 1 / (↑(Real.sqrt a) : ℂ) = _
    rw [← Complex.ofReal_one, ← Complex.ofReal_div]
    congr 1
    dsimp [a]
    rw [Real.sqrt_div (sq_nonneg C.length), Real.sqrt_sq hL.le]
    field_simp
  rw [hpref, ← Complex.ofReal_tsum] at hAst
  have hneg := (Equiv.neg ℤ).tsum_eq (shiftedNormalHeatTerm C s θ)
  change (∑' n : ℤ, shiftedNormalHeatTerm C s θ (-n)) =
    (∑' n : ℤ, shiftedNormalHeatTerm C s θ n) at hneg
  rw [hneg] at hAst
  rw [hAst, ← mul_assoc, ← Complex.ofReal_mul]
  have hsqrt : Real.sqrt (4 * Real.pi * s) ≠ 0 := (Real.sqrt_pos.mpr hA).ne'
  rw [show C.length / Real.sqrt (4 * Real.pi * s) *
      (Real.sqrt (4 * Real.pi * s) / C.length) = 1 by field_simp,
    Complex.ofReal_one, one_mul]

def properWindingKernel (A ω s : ℝ) : ℝ :=
  s ^ (-(3 : ℝ) / 2) * Real.exp (-(ω ^ 2 * s) - A ^ 2 / (4 * s))

/-- Exact proper-time integral of a nonzero winding with the source
(A=wL>0). It is the same checked square-root subordination under a
positive rescaling of proper time. -/
theorem winding_proper_integral {A ω : ℝ} (hA : 0 < A) (hω : 0 ≤ ω) :
    (∫ s in Ioi (0 : ℝ), properWindingKernel A ω s) =
      2 * Real.sqrt Real.pi * Real.exp (-(A * ω)) / A := by
  have hAA : 0 < A ^ 2 := sq_pos_of_pos hA
  have hs := integral_comp_mul_left_Ioi (properWindingKernel A ω) 0 hAA
  simp only [mul_zero, smul_eq_mul] at hs
  have he : (∫ t in Ioi (0 : ℝ), properWindingKernel A ω (A ^ 2 * t)) =
      (A ^ 3)⁻¹ * ∫ t in Ioi (0 : ℝ), UV.oqedDensityCore (A * ω) t := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht₀ := mem_Ioi.mp ht
    unfold properWindingKernel UV.oqedDensityCore
    dsimp only
    have hpow : (A ^ 2 : ℝ) ^ (-(3 : ℝ) / 2) = (A ^ 3)⁻¹ := by
      rw [← Real.rpow_natCast_mul hA.le]
      norm_num only [Nat.cast_ofNat]
      rw [Real.rpow_neg hA.le]
      norm_num
    rw [Real.mul_rpow hAA.le ht₀.le, hpow]
    have hexp : -(ω ^ 2 * (A ^ 2 * t)) - A ^ 2 / (4 * (A ^ 2 * t)) =
        -((A * ω) ^ 2 * t) - 1 / (4 * t) := by
      field_simp [hA.ne', ht₀.ne']
    rw [hexp]
    ring
  rw [he, UV.oqedDensityCore_integral (mul_nonneg hA.le hω)] at hs
  calc
    _ = A ^ 2 * ((A ^ 2)⁻¹ * ∫ s in Ioi (0 : ℝ), properWindingKernel A ω s) := by
      rw [← mul_assoc, mul_inv_cancel₀ hAA.ne', one_mul]
    _ = _ := by rw [← hs]; field_simp

end UV.ExtendNativeHolonomy
