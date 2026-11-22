import UV.ResumeOpticalResolution
import Mathlib.Analysis.Analytic.Basic

/-! The alternative optical implication from a supplied physical
Hermitian-analytic jump. The two external rim coefficients are distinct
from the two character calculations of a directed graph. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E]
variable {N : Type*} {X : N → Type*} [∀ n, MeasurableSpace (X n)]

/-- Sum the squared extracted coefficients over the admitted positive
phase-space measures on the fixed plane. -/
def Plane.physicalCoefficientCutWeight (diamond : Plane E)
    (phaseMeasure : Plane E → ∀ n, Measure (X n))
    (amplitudes : Plane E → ∀ n, X n → ℂ) : ℝ≥0∞ :=
  ∑' n, ∫⁻ x, ENNReal.ofReal (‖amplitudes diamond n x‖ ^ 2) ∂phaseMeasure diamond n

/-- When Hermitian analyticity and the normalized factorization of the
physical jump are established on the external cut, the optical relation
follows with the exact factor two and the complete positive channel sum. -/
theorem Plane.physical_optical_matched_coefficient (diamond : Plane E)
    (phaseMeasure : Plane E → ∀ n, Measure (X n))
    (amplitudes : Plane E → ∀ n, X n → ℂ)
    (upper lower : Plane E → ℂ)
    (hfinite : diamond.physicalCoefficientCutWeight phaseMeasure amplitudes ≠ ∞)
    (hHermitian : lower diamond = star (upper diamond))
    (hmatched : upper diamond - lower diamond =
      Complex.I * ((diamond.physicalCoefficientCutWeight phaseMeasure amplitudes).toReal : ℂ)) :
    2 * (upper diamond).im = (diamond.physicalCoefficientCutWeight phaseMeasure amplitudes).toReal ∧
      ENNReal.ofReal (2 * (upper diamond).im) =
        diamond.physicalCoefficientCutWeight phaseMeasure amplitudes := by
  have h := congrArg Complex.im hmatched
  have hLower : (lower diamond).im = -(upper diamond).im := by
    rw [hHermitian]
    exact Complex.conj_im _
  simp only [Complex.sub_im, hLower, sub_neg_eq_add, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add] at h
  have hvalue : 2 * (upper diamond).im =
      (diamond.physicalCoefficientCutWeight phaseMeasure amplitudes).toReal := by
    simpa only [two_mul] using h
  exact ⟨hvalue, (congrArg ENNReal.ofReal hvalue).trans (ENNReal.ofReal_toReal hfinite)⟩

/-- The same imaginary entire constant on both rims leaves the jump
unchanged. Its contribution to the twice-imaginary forward coefficient
is exactly twice the constant. -/
theorem optical_imaginary_entire_shift (upper lower : ℂ) (c : ℝ) :
    (∀ z : ℂ, AnalyticAt ℂ (fun _ : ℂ => Complex.I * (c : ℂ)) z) ∧
    ((upper + Complex.I * (c : ℂ)) - (lower + Complex.I * (c : ℂ)) = upper - lower) ∧
    2 * (upper + Complex.I * (c : ℂ)).im = 2 * upper.im + 2 * c := by
  refine ⟨fun _ => analyticAt_const, ?_, ?_⟩
  · ring
  · simp [Complex.mul_im]
    ring

end UV.SectorPlane
