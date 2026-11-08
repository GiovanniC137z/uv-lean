import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Tactic

/-! Elementary bounds for the actual normalized O--QED kernel.
Source: eq:OQED-normalized-kernel and eq:OQED-linear-exponential-bounds.
These theorems do not assert the subordination or Bessel moment formula. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace UV

def depthProfile (M u : ℝ) : ℝ := Real.sqrt (u + M ^ 2) - M

def kernel (a M u : ℝ) : ℝ := Real.exp (-a * depthProfile M u)

theorem depthProfile_nonneg {M u : ℝ} (hM : 0 ≤ M) (hu : 0 ≤ u) :
    0 ≤ depthProfile M u := by
  have h := Real.sqrt_le_sqrt (show M ^ 2 ≤ u + M ^ 2 by linarith)
  rw [Real.sqrt_sq hM] at h
  exact sub_nonneg.mpr h

theorem depthProfile_le_sqrt {M u : ℝ} (hM : 0 ≤ M) (hu : 0 ≤ u) :
    depthProfile M u ≤ Real.sqrt u := by
  have huM : 0 ≤ u + M ^ 2 := by positivity
  have hs := Real.sq_sqrt hu
  have hsu := Real.sq_sqrt huM
  have hp := mul_nonneg (Real.sqrt_nonneg u) hM
  have hn := Real.sqrt_nonneg (u + M ^ 2)
  have hr := Real.sqrt_nonneg u
  dsimp [depthProfile]
  nlinarith

theorem sqrt_sub_le_depthProfile (M u : ℝ) :
    Real.sqrt u - M ≤ depthProfile M u := by
  exact sub_le_sub_right (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg M])) M

@[simp] theorem kernel_zero {a M : ℝ} (hM : 0 ≤ M) : kernel a M 0 = 1 := by
  simp [kernel, depthProfile, Real.sqrt_sq hM]

theorem kernel_pos (a M u : ℝ) : 0 < kernel a M u := Real.exp_pos _

theorem kernel_le_one {a M u : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M) (hu : 0 ≤ u) :
    kernel a M u ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (depthProfile_nonneg hM hu)

theorem kernel_lower {a M u : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M) (hu : 0 ≤ u) :
    Real.exp (-a * Real.sqrt u) ≤ kernel a M u := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (depthProfile_le_sqrt hM hu) (neg_nonpos.mpr ha)

theorem kernel_upper {a M u : ℝ} (ha : 0 ≤ a) (_hu : 0 ≤ u) :
    kernel a M u ≤ Real.exp (a * M) * Real.exp (-a * Real.sqrt u) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonpos_left (sqrt_sub_le_depthProfile M u)
    (neg_nonpos.mpr ha)
  nlinarith

theorem kernel_antitone_depth {a b M u : ℝ} (hab : a ≤ b)
    (hM : 0 ≤ M) (hu : 0 ≤ u) : kernel b M u ≤ kernel a M u := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg hab) (depthProfile_nonneg hM hu)

/-- The source inverse moment excludes zero. Use an extended-valued integral so
    divergence is not silently assigned the Bochner integral's default zero. -/
def inverseMoment (ρ : Measure ℝ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ τ in Ioi 0, ENNReal.ofReal (τ ^ (-r)) ∂ρ

def laplace (ρ : Measure ℝ) (z : ℝ) : ℝ := ∫ τ, Real.exp (-τ * z) ∂ρ

@[simp] theorem inverseMoment_dirac_zero (r : ℝ) :
    inverseMoment (Measure.dirac 0) r = 0 := by
  rw [inverseMoment, restrict_dirac]
  simp

@[simp] theorem laplace_dirac_zero (z : ℝ) : laplace (Measure.dirac 0) z = 1 := by
  simp [laplace]

/-- Finiteness of the source's inverse moment does not imply absence of an atom. -/
theorem inverseMoment_does_not_exclude_atom (r : ℝ) :
    inverseMoment (Measure.dirac 0) r < ⊤ ∧ (Measure.dirac (0 : ℝ)) {0} ≠ 0 := by
  simp

end UV
