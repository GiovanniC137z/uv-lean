import UV.Kernel
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Principal complex square roots and the literal O--QED scalar covariance.
These are branch, holomorphy and norm estimates used in the momentum tube. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace UV

def principalSqrt (z : ℂ) : ℂ := z ^ (2⁻¹ : ℂ)

theorem principalSqrt_re (z : ℂ) :
    (principalSqrt z).re = Real.sqrt ((‖z‖ + z.re) / 2) :=
  Complex.cpow_inv_two_re z

theorem principalSqrt_re_nonneg (z : ℂ) : 0 ≤ (principalSqrt z).re := by
  rw [principalSqrt_re]
  exact Real.sqrt_nonneg _

/-- The inequality is valid globally, and in particular on the closed right
half-plane where its left side is the square root of a nonnegative number. -/
theorem principalSqrt_re_lower (z : ℂ) : Real.sqrt z.re ≤ (principalSqrt z).re := by
  rw [principalSqrt_re]
  apply Real.sqrt_le_sqrt
  have h := Complex.re_le_norm z
  linarith

theorem principalSqrt_ofReal {u : ℝ} (hu : 0 ≤ u) :
    principalSqrt (u : ℂ) = (Real.sqrt u : ℂ) := by
  have h := Complex.ofReal_cpow hu (2⁻¹ : ℝ)
  simpa only [principalSqrt, Real.sqrt_eq_rpow, one_div, Complex.ofReal_inv,
    Complex.ofReal_ofNat] using h.symm

theorem principalSqrt_hasDerivAt {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt principalSqrt ((2⁻¹ : ℂ) * z ^ ((2⁻¹ : ℂ) - 1)) z :=
  (Complex.hasStrictDerivAt_cpow_const hz).hasDerivAt

theorem principalSqrt_differentiableAt {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ principalSqrt z :=
  (principalSqrt_hasDerivAt (Complex.mem_slitPlane_iff.mpr (Or.inl hz))).differentiableAt

theorem principalSqrt_analyticOnNhd_rightHalfPlane :
    AnalyticOnNhd ℂ principalSqrt {z : ℂ | 0 < z.re} := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    exact (principalSqrt_differentiableAt hz).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re

@[measurability, fun_prop] theorem principalSqrt_measurable : Measurable principalSqrt := by
  have he : principalSqrt = (fun z : ℂ => if z = 0 then 0 else
      Complex.exp (Complex.log z * (2⁻¹ : ℂ))) := by
    funext z
    unfold principalSqrt
    rw [Complex.cpow_def]
    norm_num
  rw [he]
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    ((Complex.measurable_log.mul_const (2⁻¹ : ℂ)).cexp)

def principalScalarCovariance (a M m : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(a : ℂ) * (principalSqrt (z + ((M ^ 2 : ℝ) : ℂ)) - (M : ℂ))) /
    (z + ((m ^ 2 : ℝ) : ℂ))

@[measurability, fun_prop] theorem principalScalarCovariance_measurable (a M m : ℝ) :
    Measurable (principalScalarCovariance a M m) := by
  unfold principalScalarCovariance
  exact ((((principalSqrt_measurable.comp (measurable_id.add_const ((M ^ 2 : ℝ) : ℂ))).sub_const
    (M : ℂ)).const_mul (-(a : ℂ))).cexp).div
      (measurable_id.add_const ((m ^ 2 : ℝ) : ℂ))

theorem principalScalarCovariance_differentiableAt (a M m : ℝ) {z : ℂ}
    (hz : 0 < (z + ((M ^ 2 : ℝ) : ℂ)).re) (hden : z + ((m ^ 2 : ℝ) : ℂ) ≠ 0) :
    DifferentiableAt ℂ (principalScalarCovariance a M m) z := by
  have hs := (principalSqrt_differentiableAt hz).comp z
    (differentiableAt_id.add_const ((M ^ 2 : ℝ) : ℂ))
  exact (((hs.sub_const (M : ℂ)).const_mul (-(a : ℂ))).cexp).div
    (differentiableAt_id.add_const ((m ^ 2 : ℝ) : ℂ)) hden

theorem principalScalarCovariance_analyticOnNhd (a M m : ℝ) :
    AnalyticOnNhd ℂ (principalScalarCovariance a M m)
      {z : ℂ | 0 < (z + ((M ^ 2 : ℝ) : ℂ)).re ∧ z + ((m ^ 2 : ℝ) : ℂ) ≠ 0} := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    exact (principalScalarCovariance_differentiableAt a M m hz.1 hz.2).differentiableWithinAt
  · exact (isOpen_lt continuous_const
      (Complex.continuous_re.comp (continuous_id.add continuous_const))).inter
        (isOpen_ne_fun (continuous_id.add continuous_const) continuous_const)

theorem principalScalarCovariance_ofReal (a M m : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    principalScalarCovariance a M m (u : ℂ) =
      ((kernel a M u / (u + m ^ 2) : ℝ) : ℂ) := by
  unfold principalScalarCovariance
  rw [← Complex.ofReal_add, principalSqrt_ofReal (show 0 ≤ u + M ^ 2 by positivity)]
  simp only [← Complex.ofReal_sub, ← Complex.ofReal_mul, ← Complex.ofReal_neg,
    ← Complex.ofReal_exp, ← Complex.ofReal_add, ← Complex.ofReal_div]
  rfl

theorem principalScalarCovariance_norm (a M m : ℝ) (z : ℂ) :
    ‖principalScalarCovariance a M m z‖ =
      Real.exp (a * M - a * (principalSqrt (z + ((M ^ 2 : ℝ) : ℂ))).re) /
        ‖z + ((m ^ 2 : ℝ) : ℂ)‖ := by
  unfold principalScalarCovariance
  rw [norm_div, Complex.norm_exp]
  congr 1
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    neg_zero, zero_mul, sub_zero, Complex.sub_re]
  ring

/-- The denominator lower bound is explicit; no analyticity or branch-domain
assumption is needed for this global norm estimate. -/
theorem principalScalarCovariance_norm_bound {a M m lower : ℝ} {z : ℂ}
    (ha : 0 ≤ a) (hlower : 0 < lower) (hden : lower ≤ ‖z + ((m ^ 2 : ℝ) : ℂ)‖) :
    ‖principalScalarCovariance a M m z‖ ≤
      Real.exp (a * M) * Real.exp (-a * Real.sqrt (z + ((M ^ 2 : ℝ) : ℂ)).re) / lower := by
  rw [principalScalarCovariance_norm]
  calc
    _ ≤ Real.exp (a * M - a * (principalSqrt (z + ((M ^ 2 : ℝ) : ℂ))).re) / lower :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le hlower hden
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hlower.le
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hr := mul_le_mul_of_nonneg_left (principalSqrt_re_lower (z + ((M ^ 2 : ℝ) : ℂ))) ha
      linarith

end UV
