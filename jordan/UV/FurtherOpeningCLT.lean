import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

/-! The standardized Poisson law of the critical oscillator channel count.
This module uses the independently pinned companion toolchain. -/

noncomputable section
open MeasureTheory Filter ProbabilityTheory Complex Asymptotics
open scoped Topology NNReal RealInnerProductSpace

namespace UV

def openingCriticalMeasure (M : ℝ) : ProbabilityMeasure ℝ where
  val := ((poissonMeasure M.toNNReal).map (Nat.cast : ℕ → ℝ)).map
    (fun x : ℝ ↦ (x - M) / Real.sqrt M)
  property := Measure.isProbabilityMeasure_map (by fun_prop)

def openingGaussianMeasure : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩

def openingCriticalPhase (t M : ℝ) : ℂ := ((t / Real.sqrt M : ℝ) : ℂ) * I

theorem openingCriticalMeasure_charFun {M : ℝ} (hM : 0 < M) (t : ℝ) :
    charFun (openingCriticalMeasure M) t =
      cexp ((M : ℂ) * (cexp (openingCriticalPhase t M) - 1 - openingCriticalPhase t M)) := by
  let μ := (poissonMeasure M.toNNReal).map (Nat.cast : ℕ → ℝ)
  have hmap : (openingCriticalMeasure M : Measure ℝ) =
      (μ.map (fun x : ℝ ↦ x + (-M))).map (fun x : ℝ ↦ (Real.sqrt M)⁻¹ * x) := by
    change μ.map (fun x : ℝ ↦ (x - M) / Real.sqrt M) = _
    conv_rhs => rw [Measure.map_map (by fun_prop) (by fun_prop)]
    have he : (fun x : ℝ ↦ (x - M) / Real.sqrt M) =
        (fun x : ℝ ↦ (Real.sqrt M)⁻¹ * x) ∘ (fun x : ℝ ↦ x + (-M)) := by
      funext x
      dsimp only [Function.comp_apply]
      ring
    rw [he]
  rw [hmap, charFun_map_mul, charFun_map_add_const, charFun_map_cast_poissonMeasure,
    ← Complex.exp_add, Real.coe_toNNReal M hM.le]
  congr 1
  simp only [openingCriticalPhase, Real.inner_apply, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_inv, Complex.ofReal_div]
  ring

theorem openingCriticalExponent_tendsto (t : ℝ) :
    Tendsto (fun M : ℝ ↦ (M : ℂ) * (cexp (openingCriticalPhase t M) - 1 - openingCriticalPhase t M))
      atTop (𝓝 (-(t : ℂ) ^ 2 / 2)) := by
  by_cases ht : t = 0
  · subst t
    simp [openingCriticalPhase]
  let z := openingCriticalPhase t
  let R (w : ℂ) := cexp w - (1 + w + w ^ 2 / 2)
  have hR : R =o[𝓝 0] (fun w : ℂ ↦ w ^ 2) := by
    have h := Complex.exp_sub_sum_range_succ_isLittleO_pow 2
    convert h using 1
    ext w
    simp [R, Finset.sum_range_succ]
  have hz : Tendsto z atTop (𝓝 0) := by
    have h : Tendsto (fun M : ℝ ↦ t / Real.sqrt M) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
    change Tendsto (fun M ↦ ((t / Real.sqrt M : ℝ) : ℂ) * I) atTop (𝓝 0)
    simpa only [Function.comp_apply, Complex.ofReal_zero, zero_mul] using
      (Complex.continuous_ofReal.continuousAt.tendsto.comp h).mul_const I
  have hsmall : Tendsto (fun M : ℝ ↦ R (z M) / (z M) ^ 2) atTop (𝓝 0) :=
    (hR.comp_tendsto hz).tendsto_div_nhds_zero
  have hT := (hsmall.const_mul (-(t : ℂ) ^ 2)).add_const (-(t : ℂ) ^ 2 / 2)
  simp only [mul_zero, zero_add] at hT
  apply hT.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
  have hs : Real.sqrt M ≠ 0 := (Real.sqrt_pos.mpr hM).ne'
  have hs' : ((Real.sqrt M : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hsq : (((Real.sqrt M : ℝ) : ℂ) ^ 2) = (M : ℂ) := by exact_mod_cast Real.sq_sqrt hM.le
  have hn : z M ≠ 0 := mul_ne_zero (by exact_mod_cast div_ne_zero ht hs) I_ne_zero
  have hzz : (M : ℂ) * z M ^ 2 = -(t : ℂ) ^ 2 := by
    dsimp [z, openingCriticalPhase]
    rw [Complex.ofReal_div, mul_pow, div_pow, I_sq, ← hsq]
    field_simp
  change -(t : ℂ) ^ 2 * (R (z M) / (z M) ^ 2) + -(t : ℂ) ^ 2 / 2 =
    (M : ℂ) * (cexp (z M) - 1 - z M)
  rw [← hzz]
  have he : (M : ℂ) * z M ^ 2 * (R (z M) / (z M) ^ 2) = (M : ℂ) * R (z M) := by
    field_simp
  rw [he]
  dsimp only [R]
  ring

/-- Weak Gaussian convergence for positive real rates tending to infinity. -/
theorem openingCriticalMeasure_tendsto_gaussian :
    Tendsto openingCriticalMeasure atTop (𝓝 openingGaussianMeasure) := by
  apply tendsto_iff_seq_tendsto.mpr
  intro u hu
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  have h := (Complex.continuous_exp.continuousAt.tendsto.comp (openingCriticalExponent_tendsto t)).comp hu
  change Tendsto (fun n : ℕ ↦ cexp ((u n : ℂ) *
    (cexp (openingCriticalPhase t (u n)) - 1 - openingCriticalPhase t (u n)))) atTop
    (𝓝 (cexp (-(t : ℂ) ^ 2 / 2))) at h
  have hg : charFun (openingGaussianMeasure : Measure ℝ) t = cexp (-(t : ℂ) ^ 2 / 2) := by
    simp [openingGaussianMeasure, charFun_gaussianReal, neg_div]
  rw [hg]
  apply h.congr'
  filter_upwards [hu.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
  exact (openingCriticalMeasure_charFun hn t).symm

end UV
