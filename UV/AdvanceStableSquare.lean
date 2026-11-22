import UV.ContinueStableMassiveRemainder
import Mathlib.Analysis.Calculus.Taylor

/-! The exact finite-height branch expansion of the stable-half
multiplier on the massless squared inverse. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology Interval

/-- The exponential remainder on the closed left half-plane is
bounded along the full line segment from zero to its argument. -/
theorem exp_quadratic_remainder_norm_le_of_re_nonpos {x : ℂ} (hx : x.re ≤ 0) :
    ‖Complex.exp x - 1 - x - x ^ 2 / 2‖ ≤ ‖x‖ ^ 3 / 2 := by
  let f (t : ℝ) := Complex.exp ((t : ℂ) * x)
  have hf : ContDiff ℝ 3 f := (Complex.ofRealCLM.contDiff.mul contDiff_const).cexp
  have hd (t : ℝ) : HasDerivAt f (f t * x) t :=
    by simpa [f] using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const x).cexp
  have he (n : ℕ) : iteratedDeriv n f = fun t => f t * x ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      rw [((hd t).mul_const (x ^ n)).deriv, pow_succ]
      ring
  have hW {n : ℕ} (hn : n ≤ 3) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      iteratedDerivWithin n f (Icc 0 1) t = f t * x ^ n := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      (hf.of_le (by exact_mod_cast hn)).contDiffAt ht, he]
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖iteratedDerivWithin 3 f (Icc 0 1) t‖ ≤ ‖x‖ ^ 3 := by
    rw [hW le_rfl ht, norm_mul, norm_pow]
    apply mul_le_of_le_one_left (by positivity)
    rw [show f t = Complex.exp ((t : ℂ) * x) from rfl,
      Complex.norm_exp, Real.exp_le_one_iff]
    simpa [Complex.mul_re] using mul_nonpos_of_nonneg_of_nonpos ht.1 hx
  have H := taylor_mean_remainder_bound (n := 2) (x := (1 : ℝ))
    zero_le_one hf.contDiffOn (right_mem_Icc.mpr zero_le_one) hbound
  have h₀ : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.mpr zero_le_one
  have hT : taylorWithinEval f 2 (Icc 0 1) 0 1 = 1 + x + x ^ 2 / 2 := by
    rw [taylor_within_apply]
    norm_num [Finset.sum_range_succ, hW (by decide : 0 ≤ 3) h₀,
      hW (by decide : 1 ≤ 3) h₀, hW (by decide : 2 ≤ 3) h₀, f, Complex.real_smul]
    ring
  rw [hT] at H
  convert H using 1
  · simp only [f, Complex.ofReal_one, one_mul]
    congr 1
    ring
  · norm_num

variable {E : Type*} [NormedAddCommGroup E]

/-- Principal branch at the original shifted invariant of the same
diamond and positive vectorial pole height. -/
def Plane.stableShellRoot (diamond : Plane E) (ε : Evolution) (h : Height) (w : ℝ) : ℂ :=
  principalSqrt (-(diamond.shiftedShellCoefficient ε h w))

theorem Plane.stable_shell_root_sq (diamond : Plane E) (ε : Evolution) (h : Height) (w : ℝ) :
    (diamond.stableShellRoot ε h w) ^ 2 = -(diamond.shiftedShellCoefficient ε h w) :=
  principalSqrt_sq _

theorem Plane.stable_shell_root_ne_zero (diamond : Plane E) (ε : Evolution) (h : Height) (w : ℝ) :
    diamond.stableShellRoot ε h w ≠ 0 := by
  intro hz
  have hsq := diamond.stable_shell_root_sq ε h w
  simp only [hz, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_eq_neg] at hsq
  exact diamond.massless_shifted_coefficient_nonzero ε h w hsq

/-- The cubic Taylor remainder after dividing by the same shifted
invariant twice. Its boundary singularity is locally integrable. -/
def stableSquareResidualFromRoot (a : ℝ) (s z : ℂ) : ℂ :=
  let x := -(a : ℂ) * s
  (Complex.exp x - 1 - x - x ^ 2 / 2) / z ^ 2

def stableSquareResidual (a : ℝ) (z : ℂ) : ℂ :=
  stableSquareResidualFromRoot a (principalSqrt (-z)) z

theorem stable_square_residual_from_root_norm_le {a : ℝ} (ha : 0 ≤ a) {s z : ℂ}
    (hz : z ≠ 0) (hs : ‖s‖ = Real.sqrt ‖z‖) (hsre : 0 ≤ s.re) :
    ‖stableSquareResidualFromRoot a s z‖ ≤ a ^ 3 / (2 * Real.sqrt ‖z‖) := by
  let x := -(a : ℂ) * s
  let S := Real.sqrt ‖z‖
  have hS : 0 < S := Real.sqrt_pos.mpr (norm_pos_iff.mpr hz)
  have hS2 : S ^ 2 = ‖z‖ := Real.sq_sqrt (norm_nonneg _)
  have hx : x.re ≤ 0 := by
    have H := mul_nonpos_of_nonneg_of_nonpos hsre (neg_nonpos.mpr ha)
    simpa only [x, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, neg_zero, zero_mul, mul_zero, sub_zero, mul_comm] using H
  have hN : ‖x‖ = a * S := by simp [x, S, hs, Complex.norm_real, abs_of_nonneg ha]
  change ‖(Complex.exp x - 1 - x - x ^ 2 / 2) / z ^ 2‖ ≤ _
  rw [norm_div, norm_pow]
  calc
    _ ≤ (‖x‖ ^ 3 / 2) / ‖z‖ ^ 2 :=
      div_le_div_of_nonneg_right (exp_quadratic_remainder_norm_le_of_re_nonpos hx) (by positivity)
    _ = _ := by
      rw [hN]
      change (a * S) ^ 3 / 2 / ‖z‖ ^ 2 = a ^ 3 / (2 * S)
      rw [← hS2]
      field_simp [hS.ne']

theorem stable_square_residual_norm_le {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : z ≠ 0) :
    ‖stableSquareResidual a z‖ ≤ a ^ 3 / (2 * Real.sqrt ‖z‖) :=
  stable_square_residual_from_root_norm_le ha hz
    (by rw [principalSqrt_norm, norm_neg]) (principalSqrt_re_nonneg _)

/-- Exact split into a double pole, the branch term of order −3/2, a
simple pole, and the residual of order at most −1/2. -/
theorem Plane.stable_square_coefficient_split (diamond : Plane E) (ε : Evolution)
    (h : Height) (a w : ℝ) :
    diamond.stableHalfCoefficient ε a w h * (diamond.poleCoefficient ε h w) ^ 2 =
      (diamond.poleCoefficient ε h w) ^ 2 -
        (a : ℂ) / (diamond.stableShellRoot ε h w) ^ 3 -
        ((a : ℂ) ^ 2 / 2) * diamond.poleCoefficient ε h w +
        stableSquareResidual a (diamond.shiftedShellCoefficient ε h w) := by
  let s := diamond.stableShellRoot ε h w
  let z := diamond.shiftedShellCoefficient ε h w
  have hsz : s ^ 2 = -z := diamond.stable_shell_root_sq ε h w
  have hs := diamond.stable_shell_root_ne_zero ε h w
  have hs' : s ≠ 0 := hs
  rw [Plane.stableHalfCoefficient, dif_pos h.property, diamond.stable_half_numerator_characters,
    diamond.pole_coefficient_eq_inv, stableSquareResidual, stableSquareResidualFromRoot]
  change Complex.exp (-(a : ℂ) * s) * z⁻¹ ^ 2 =
    z⁻¹ ^ 2 - (a : ℂ) / s ^ 3 - ((a : ℂ) ^ 2 / 2) * z⁻¹ +
      (Complex.exp (-(a : ℂ) * s) - 1 - (-(a : ℂ) * s) - (-(a : ℂ) * s) ^ 2 / 2) / z ^ 2
  have hz : z = -(s ^ 2) := by rw [hsz, neg_neg]
  rw [hz]
  field_simp [hs']
  ring

theorem Plane.stable_square_coefficient_directed (diamond : Plane E) (ε : Evolution)
    (h : Height) (a w : ℝ) :
    directed (diamond.stableHalfCoefficient ε a w h * (diamond.poleCoefficient ε h w) ^ 2) =
      diamond.stableHalfNumerator ε h a w * (diamond.poleInverse ε h w) ^ 2 := by
  rw [Plane.stableHalfCoefficient, dif_pos h.property, diamond.stable_half_numerator_characters,
    diamond.pole_coefficient_eq_inv, Plane.stableHalfNumerator]
  simp only [pow_two, directed_mul, Plane.shiftedShellCoefficient, diamond.pole_inverse_complex]

theorem Plane.stable_square_residual_inverse_root_bound (diamond : Plane E) (ε : Evolution)
    (h : Height) {a w : ℝ} (ha : 0 ≤ a) (hw : w ≠ 0) :
    ‖stableSquareResidual a (diamond.shiftedShellCoefficient ε h w)‖ ≤
      (a ^ 3 / 2) * inverseRootAbs w := by
  let z := diamond.shiftedShellCoefficient ε h w
  have hz := diamond.massless_shifted_coefficient_nonzero ε h w
  have hwz : |w| ≤ ‖z‖ := by
    simpa only [z, Plane.shiftedShellCoefficient, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero,
      sub_zero, add_zero] using Complex.abs_re_le_norm z
  apply (stable_square_residual_norm_le ha hz).trans
  rw [inverseRootAbs, div_mul_eq_div_div, div_eq_mul_inv (a ^ 3 / 2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact inv_anti₀ (Real.sqrt_pos.mpr (abs_pos.mpr hw)) (Real.sqrt_le_sqrt hwz)

end UV.SectorPlane
