import UV.RevisionLegacyStableTail
import Mathlib.Analysis.Calculus.Taylor

noncomputable section

open MeasureTheory Real Set
namespace UV

def stableCosRemainder (t : ℝ) : ℝ :=
  Real.cos t - 1 + t ^ 2 / 2 - t ^ 4 / 24

private theorem stable_cos_remainder_bound (t : ℝ) :
    |stableCosRemainder t| ≤ |t| ^ 6 / 120 := by
  by_cases ht : t = 0
  · simp [ht, stableCosRemainder]
  have hp : 0 < |t| := abs_pos.mpr ht
  have h0 : (0 : ℝ) ∈ Icc 0 |t| := ⟨le_rfl, hp.le⟩
  have h : ‖Real.cos |t| - taylorWithinEval Real.cos 5 (Icc 0 |t|) 0 |t|‖ ≤
      (1 : ℝ) * (|t| - 0)^6 / (120 : ℝ) :=
    taylor_mean_remainder_bound (n := 5) hp.le Real.contDiff_cos.contDiffOn
      ⟨hp.le, le_rfl⟩ (fun y hy => by
        rw [Real.iteratedDerivWithin_cos_Icc 6 hp hy, Real.norm_eq_abs]
        exact Real.abs_iteratedDeriv_cos_le_one 6 y)
  have hEval : taylorWithinEval Real.cos 5 (Icc 0 |t|) 0 |t| =
      1 - |t| ^ 2 / 2 + |t| ^ 4 / 24 := by
    rw [taylor_within_apply]
    simp_rw [Real.iteratedDerivWithin_cos_Icc _ hp h0]
    rw [show (5 : ℕ) + 1 = 6 by decide]
    norm_num [Finset.sum_range_succ,
      show iteratedDeriv 2 Real.cos = -Real.cos by simp,
      show iteratedDeriv 3 Real.cos = Real.sin by simpa using Real.iteratedDeriv_odd_cos 1,
      show iteratedDeriv 4 Real.cos = Real.cos by simp,
      show iteratedDeriv 5 Real.cos = -Real.sin by ext x; simp]
    ring
  rw [hEval, Real.norm_eq_abs, Real.cos_abs, sq_abs, show |t| ^ 4 = t ^ 4 by
    calc |t| ^ 4 = (|t| ^ 2) ^ 2 := by ring
      _ = t ^ 4 := by rw [sq_abs]; ring] at h
  simpa only [one_mul, sub_zero, stableCosRemainder, show
    Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24) = Real.cos t - 1 + t ^ 2 / 2 - t ^ 4 / 24 by ring] using h

private theorem stableCovarianceTailSquare_measurable (a m : ℝ) :
    Measurable (stableCovarianceTailSquare a m) := by
  unfold stableCovarianceTailSquare
  exact Measurable.piecewise (s := {x : ScalarMomentum | m⁻¹ < ‖x‖})
    (measurableSet_lt measurable_const continuous_norm.measurable) (by fun_prop) measurable_const

/-- After subtracting the literal square tail, the cosine integral beyond
its fourth-order Taylor terms has an explicit sixth-order error. -/
theorem revised_stable_residual_cosine_error {a m : ℝ} (ha : 0 < a) (hm : 0 < m) (h : ℝ) :
    let S := fun x : ScalarMomentum => stableCoordinateCovariance a m x ^ 2 -
      stableCovarianceTailSquare a m x
    |∫ x : ScalarMomentum, stableCosRemainder (h * x 0) * S x| ≤
      (|h| ^ 6 / 120) * ∫ x : ScalarMomentum, ‖x‖ ^ 6 * |S x| := by
  intro S
  have hmom : Integrable (fun x : ScalarMomentum => ‖x‖ ^ 6 * |S x|) := by
    have hmom := (revised_stable_square_tail_residual_sixth_moment ha hm).abs
    apply hmom.congr
    filter_upwards with x
    rw [abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg x) 6)]
  have hS : Measurable S :=
    ((stableCoordinateCovariance_continuous ha hm).measurable.pow_const 2).sub
      (stableCovarianceTailSquare_measurable a m)
  have hP : Continuous stableCosRemainder := by unfold stableCosRemainder; fun_prop
  have hf : Measurable (fun x : ScalarMomentum => stableCosRemainder (h * x 0) * S x) :=
    (hP.measurable.comp (measurable_const.mul
      (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0).measurable)).mul hS
  have hbound (x : ScalarMomentum) : |stableCosRemainder (h * x 0) * S x| ≤
      (|h| ^ 6 / 120) * (‖x‖ ^ 6 * |S x|) := by
    have hn : |x 0| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
    rw [abs_mul]
    calc
      _ ≤ (|h * x 0| ^ 6 / 120) * |S x| :=
        mul_le_mul_of_nonneg_right (stable_cos_remainder_bound _) (abs_nonneg _)
      _ ≤ ((|h| * ‖x‖) ^ 6 / 120) * |S x| := by
        rw [abs_mul]
        gcongr
      _ = _ := by rw [mul_pow]; ring
  have hmaj := hmom.const_mul (|h| ^ 6 / 120)
  have hi := hmaj.mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbound x)
  refine abs_integral_le_integral_abs.trans ?_
  rw [← integral_const_mul]
  exact integral_mono hi.abs hmaj hbound

end UV
