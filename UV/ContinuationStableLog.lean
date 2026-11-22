import UV.ContinuationStableAxis
import UV.ContinuationStableRemainder

/-! Full nonanalytic term of the literal stable-half bubble at zero momentum. -/

noncomputable section

open Filter Real
open scoped Topology

namespace UV

/-- The actual unit-axis bubble has the stated logarithmic term with a
uniform quantitative order-six remainder for (0<|h|\le m). -/
theorem stableAxisBubble_leading_log_bound {a m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, 0 < |h| → |h| ≤ m →
      |stableAxisBubble a m h - stableAxisBubble a m 0 -
        (iteratedDeriv 2 (stableAxisBubble a m) 0 / 2) * h ^ 2 -
        (iteratedDeriv 4 (stableAxisBubble a m) 0 / 24) * h ^ 4 +
        (a ^ 2 / (8192 * π ^ 2 * m ^ 4)) * h ^ 6 * log (m / |h|)| ≤ K * |h| ^ 6 := by
  obtain ⟨K, hK, hcert⟩ := stable_covariance_cosine_leading_log ha hm
  refine ⟨K, hK, fun h hh hhm => ?_⟩
  rw [stableAxisBubble_taylor_four_integral ha hm h]
  exact hcert h hh hhm

/-- The exact leading nonanalytic term and order-six remainder in the
revised stable-half bubble proposition. -/
theorem stableAxisBubble_exact_leading_log {a m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    (fun h : ℝ =>
      stableAxisBubble a m h - stableAxisBubble a m 0 -
        (iteratedDeriv 2 (stableAxisBubble a m) 0 / 2) * h ^ 2 -
        (iteratedDeriv 4 (stableAxisBubble a m) 0 / 24) * h ^ 4 +
        (a ^ 2 / (8192 * π ^ 2 * m ^ 4)) * h ^ 6 * log (m / |h|))
      =O[𝓝 0] (fun h => h ^ 6) := by
  obtain ⟨K, _, hK⟩ := stableAxisBubble_leading_log_bound ha hm
  refine Asymptotics.IsBigO.of_bound K ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hm] with h hh
  by_cases hz : h = 0
  · simp [hz]
  · have hhm : |h| ≤ m := (show |h| < m by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hh).le
    simpa only [Real.norm_eq_abs, abs_pow] using hK h (abs_pos.mpr hz) hhm

end UV
