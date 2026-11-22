import UV.AdvanceNetworkMomentum
import UV.ContinueNetworkTonelli

/-! The proper-time estimate for marked routed networks. Fixed powers of
the positive durations and their inverses retain the original edge-kernel
prefactor and cost a finite inverse power of the common mark scale. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace UV

/-- The short-duration exponential gains any fixed integer power at a
cost of the corresponding inverse power of the positive mark scale. -/
theorem networkShortMarkInversePower {c r s z : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hs : 0 < s) (hz : c * r ≤ z) (N : ℕ) :
    Real.exp (-(z ^ 2 / (4 * s))) ≤
      (((N.factorial : ℝ) / (c ^ 2 / 4) ^ N) / r ^ (2 * N)) * s ^ N := by
  let a := (c ^ 2 / 4) * r ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hsq := pow_le_pow_left₀ (mul_nonneg hc.le hr.le) hz 2
  rw [mul_pow] at hsq
  have hexp : Real.exp (-(z ^ 2 / (4 * s))) ≤ Real.exp (-(a * s⁻¹)) := by
    apply Real.exp_le_exp.mpr
    dsimp [a]
    have h := div_le_div_of_nonneg_right hsq (show 0 ≤ 4 * s by positivity)
    have haeq : c ^ 2 / 4 * r ^ 2 * s⁻¹ = c ^ 2 * r ^ 2 / (4 * s) := by
      field_simp
    rw [haeq]
    exact neg_le_neg h
  calc
    _ ≤ Real.exp (-(a * s⁻¹)) := hexp
    _ = s ^ N * ((s⁻¹) ^ N * Real.exp (-(a * s⁻¹))) := by
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hs.ne', one_pow, one_mul]
    _ ≤ s ^ N * ((N.factorial : ℝ) / a ^ N) :=
      mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le ha (inv_nonneg.mpr hs.le) N)
        (pow_nonneg hs.le _)
    _ = _ := by unfold a; rw [mul_pow, ← pow_mul]; ring

def networkTimePolynomial (p q : ℕ) (s : ℝ) : ℝ :=
  (1 + s) ^ p * (1 + s⁻¹) ^ q

def networkEdgeTimeEnvelope (m : ℝ) (d : ℕ) (s : ℝ) : ℝ :=
  (1 + s) ^ d * Real.exp (-(m ^ 2 * s))

def networkEdgeTimeConstant (c : ℝ) (q : ℕ) : ℝ :=
  (1 / (32 * Real.pi ^ 2 * Real.sqrt Real.pi)) *
    (((q + 3).factorial : ℝ) / (c ^ 2 / 4) ^ (q + 3))

/-- The literal weighted five-dimensional edge kernel has an integrable
time envelope with a fixed inverse mark cost. -/
theorem networkEdgeTime_bound (m : ℝ) (p q : ℕ) {c r s z : ℝ}
    (hc : 0 < c) (hr : 0 < r) (hs : 0 < s) (hz : c * r ≤ z) :
    networkTimePolynomial p q s * networkHeatFive m z s ≤
      (networkEdgeTimeConstant c q / r ^ (2 * (q + 3))) *
        networkEdgeTimeEnvelope m (p + q + 1) s := by
  let A : ℝ := 1 / (32 * Real.pi ^ 2 * Real.sqrt Real.pi)
  let M := ((q + 3).factorial : ℝ) / (c ^ 2 / 4) ^ (q + 3) / r ^ (2 * (q + 3))
  have hmul : (1 + s⁻¹) ^ q * s ^ (q + 3) = (1 + s) ^ q * s ^ 3 := by
    rw [pow_add, ← mul_assoc, ← mul_pow]
    congr 2
    rw [add_mul, inv_mul_cancel₀ hs.ne', one_mul, add_comm]
  have hpow : s ^ (-(5 : ℝ) / 2) * s ^ 3 = Real.sqrt s := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hs]
    congr 1
    norm_num
  have hsqrt : Real.sqrt s ≤ 1 + s := by
    nlinarith [Real.sq_sqrt hs.le, sq_nonneg (Real.sqrt s - 1)]
  have hK : 0 ≤ A * M := by dsimp [A, M]; positivity
  calc
    _ = ((1 + s) ^ p * (1 + s⁻¹) ^ q * A * s ^ (-(5 : ℝ) / 2) *
        Real.exp (-(m ^ 2 * s))) * Real.exp (-(z ^ 2 / (4 * s))) := by
      unfold networkTimePolynomial networkHeatFive A
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ ((1 + s) ^ p * (1 + s⁻¹) ^ q * A * s ^ (-(5 : ℝ) / 2) *
        Real.exp (-(m ^ 2 * s))) * (M * s ^ (q + 3)) :=
      mul_le_mul_of_nonneg_left (networkShortMarkInversePower hc hr hs hz (q + 3))
        (by positivity)
    _ = (A * M) * ((1 + s) ^ (p + q) * Real.sqrt s * Real.exp (-(m ^ 2 * s))) := by
      have hjoin : (1 + s⁻¹) ^ q * s ^ (q + 3) * s ^ (-(5 : ℝ) / 2) =
          (1 + s) ^ q * Real.sqrt s := by
        rw [hmul, mul_assoc, mul_comm (s ^ 3), hpow]
      calc
        _ = (A * M) * ((1 + s) ^ p *
            ((1 + s⁻¹) ^ q * s ^ (q + 3) * s ^ (-(5 : ℝ) / 2)) *
            Real.exp (-(m ^ 2 * s))) := by ring
        _ = _ := by rw [hjoin, pow_add]; ring
    _ ≤ (A * M) * ((1 + s) ^ (p + q) * (1 + s) * Real.exp (-(m ^ 2 * s))) := by
      gcongr
    _ = _ := by unfold A M networkEdgeTimeConstant networkEdgeTimeEnvelope; rw [pow_succ]; ring

theorem networkEdgeTimeEnvelope_integrable {m : ℝ} (hm : 0 < m) (d : ℕ) :
    IntegrableOn (networkEdgeTimeEnvelope m d) (Ioi 0) := by
  have h := (integrable_polynomial_exp (E := ℝ) (μ := volume) (sq_pos_of_pos hm) d).const_mul
    ((2 : ℝ) ^ (d - 1))
  apply h.integrableOn.mono' (by
    apply Measurable.aestronglyMeasurable
    unfold networkEdgeTimeEnvelope
    fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hpos : 0 < s := hs
  change ‖networkEdgeTimeEnvelope m d s‖ ≤
    (2 : ℝ) ^ (d - 1) * ((1 + ‖s‖ ^ d) * Real.exp (-(m ^ 2 * ‖s‖)))
  rw [Real.norm_of_nonneg hpos.le, networkEdgeTimeEnvelope, Real.norm_of_nonneg (by positivity),
    ← mul_assoc]
  have hp := add_pow_le (show 0 ≤ (1 : ℝ) from zero_le_one) hpos.le d
  simp only [one_pow] at hp
  exact mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)

/-- Positive masses control the tail and positive transverse marks the
short-time region under every fixed pair of proper-time powers. -/
theorem networkEdgeTime_integral_bound {m c r z : ℝ}
    (hm : 0 < m) (hc : 0 < c) (hr : 0 < r) (hz : c * r ≤ z) (p q : ℕ) :
    IntegrableOn (fun s => networkTimePolynomial p q s * networkHeatFive m z s) (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ), networkTimePolynomial p q s * networkHeatFive m z s) ≤
        (networkEdgeTimeConstant c q / r ^ (2 * (q + 3))) *
          ∫ s in Ioi (0 : ℝ), networkEdgeTimeEnvelope m (p + q + 1) s := by
  let K := networkEdgeTimeConstant c q / r ^ (2 * (q + 3))
  have hn {s : ℝ} (hs : 0 < s) :
      0 ≤ networkTimePolynomial p q s * networkHeatFive m z s := by
    unfold networkTimePolynomial
    exact mul_nonneg (by positivity) (networkHeatFive_nonneg hs.le m z)
  have hI := (networkEdgeTimeEnvelope_integrable hm (p + q + 1)).const_mul K
  have hBound : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)),
      networkTimePolynomial p q s * networkHeatFive m z s ≤ K * networkEdgeTimeEnvelope m (p + q + 1) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact networkEdgeTime_bound m p q hc hr hs hz
  have hInt : IntegrableOn (fun s => networkTimePolynomial p q s * networkHeatFive m z s) (Ioi 0) := by
    apply hI.mono' (by
      apply Measurable.aestronglyMeasurable
      unfold networkTimePolynomial networkHeatFive
      fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi, hBound] with s hs hb
    rwa [Real.norm_of_nonneg (hn hs)]
  have h := integral_mono_ae hInt hI hBound
  rw [integral_const_mul] at h
  exact ⟨hInt, h⟩

end UV
