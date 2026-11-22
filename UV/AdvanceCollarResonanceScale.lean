import UV.ResumeCollarLower
import UV.FurtherBoundaryCollar

/-! Optimizing the collar test at fixed duration as the normal angular
number approaches resonance in the same normal readout. -/

noncomputable section

open Filter Set Real
open scoped Topology

namespace UV.AdvanceCollarResonanceScale

open UV.ResumeCollarSpectral (durationLog)

def resonanceRadius (K ν : ℝ) : ℝ :=
  K * ν ^ (1 / 3 : ℝ) * durationLog ν ^ (-1 / 2 : ℝ)

def resonanceScale (ν : ℝ) : ℝ :=
  ν ^ (-2 / 3 : ℝ) * durationLog ν ^ (4 : ℕ)

private theorem durationLog_one_le (ν : ℝ) : 1 ≤ durationLog ν := by
  unfold durationLog
  linarith [abs_nonneg (Real.log ν)]

private theorem durationLog_pos (ν : ℝ) : 0 < durationLog ν :=
  zero_lt_one.trans_le (durationLog_one_le ν)

theorem resonance_radius_pos {K ν : ℝ} (hK : 0 < K) (hν : 0 < ν) :
    0 < resonanceRadius K ν :=
  mul_pos (mul_pos hK (Real.rpow_pos_of_pos hν _))
    (Real.rpow_pos_of_pos (durationLog_pos ν) _)

private theorem resonanceRadius_pow_div {K ν : ℝ} (hK : 0 < K) (hν : 0 < ν)
    (j : ℝ) (n : ℕ) :
    ν ^ j / resonanceRadius K ν ^ n =
      (K ^ n)⁻¹ * ν ^ (j - (n : ℝ) / 3) * durationLog ν ^ ((n : ℝ) / 2) := by
  let h := resonanceRadius K ν
  have hh := resonance_radius_pos hK hν
  have hEquation : (h ^ n)⁻¹ =
      (K ^ n)⁻¹ * ν ^ (-(n : ℝ) / 3) * durationLog ν ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hh.le]
    unfold resonanceRadius
    rw [Real.mul_rpow (mul_nonneg hK.le (Real.rpow_nonneg hν.le _))
      (Real.rpow_nonneg (durationLog_pos ν).le _), Real.mul_rpow hK.le (Real.rpow_nonneg hν.le _),
      ← Real.rpow_mul hν.le, ← Real.rpow_mul (durationLog_pos ν).le,
      Real.rpow_neg hK.le, Real.rpow_natCast]
    rw [show (1 / 3 : ℝ) * -(n : ℝ) = -(n : ℝ) / 3 by ring,
      show (-1 / 2 : ℝ) * -(n : ℝ) = (n : ℝ) / 2 by ring]
  rw [div_eq_mul_inv, hEquation, show j - (n : ℝ) / 3 = j + (-(n : ℝ) / 3) by ring,
    Real.rpow_add hν]
  ring

theorem resonance_energy_scaling {K ν : ℝ} (hK : 0 < K) (hν : 0 < ν) :
    let h := resonanceRadius K ν
    (h ^ (2 : ℕ))⁻¹ = (K ^ (2 : ℕ))⁻¹ * ν ^ (-2 / 3 : ℝ) * durationLog ν ∧
      ν ^ (2 : ℕ) / h ^ (8 : ℕ) = resonanceScale ν / K ^ (8 : ℕ) ∧
      ν / h ^ (5 : ℕ) =
        (K ^ (5 : ℕ))⁻¹ * ν ^ (-2 / 3 : ℝ) * durationLog ν ^ (5 / 2 : ℝ) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · have h := resonanceRadius_pow_div hK hν 0 2
    rw [show (0 : ℝ) - (↑(2 : ℕ) : ℝ) / 3 = -2 / 3 by norm_num] at h
    simpa using h
  · have h := resonanceRadius_pow_div hK hν 2 8
    rw [show (2 : ℝ) - ((8 : ℕ) : ℝ) / 3 = -2 / 3 by norm_num,
      show (((8 : ℕ) : ℝ) / 2) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast] at h
    have h' : ν ^ (2 : ℕ) / resonanceRadius K ν ^ (8 : ℕ) =
        (K ^ (8 : ℕ))⁻¹ * ν ^ (-2 / 3 : ℝ) * durationLog ν ^ (4 : ℕ) := by
      simpa only [Real.rpow_two] using h
    rw [h']
    unfold resonanceScale
    ring
  · have h := resonanceRadius_pow_div hK hν 1 5
    rw [Real.rpow_one, show (1 : ℝ) - ((5 : ℕ) : ℝ) / 3 = -2 / 3 by norm_num] at h
    simpa only [Nat.cast_ofNat] using h

private theorem resonance_radius_log {K ν : ℝ} (hK : 0 < K) (hν : 0 < ν) :
    Real.log (resonanceRadius K ν) =
      Real.log K + (1 / 3 : ℝ) * Real.log ν - (1 / 2 : ℝ) * Real.log (durationLog ν) := by
  unfold resonanceRadius
  rw [Real.log_mul (mul_ne_zero hK.ne' (Real.rpow_pos_of_pos hν _).ne')
    (Real.rpow_pos_of_pos (durationLog_pos ν) _).ne',
    Real.log_mul hK.ne' (Real.rpow_pos_of_pos hν _).ne',
    Real.log_rpow hν, Real.log_rpow (durationLog_pos ν)]
  ring

private theorem resonance_cutoff_eventually {K : ℝ} (hK : 0 < K) :
    ∀ᶠ ν in 𝓝[>] (0 : ℝ),
      0 < ν ∧ ν ≤ 1 ∧ 2 * resonanceRadius K ν ≤ 1 ∧
        6 * Real.log (2 * K) ≤ -Real.log ν := by
  have htlim : Tendsto (fun t : ℝ => t ^ (1 / 3 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont := (continuousAt_id (x := (0 : ℝ))).rpow_const
      (Or.inr (by norm_num : 0 ≤ (1 / 3 : ℝ)))
    simpa [ContinuousAt, Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0)] using
      hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hsmall := (tendsto_order.mp (by simpa using (htlim.const_mul K) : Tendsto
    (fun t : ℝ => K * t ^ (1 / 3 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0))).2 (1 / 2) (by norm_num)
  have hbig := Real.tendsto_log_nhdsGT_zero.eventually_le_atBot (-(6 * Real.log (2 * K)))
  filter_upwards [hsmall, hbig, Ioc_mem_nhdsGT one_pos] with ν hS hB hν
  have hroot : durationLog ν ^ (-1 / 2 : ℝ) ≤ 1 := by
    rw [← Real.rpow_zero (durationLog ν)]
    exact Real.rpow_le_rpow_of_exponent_le (durationLog_one_le ν) (by norm_num)
  refine ⟨hν.1, hν.2, ?_, by linarith⟩
  have hm := mul_le_mul_of_nonneg_left hroot (mul_nonneg hK.le (Real.rpow_nonneg hν.1.le (1 / 3 : ℝ)))
  unfold resonanceRadius
  nlinarith

private theorem durationLog_at_zero :
    Tendsto durationLog (𝓝[>] (0 : ℝ)) atTop := by
  have h : Tendsto (fun ν : ℝ => 1 + -Real.log ν) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)
  apply h.congr'
  filter_upwards [Ioc_mem_nhdsGT one_pos] with ν hν
  simp [durationLog, abs_of_nonpos (Real.log_nonpos hν.1.le hν.2)]

set_option maxHeartbeats 500000 in
/-- Uniform scalar lower bound from the exact supported-bump radius.
The logarithm includes the ninth-power overlap factor. -/
theorem resonance_bump_lower_scale {A B d t : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (hd : 0 < d) (ht : 0 < t) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ᶠ ν in 𝓝[>] (0 : ℝ),
      let h := resonanceRadius K ν
      0 < h ∧ 2 * h ≤ 1 ∧ ∀ r ∈ Icc h (2 * h),
        c * resonanceScale ν ≤
          Real.log (d * h ^ (9 : ℕ)) + A / r ^ (2 : ℕ) * durationLog r ^ (3 : ℕ) -
            2 * t * B * ((h ^ (2 : ℕ))⁻¹ + ν ^ (2 : ℕ) / h ^ (8 : ℕ) + ν / h ^ (5 : ℕ)) := by
  let a := A / (4 * 6 ^ (3 : ℕ))
  have ha : 0 < a := by positivity
  let K := 1 + 8 * t * B / a
  have hK1 : 1 ≤ K := by
    unfold K
    linarith [div_nonneg (show 0 ≤ 8 * t * B by positivity) ha.le]
  have hK : 0 < K := zero_lt_one.trans_le hK1
  let c := a / (4 * K ^ (2 : ℕ))
  have hc : 0 < c := by positivity
  have hkc : 2 * t * B / K ^ (8 : ℕ) ≤ c := by
    have hK6 : K ≤ K ^ (6 : ℕ) := le_self_pow₀ hK1 (by decide)
    have hsum : 8 * t * B ≤ a * K := by
      unfold K
      have hf : a * (1 + 8 * t * B / a) = a + 8 * t * B := by field_simp
      linarith
    have hbig := hsum.trans (mul_le_mul_of_nonneg_left hK6 ha.le)
    apply (div_le_div_iff₀ (pow_pos hK 8) (by positivity : 0 < 4 * K ^ 2)).mpr
    calc
      _ = (8 * t * B) * K ^ (2 : ℕ) := by ring
      _ ≤ (a * K ^ (6 : ℕ)) * K ^ (2 : ℕ) := mul_le_mul_of_nonneg_right hbig (sq_nonneg _)
      _ = _ := by ring
  let D := |Real.log d| + 9
  let M := 2 * t * B * ((K ^ (2 : ℕ))⁻¹ + (K ^ (5 : ℕ))⁻¹) + D
  have hD : 0 ≤ D := by unfold D; positivity
  have hLg := durationLog_at_zero.eventually_ge_atTop (M / c)
  refine ⟨K, c, hK, hc, ?_⟩
  filter_upwards [resonance_cutoff_eventually hK, hLg] with ν hsmall hLlarge
  obtain ⟨hν, hν1, hsupport, hbig⟩ := hsmall
  let h := resonanceRadius K ν
  let L := durationLog ν
  let X := ν ^ (-2 / 3 : ℝ)
  let S := resonanceScale ν
  have hh : 0 < h := resonance_radius_pos hK hν
  have hL : 0 < L := durationLog_pos ν
  have hL1 : 1 ≤ L := durationLog_one_le ν
  have hX1 : 1 ≤ X := by
    change 1 ≤ ν ^ (-2 / 3 : ℝ)
    rw [← Real.one_rpow (-2 / 3 : ℝ)]
    exact Real.rpow_le_rpow_of_nonpos hν hν1 (by norm_num)
  have hX := zero_le_one.trans hX1
  have hS : S = X * L ^ (4 : ℕ) := rfl
  have hSL : S / L = X * L ^ (3 : ℕ) := by rw [hS]; field_simp
  have hL13 : L ≤ L ^ (3 : ℕ) := le_self_pow₀ hL1 (by decide)
  have hL53 : L ^ (5 / 2 : ℝ) ≤ L ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hcost : M * (S / L) ≤ c * S := by
    have hcS : 0 ≤ S := by rw [hS]; positivity
    have hm : M / L ≤ c := (div_le_iff₀ hL).mpr ((div_le_iff₀ hc).mp hLlarge |>.trans_eq (mul_comm _ _))
    calc
      _ = (M / L) * S := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hm hcS
  obtain ⟨h2, h8, h5⟩ := resonance_energy_scaling hK hν
  change _ = (K ^ (2 : ℕ))⁻¹ * X * L at h2
  change _ = S / K ^ (8 : ℕ) at h8
  change _ = (K ^ (5 : ℕ))⁻¹ * X * L ^ (5 / 2 : ℝ) at h5
  have hkin : 2 * t * B * ((h ^ (2 : ℕ))⁻¹ + ν ^ (2 : ℕ) / h ^ (8 : ℕ) + ν / h ^ (5 : ℕ)) ≤
      c * S + (M - D) * (S / L) := by
    rw [h2, h8, h5]
    have h2' := mul_le_mul_of_nonneg_left hL13 (by positivity : 0 ≤ (K ^ (2 : ℕ))⁻¹ * X)
    have h5' := mul_le_mul_of_nonneg_left hL53 (by positivity : 0 ≤ (K ^ (5 : ℕ))⁻¹ * X)
    have h8' : 2 * t * B * (S / K ^ (8 : ℕ)) ≤ c * S := by
      calc
        _ = (2 * t * B / K ^ (8 : ℕ)) * S := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hkc (by rw [hS]; positivity)
    rw [hSL]
    unfold M
    have hsum := mul_le_mul_of_nonneg_left (add_le_add h2' h5') (show 0 ≤ 2 * t * B by positivity)
    linarith only [hsum, h8']
  have hlogh : -L ≤ Real.log h := by
    rw [show h = resonanceRadius K ν by rfl, resonance_radius_log hK hν]
    have hνlog : Real.log ν = 1 - L := by
      unfold L durationLog
      rw [abs_of_nonpos (Real.log_nonpos hν.le hν1)]
      ring
    rw [hνlog]
    linarith [Real.log_nonneg hK1, Real.log_le_sub_one_of_pos hL]
  have hlog : -(D * (S / L)) ≤ Real.log (d * h ^ (9 : ℕ)) := by
    rw [Real.log_mul hd.ne' (pow_ne_zero _ hh.ne'), Real.log_pow]
    have hs' : L ≤ S / L := by
      rw [hSL]
      exact hL13.trans (le_mul_of_one_le_left (pow_nonneg hL.le _) hX1)
    have ha' : -(D * L) ≤ Real.log d + 9 * Real.log h := by
      unfold D
      have hu := mul_le_mul_of_nonneg_left hL1 (abs_nonneg (Real.log d))
      have hv := neg_abs_le (Real.log d)
      linarith
    exact (neg_le_neg (mul_le_mul_of_nonneg_left hs' hD)).trans ha'
  refine ⟨hh, hsupport, fun r hr => ?_⟩
  have hr0 : 0 < r := hh.trans_le hr.1
  have hrt : r ≤ 1 := hr.2.trans hsupport
  have hrl : L / 6 ≤ durationLog r := by
    have hlogr := Real.log_le_log hr0 hr.2
    have hrepr : Real.log (2 * h) = Real.log (2 * K) + (1 / 3 : ℝ) * Real.log ν -
        (1 / 2 : ℝ) * Real.log L := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hh.ne', show h = resonanceRadius K ν by rfl,
        resonance_radius_log hK hν, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hK.ne']
      ring
    rw [hrepr] at hlogr
    unfold L durationLog
    rw [abs_of_nonpos (Real.log_nonpos hν.le hν1), abs_of_nonpos (Real.log_nonpos hr0.le hrt)]
    linarith [Real.log_nonneg hL1]
  have hmain : (4 * c) * S ≤ A / r ^ (2 : ℕ) * durationLog r ^ (3 : ℕ) := by
    calc
      _ = A / (2 * h) ^ (2 : ℕ) * (L / 6) ^ (3 : ℕ) := by
        have hcalc : A / (2 * h) ^ (2 : ℕ) = A * ((2 : ℝ) ^ (2 : ℕ))⁻¹ * (h ^ (2 : ℕ))⁻¹ := by
          rw [mul_pow, div_eq_mul_inv, mul_inv]
          ring
        rw [hcalc, h2, hS]
        unfold c a
        ring_nf
      _ ≤ _ := mul_le_mul
        (div_le_div_of_nonneg_left hA.le (pow_pos hr0 2) (pow_le_pow_left₀ hr0.le hr.2 2))
        (pow_le_pow_left₀ (by positivity) hrl 3) (by positivity) (by positivity)
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hcS := mul_nonneg hc.le hS0
  linarith only [hmain, hlog, hkin, hcost, hcS]

end UV.AdvanceCollarResonanceScale
