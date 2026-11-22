import UV.ResumeCollarSpectral

/-! The scalar bump optimization in the lower short-collar estimate. -/

noncomputable section

open Filter Set Real
open scoped Topology

namespace UV.ResumeCollarLower

/-- Radial size of the bump used for the short collar at duration `t`. -/
def bumpRadius (K t : ℝ) : ℝ :=
  K * t ^ (1 / 6 : ℝ) * UV.ResumeCollarSpectral.durationLog t ^ (-1 / 2 : ℝ)

open UV.ResumeCollarSpectral

private theorem durationLog_pos (t : ℝ) : 0 < durationLog t := by
  unfold durationLog
  positivity

private theorem bump_radius_rpow {K t : ℝ} (hK : 0 < K) (ht : 0 < t) (p : ℝ) :
    bumpRadius K t ^ p =
      K ^ p * t ^ ((1 / 6 : ℝ) * p) * durationLog t ^ ((-1 / 2 : ℝ) * p) := by
  unfold bumpRadius
  rw [Real.mul_rpow (mul_nonneg hK.le (Real.rpow_nonneg ht.le _))
    (Real.rpow_nonneg (durationLog_pos t).le _),
    Real.mul_rpow hK.le (Real.rpow_nonneg ht.le _),
    ← Real.rpow_mul ht.le, ← Real.rpow_mul (durationLog_pos t).le]

private theorem source_bump_log {K t r : ℝ} (hK : 0 < K) (ht : 0 < t) (ht1 : t ≤ 1)
    (hsmall : 2 * bumpRadius K t ≤ 1)
    (hbig : 12 * Real.log (2 * K) ≤ -Real.log t)
    (hr : r ∈ Icc (bumpRadius K t) (2 * bumpRadius K t)) :
    durationLog t / 12 ≤ durationLog r := by
  have hL1 : 1 ≤ durationLog t := by unfold durationLog; linarith [abs_nonneg (Real.log t)]
  have hLa : durationLog t = 1 - Real.log t := by
    unfold durationLog
    rw [abs_of_nonpos (Real.log_nonpos ht.le ht1)]
    ring
  have hb : 0 < bumpRadius K t := by
    unfold bumpRadius
    exact mul_pos (mul_pos hK (Real.rpow_pos_of_pos ht _)) (Real.rpow_pos_of_pos (durationLog_pos t) _)
  have hr0 := hb.trans_le hr.1
  have hrt : r ≤ 1 := hr.2.trans hsmall
  have hlogr := Real.log_le_log hr0 hr.2
  have hlogb : Real.log (2 * bumpRadius K t) =
      Real.log (2 * K) + (1 / 6 : ℝ) * Real.log t + (-1 / 2 : ℝ) * Real.log (durationLog t) := by
    have hrepr : 2 * bumpRadius K t =
        (2 * K) * t ^ (1 / 6 : ℝ) * durationLog t ^ (-1 / 2 : ℝ) := by
      unfold bumpRadius
      ring
    rw [hrepr, Real.log_mul
      (mul_pos (by positivity : 0 < 2 * K) (Real.rpow_pos_of_pos ht _)).ne'
      (Real.rpow_pos_of_pos (durationLog_pos t) _).ne',
      Real.log_mul (by positivity : 2 * K ≠ 0) (Real.rpow_pos_of_pos ht _).ne',
      Real.log_rpow ht, Real.log_rpow (durationLog_pos t)]
  rw [hlogb] at hlogr
  unfold durationLog
  rw [abs_of_nonpos (Real.log_nonpos ht.le ht1), abs_of_nonpos (Real.log_nonpos hr0.le hrt)]
  linarith [Real.log_nonneg hL1]

private theorem source_bump_kinetic {K t : ℝ} (hK : 0 < K) (ht : 0 < t) :
    t / bumpRadius K t ^ (8 : ℕ) = collarScale t / K ^ (8 : ℕ) := by
  rw [div_eq_mul_inv, ← Real.rpow_natCast, ← Real.rpow_neg (by
    unfold bumpRadius
    exact mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg ht.le _))
      (Real.rpow_nonneg (durationLog_pos t).le _))]
  rw [bump_radius_rpow hK ht]
  rw [show (1 / 6 : ℝ) * -((8 : ℕ) : ℝ) = -4 / 3 by norm_num,
    show (-1 / 2 : ℝ) * -((8 : ℕ) : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg hK.le, Real.rpow_natCast, Real.rpow_natCast]
  unfold collarScale
  have he : t * t ^ (-4 / 3 : ℝ) = t ^ (-1 / 3 : ℝ) := by
    rw [mul_comm, ← Real.rpow_add_one ht.ne']
    congr 1
    norm_num
  rw [show t * ((K ^ (8 : ℕ))⁻¹ * t ^ (-4 / 3 : ℝ) * durationLog t ^ (4 : ℕ)) =
    (t * t ^ (-4 / 3 : ℝ)) * durationLog t ^ (4 : ℕ) / K ^ (8 : ℕ) by ring, he]

/-- The bump radius yields the matching positive scalar lower coefficient on its entire support. -/
theorem source_bump_lower_scale {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (2 * bumpRadius K t ≤ 1) ∧
      ∀ r ∈ Icc (bumpRadius K t) (2 * bumpRadius K t),
        c * collarScale t ≤
          A / r ^ (2 : ℕ) * durationLog r ^ (3 : ℕ) -
            2 * B * t / bumpRadius K t ^ (8 : ℕ) := by
  let a := A / (4 * 12 ^ (3 : ℕ))
  have ha : 0 < a := by positivity
  let K := 1 + 4 * B / a
  have hK1 : 1 ≤ K := by unfold K; linarith [div_nonneg (by positivity : 0 ≤ 4*B) ha.le]
  have hK : 0 < K := zero_lt_one.trans_le hK1
  let c := a / (2 * K ^ (2 : ℕ))
  have hc : 0 < c := by positivity
  have hkcost : 2 * B / K ^ (8 : ℕ) ≤ c := by
    have hK6 : K ≤ K ^ (6 : ℕ) := le_self_pow₀ hK1 (by decide)
    have hsum : 4 * B ≤ a * K := by
      unfold K
      have hf : a * (1 + 4 * B / a) = a + 4 * B := by field_simp
      linarith
    have hbig := hsum.trans (mul_le_mul_of_nonneg_left hK6 ha.le)
    unfold c
    apply (div_le_div_iff₀ (pow_pos hK 8) (by positivity : 0 < 2 * K ^ (2 : ℕ))).mpr
    calc
      _ = (4 * B) * K ^ (2 : ℕ) := by ring
      _ ≤ (a * K ^ (6 : ℕ)) * K ^ (2 : ℕ) := mul_le_mul_of_nonneg_right hbig (sq_nonneg _)
      _ = _ := by ring
  refine ⟨K, c, hK, hc, ?_⟩
  have htlim : Tendsto (fun t : ℝ => t ^ (1 / 6 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont := (continuousAt_id (x := (0 : ℝ))).rpow_const
      (Or.inr (by norm_num : 0 ≤ (1 / 6 : ℝ)))
    simpa [ContinuousAt, Real.zero_rpow (by norm_num : (1 / 6 : ℝ) ≠ 0)] using
      hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hsmall := (tendsto_order.mp (by simpa using (htlim.const_mul K) :
    Tendsto (fun t : ℝ => K * t ^ (1 / 6 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0))).2 (1 / 2) (by norm_num)
  have hbig := Real.tendsto_log_nhdsGT_zero.eventually_le_atBot (-(12 * Real.log (2 * K)))
  filter_upwards [hsmall, hbig, Ioc_mem_nhdsGT one_pos] with t htS htB ht
  have ht0 : 0 < t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hL := durationLog_pos t
  have hL1 : 1 ≤ durationLog t := by unfold durationLog; linarith [abs_nonneg (Real.log t)]
  have hroot : durationLog t ^ (-1 / 2 : ℝ) ≤ 1 := by
    rw [← Real.rpow_zero (durationLog t)]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  let h := bumpRadius K t
  have hh : 0 < h := mul_pos (mul_pos hK (Real.rpow_pos_of_pos ht0 _)) (Real.rpow_pos_of_pos hL _)
  have hsm : 2 * h ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ K * t ^ (1 / 6 : ℝ))
    change h ≤ _ at hm
    nlinarith
  refine ⟨hsm, fun r hr => ?_⟩
  have hrl := source_bump_log hK ht0 ht1 hsm (by linarith) hr
  have hr0 : 0 < r := hh.trans_le hr.1
  have hD : A / (2 * h) ^ (2 : ℕ) ≤ A / r ^ (2 : ℕ) :=
    div_le_div_of_nonneg_left hA.le (pow_pos hr0 2) (pow_le_pow_left₀ hr0.le hr.2 2)
  have hpower : (h ^ (2 : ℕ))⁻¹ =
      (K ^ (2 : ℕ))⁻¹ * t ^ (-1 / 3 : ℝ) * durationLog t := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hh.le, show h = bumpRadius K t by rfl,
      bump_radius_rpow hK ht0, show (1 / 6 : ℝ) * -((2 : ℕ) : ℝ) = -1 / 3 by norm_num,
      show (-1 / 2 : ℝ) * -((2 : ℕ) : ℝ) = 1 by norm_num,
      Real.rpow_neg hK.le, Real.rpow_natCast, Real.rpow_one]
  have hmain :
      (2 * c) * collarScale t ≤ A / r ^ (2 : ℕ) * durationLog r ^ (3 : ℕ) := by
    calc
      _ = A / (2 * h) ^ (2 : ℕ) * (durationLog t / 12) ^ (3 : ℕ) := by
        have hcalc : A / (2 * h) ^ (2 : ℕ) = A * ((2 : ℝ) ^ (2 : ℕ))⁻¹ * (h ^ (2 : ℕ))⁻¹ := by
          rw [mul_pow, div_eq_mul_inv, mul_inv]
          ring
        rw [hcalc, hpower]
        unfold c a collarScale
        ring_nf
      _ ≤ _ := mul_le_mul hD (pow_le_pow_left₀ (by positivity) hrl 3) (by positivity) (by positivity)
  have hkin : 2 * B * t / h ^ (8 : ℕ) ≤ c * collarScale t := by
    rw [show 2 * B * t / h ^ (8 : ℕ) = 2 * B * (t / h ^ (8 : ℕ)) by ring,
      source_bump_kinetic hK ht0]
    have hS : 0 ≤ collarScale t := by
      unfold collarScale
      exact mul_nonneg (Real.rpow_nonneg ht0.le _) (by positivity)
    calc
      _ = (2 * B / K ^ (8 : ℕ)) * collarScale t := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hkcost hS
  linarith

/-- The exact supported-bump estimate transfers to the logarithmic lower bound. -/
theorem collar_lower_from_bump_test {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (Z E U : ℝ → ℝ)
    (hZ : ∀ r ∈ Ioc 0 1, Real.exp (A / r ^ (2 : ℕ) * durationLog r ^ (3 : ℕ)) ≤ Z r)
    (hE : ∀ h, 0 < h → 2 * h ≤ 1 → E h ≤ B / h ^ (8 : ℕ))
    (hTest : ∀ t h, 0 < t → 0 < h → 2 * h ≤ 1 → ∀ z,
      (∀ r ∈ Icc h (2 * h), z ≤ Z r) → z * Real.exp (-2 * t * E h) ≤ U t) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < U t ∧ c * collarScale t ≤ Real.log (U t) := by
  obtain ⟨K, c, hK, hc, hscale⟩ := source_bump_lower_scale hA hB
  refine ⟨c, hc, ?_⟩
  filter_upwards [hscale, self_mem_nhdsWithin] with t ht hpos
  have ht0 : 0 < t := hpos
  let h := bumpRadius K t
  have hh : 0 < h := mul_pos (mul_pos hK (Real.rpow_pos_of_pos ht0 _))
    (Real.rpow_pos_of_pos (durationLog_pos t) _)
  let z := Real.exp (c * collarScale t + 2 * B * t / h ^ (8 : ℕ))
  have hz : ∀ r ∈ Icc h (2 * h), z ≤ Z r := by
    intro r hr
    have hmon := ht.2 r hr
    change c * collarScale t ≤ _ - 2 * B * t / h ^ (8 : ℕ) at hmon
    exact (Real.exp_le_exp.mpr ((le_sub_iff_add_le).mp hmon)).trans
      (hZ r ⟨hh.trans_le hr.1, hr.2.trans ht.1⟩)
  have hU := hTest t h ht0 hh ht.1 z hz
  have hE0 := mul_le_mul_of_nonneg_left (hE h hh ht.1) (show 0 ≤ 2 * t by positivity)
  have hL : Real.exp (c * collarScale t) ≤ U t := by
    apply le_trans _ hU
    unfold z
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hrw : 2 * t * (B / h ^ (8 : ℕ)) = 2 * B * t / h ^ (8 : ℕ) := by ring
    rw [hrw] at hE0
    linarith
  refine ⟨(Real.exp_pos _).trans_le hL, ?_⟩
  simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hL

end UV.ResumeCollarLower
