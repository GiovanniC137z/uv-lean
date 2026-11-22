import UV.FurtherBoundaryEnvelope

/-! The sharp scalar spectral exponent for a short charged normal collar. -/

noncomputable section

open Real

namespace UV.ResumeCollarSpectral

/-- The logarithmic factor for short collar durations. -/
def durationLog (t : ℝ) : ℝ := 1 + |Real.log t|

/-- The scale of the sharp short-duration logarithmic bound. -/
def collarScale (t : ℝ) : ℝ := t ^ (-1 / 3 : ℝ) * durationLog t ^ (4 : ℕ)

private theorem durationLog_one_le (t : ℝ) : 1 ≤ durationLog t := by
  unfold durationLog
  linarith [abs_nonneg (Real.log t)]

private theorem collarScale_one_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    1 ≤ collarScale t := by
  have hp : 1 ≤ t ^ (-1 / 3 : ℝ) := by
    rw [← Real.rpow_zero t]
    exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num)
  change 1 ≤ t ^ (-1 / 3 : ℝ) * durationLog t ^ (4 : ℕ)
  have hL := pow_le_pow_left₀ zero_le_one (durationLog_one_le t) 4
  simp only [one_pow] at hL
  simpa only [one_mul] using mul_le_mul hp hL zero_le_one
    (Real.rpow_nonneg ht.le (-1 / 3))

private theorem logarithm_le_fractional_power {v : ℝ} (hv : 0 < v) :
    Real.log v ≤ 12 * v ^ (1 / 12 : ℝ) := by
  have he := Real.add_one_le_exp (Real.log v / 12)
  rw [Real.rpow_def_of_pos hv, show Real.log v * (1 / 12) = Real.log v / 12 by ring]
  linarith

private theorem scalar_log_growth {v : ℝ} (hv : 1 ≤ v) :
    v ^ (1 / 4 : ℝ) * (1 + Real.log v) ^ (3 : ℕ) ≤ 13 ^ (3 : ℕ) * Real.sqrt v := by
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have hlog0 := Real.log_nonneg hv
  have h12 : 1 ≤ v ^ (1 / 12 : ℝ) := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow zero_le_one hv (by norm_num : 0 ≤ (1 / 12 : ℝ))
  have hsum := logarithm_le_fractional_power hv0
  have hp : (1 + Real.log v) ^ (3 : ℕ) ≤ (13 * v ^ (1 / 12 : ℝ)) ^ (3 : ℕ) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hcube : (v ^ (1 / 12 : ℝ)) ^ (3 : ℕ) = v ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_mul_natCast hv0.le]
    congr 1
    norm_num
  calc
    _ ≤ v ^ (1 / 4 : ℝ) * (13 * v ^ (1 / 12 : ℝ)) ^ (3 : ℕ) :=
      mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hv0.le _)
    _ = _ := by
      rw [mul_pow, hcube, ← mul_left_comm, ← Real.rpow_add hv0, Real.sqrt_eq_rpow]
      norm_num

/-- The source exponent has the sharp upper scale after subtracting the heat energy. -/
theorem collar_exponent_upper {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t x : ℝ), 0 < t → t ≤ 1 → 1 ≤ x →
      A * x ^ (1 / 4 : ℝ) * (1 + Real.log x) ^ (3 : ℕ) - t * x ≤ C * collarScale t := by
  let B := A * (7 : ℝ) ^ (3 : ℕ) * (13 : ℝ) ^ (3 : ℕ)
  refine ⟨1 + (B / 2) ^ (2 : ℕ), by positivity, ?_⟩
  intro t x ht ht1 hx
  let L := durationLog t
  let y := t ^ (-4 / 3 : ℝ) * L ^ (4 : ℕ)
  let v := max 1 (x / y)
  have hL : 1 ≤ L := durationLog_one_le t
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hy : 0 < y := mul_pos (Real.rpow_pos_of_pos ht _) (pow_pos hL0 _)
  have hv : 1 ≤ v := le_max_left _ _
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hty : t * y = collarScale t := by
    unfold y collarScale L
    rw [← mul_assoc, mul_comm t, ← Real.rpow_add_one ht.ne']
    congr 1
    norm_num
  have hyq : y ^ (1 / 4 : ℝ) = t ^ (-1 / 3 : ℝ) * L := by
    unfold y
    rw [Real.mul_rpow (Real.rpow_nonneg ht.le _) (pow_nonneg hL0.le _),
      ← Real.rpow_mul ht.le, show (-4 / 3 : ℝ) * (1 / 4) = -1 / 3 by norm_num]
    congr 1
    simpa using Real.pow_rpow_inv_natCast hL0.le (n := 4) (by decide)
  have hxy : x ≤ v * y := (div_le_iff₀ hy).mp (le_max_right _ _)
  have hvx : v ≤ 1 + x / y := max_le (by linarith [div_nonneg hx0.le hy.le]) (by linarith)
  have hnegative : t * y * (v - 1) ≤ t * x := by
    have hh : (v - 1) * y ≤ x := (le_div_iff₀ hy).mp (by linarith)
    linarith [mul_le_mul_of_nonneg_left hh ht.le]
  have hLdesc : L = 1 - Real.log t := by
    unfold L durationLog
    rw [abs_of_nonpos (Real.log_nonpos ht.le ht1)]
    ring
  have hylog : Real.log y ≤ 6 * L := by
    unfold y
    rw [Real.log_mul (Real.rpow_pos_of_pos ht _).ne' (pow_pos hL0 _).ne',
      Real.log_rpow ht, Real.log_pow]
    push_cast
    linarith [Real.log_le_sub_one_of_pos hL0]
  have hlog : 1 + Real.log x ≤ 7 * L * (1 + Real.log v) := by
    have hlogxy := Real.log_le_log hx0 hxy
    rw [Real.log_mul hv0.ne' hy.ne'] at hlogxy
    have hvlog0 := Real.log_nonneg hv
    nlinarith [mul_nonneg (show 0 ≤ L - 1 by linarith) hvlog0]
  have hlog0 : 0 ≤ 1 + Real.log x := by linarith [Real.log_nonneg hx]
  have hex : x ^ (1 / 4 : ℝ) ≤ v ^ (1 / 4 : ℝ) * (t ^ (-1 / 3 : ℝ) * L) := by
    simpa only [Real.mul_rpow hv0.le hy.le, hyq] using
      Real.rpow_le_rpow hx0.le hxy (by norm_num : 0 ≤ (1 / 4 : ℝ))
  have hpositive : A * x ^ (1 / 4 : ℝ) * (1 + Real.log x) ^ (3 : ℕ) ≤
      collarScale t * (B * Real.sqrt v) := by
    calc
      _ ≤ A * (v ^ (1 / 4 : ℝ) * (t ^ (-1 / 3 : ℝ) * L)) *
          (7 * L * (1 + Real.log v)) ^ (3 : ℕ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hex hA) (pow_le_pow_left₀ hlog0 hlog 3)
          (pow_nonneg hlog0 _) (by positivity)
      _ = collarScale t * (A * 7 ^ (3 : ℕ) *
          (v ^ (1 / 4 : ℝ) * (1 + Real.log v) ^ (3 : ℕ))) := by
        unfold collarScale L
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by
          unfold collarScale
          exact mul_nonneg (Real.rpow_nonneg ht.le _) (by positivity))
        unfold B
        rw [mul_assoc (A * 7 ^ (3 : ℕ))]
        exact mul_le_mul_of_nonneg_left (scalar_log_growth hv) (by positivity)
  have hquadratic : B * Real.sqrt v - v + 1 ≤ 1 + (B / 2) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (Real.sqrt v - B / 2), Real.sq_sqrt hv0.le]
  rw [hty] at hnegative
  nlinarith [mul_le_mul_of_nonneg_left hquadratic
    (zero_le_one.trans (collarScale_one_le ht ht1))]

private theorem inv_one_sub_exp_neg_le {z : ℝ} (hz : 0 < z) :
    (1 - Real.exp (-z))⁻¹ ≤ 1 + z⁻¹ := by
  have hcmp := inv_anti₀ (by linarith : (0 : ℝ) < z + 1) (Real.add_one_le_exp z)
  rw [← Real.exp_neg, add_comm z] at hcmp
  have hfrac : 1 - (1 + z)⁻¹ = z / (1 + z) := by
    field_simp
    ring
  have hl : z / (1 + z) ≤ 1 - Real.exp (-z) := by
    rw [← hfrac]
    linarith
  convert inv_anti₀ (div_pos hz (by linarith : (0 : ℝ) < 1 + z)) hl using 1
  rw [inv_div, add_div]
  simp [hz.ne', one_div, add_comm]

private theorem duration_neg_log_le_scale {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    -Real.log t ≤ collarScale t := by
  have hp : 1 ≤ t ^ (-1 / 3 : ℝ) := by
    rw [← Real.rpow_zero t]
    exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num)
  have hL := durationLog_one_le t
  have hpow := pow_le_pow_left₀ zero_le_one hL 3
  simp only [one_pow] at hpow
  have hpow' : durationLog t ≤ durationLog t ^ (4 : ℕ) := by
    calc
      _ = durationLog t * 1 := by ring
      _ ≤ durationLog t * durationLog t ^ (3 : ℕ) :=
        mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hL)
      _ = _ := by ring
  calc
    _ ≤ durationLog t := by
      unfold durationLog
      linarith [neg_le_abs (Real.log t)]
    _ ≤ durationLog t ^ (4 : ℕ) := hpow'
    _ ≤ _ := by
      unfold collarScale
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp
        (pow_nonneg (zero_le_one.trans hL) 4)

/-- Weighted spectral summability and the sharp upper scale follow from the stated mode bounds. -/
theorem collar_spectral_trace_upper {A α : ℝ} (hA : 0 < A) (hα : 0 < α)
    (E W : ℕ → ℝ)
    (hE : ∀ n : ℕ, α * (n : ℝ) ^ (2 : ℕ) ≤ E n)
    (hW0 : ∀ n, 0 ≤ W n)
    (hW : ∀ n, W n ≤ A * (1 + E n) *
      Real.exp (A * (1 + E n) ^ (1 / 4 : ℝ) * (1 + Real.log (2 + E n)) ^ (3 : ℕ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      Summable (fun n => W n * Real.exp (-2 * t * E n)) ∧
      ((0 < ∑' n, W n * Real.exp (-2 * t * E n)) →
        Real.log (∑' n, W n * Real.exp (-2 * t * E n)) ≤ C * collarScale t) := by
  obtain ⟨C, hC, hCbound⟩ := collar_exponent_upper hA.le
  let D := 2 * A * (1 + 2 / α)
  have hD : 0 < D := by positivity
  refine ⟨C + 4 + |Real.log D|, by linarith [abs_nonneg (Real.log D)], ?_⟩
  intro t ht ht1
  let S := collarScale t
  let g := Real.exp (-(t * α / 2))
  let P := (2 / t) * A * Real.exp ((C + 2) * S)
  let f := fun n => W n * Real.exp (-2 * t * E n)
  have hS : 1 ≤ S := collarScale_one_le ht ht1
  have hg0 : 0 ≤ g := Real.exp_nonneg _
  have hg1 : g < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (by positivity))
  have hP : 0 ≤ P := by positivity
  have hterm (n : ℕ) : f n ≤ P * g ^ n := by
    have hE0 : 0 ≤ E n := (mul_nonneg hα.le (sq_nonneg _)).trans (hE n)
    let z := A * (1 + E n) ^ (1 / 4 : ℝ) * (1 + Real.log (2 + E n)) ^ (3 : ℕ)
    have hshift : z - t * E n ≤ (C + 2) * S := by
      have hb := hCbound t (2 + E n) ht ht1 (by linarith)
      have hpow : (1 + E n) ^ (1 / 4 : ℝ) ≤ (2 + E n) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      have hlog : 0 ≤ 1 + Real.log (2 + E n) := by
        linarith [Real.log_nonneg (by linarith : 1 ≤ 2 + E n)]
      have hmono := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hA.le)
        (pow_nonneg hlog 3)
      change z ≤ _ at hmono
      nlinarith
    have hpol : 1 + E n ≤ (2 / t) * Real.exp (t * E n / 2) := by
      have htwo : 1 ≤ 2 / t := (le_div_iff₀ ht).mpr (by linarith)
      calc
        _ ≤ 2 / t + E n := by linarith
        _ = (2 / t) * (t * E n / 2 + 1) := by
          field_simp
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (by positivity)
    have hnat : (n : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) := by
      cases n with
      | zero => norm_num
      | succ n =>
        rw [Nat.cast_succ]
        nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]
    have hmode : Real.exp (-(t * E n / 2)) ≤ g ^ n := by
      unfold g
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_left hnat hα.le).trans (hE n)) ht.le]
    calc
      f n ≤ (A * (1 + E n) * Real.exp z) * Real.exp (-2 * t * E n) :=
        mul_le_mul_of_nonneg_right (hW n) (Real.exp_nonneg _)
      _ = A * (1 + E n) * Real.exp (z - t * E n) * Real.exp (-(t * E n)) := by
        rw [mul_assoc (A * (1 + E n)), mul_assoc (A * (1 + E n)),
          ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
      _ ≤ A * ((2 / t) * Real.exp (t * E n / 2)) * Real.exp ((C + 2) * S) *
          Real.exp (-(t * E n)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hpol hA.le) (Real.exp_le_exp.mpr hshift)
          (Real.exp_nonneg _) (by positivity)
      _ = P * Real.exp (-(t * E n / 2)) := by
        unfold P
        rw [show -(t * E n / 2) = t * E n / 2 + -(t * E n) by ring, Real.exp_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmode hP
  have hgeom := (summable_geometric_of_lt_one hg0 hg1).mul_left P
  have hs : Summable f := Summable.of_nonneg_of_le (fun n => mul_nonneg (hW0 n) (Real.exp_nonneg _))
    hterm hgeom
  have hsum := hs.tsum_le_tsum hterm hgeom
  rw [tsum_mul_left, tsum_geometric_of_lt_one hg0 hg1] at hsum
  have hfund : ∑' n, f n ≤ D * (t⁻¹) ^ (2 : ℕ) * Real.exp ((C + 2) * S) := by
    have hz : 0 < t * α / 2 := by positivity
    have hInv : (1 - g)⁻¹ ≤ (1 + 2 / α) / t := by
      have hi := inv_one_sub_exp_neg_le hz
      change (1 - g)⁻¹ ≤ 1 + (t * α / 2)⁻¹ at hi
      refine hi.trans ((le_div_iff₀ ht).mpr ?_)
      rw [show (t * α / 2)⁻¹ = 2 / (t * α) by simp [inv_div]]
      rw [add_mul, one_mul]
      have hcancel : 2 / (t * α) * t = 2 / α := by field_simp
      rw [hcancel]
      linarith
    calc
      _ ≤ P * (1 - g)⁻¹ := hsum
      _ ≤ P * ((1 + 2 / α) / t) := mul_le_mul_of_nonneg_left hInv hP
      _ = _ := by unfold P D; ring
  refine ⟨hs, ?_⟩
  intro hpos
  have hlog := Real.log_le_log hpos hfund
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',
    Real.log_mul hD.ne' (pow_pos (inv_pos.mpr ht) _).ne',
    Real.log_pow, Real.log_inv, Real.log_exp] at hlog
  have hlogD : Real.log D ≤ |Real.log D| * S := by
    have := mul_le_mul_of_nonneg_left hS (abs_nonneg (Real.log D))
    linarith [le_abs_self (Real.log D)]
  have hlt : -Real.log t ≤ S := duration_neg_log_le_scale ht ht1
  change _ ≤ (C + 4 + |Real.log D|) * S
  simp only [Nat.cast_ofNat] at hlog
  calc
    _ ≤ Real.log D + (2 : ℝ) * -Real.log t + (C + 2) * S := hlog
    _ ≤ |Real.log D| * S + 2 * S + (C + 2) * S :=
      add_le_add_right (add_le_add hlogD (mul_le_mul_of_nonneg_left hlt (by norm_num))) _
    _ = _ := by ring

/-- The weighted spectral preparation has a finite positive trace at every positive duration. -/
theorem collar_spectral_trace_at_fixed_time {A α : ℝ} (hA : 0 < A) (hα : 0 < α)
    (E W : ℕ → ℝ)
    (hE : ∀ n : ℕ, α * (n : ℝ) ^ (2 : ℕ) ≤ E n)
    (hW0 : ∀ n, 0 ≤ W n)
    (hW : ∀ n, W n ≤ A * (1 + E n) *
      Real.exp (A * (1 + E n) ^ (1 / 4 : ℝ) * (1 + Real.log (2 + E n)) ^ (3 : ℕ)))
    (hWpos : ∃ n, 0 < W n) {t : ℝ} (ht : 0 < t) :
    Summable (fun n => W n * Real.exp (-2 * t * E n)) ∧
      0 < ∑' n, W n * Real.exp (-2 * t * E n) := by
  let s := min t 1
  have hs : 0 < s := lt_min ht zero_lt_one
  obtain ⟨C, -, hsmall⟩ := collar_spectral_trace_upper hA hα E W hE hW0 hW
  have hsumSmall := (hsmall s hs (min_le_right _ _)).1
  have hnonneg (n : ℕ) : 0 ≤ W n * Real.exp (-2 * t * E n) :=
    mul_nonneg (hW0 n) (Real.exp_nonneg _)
  have hsum : Summable (fun n => W n * Real.exp (-2 * t * E n)) := by
    refine Summable.of_nonneg_of_le hnonneg (fun n => ?_) hsumSmall
    have hE0 : 0 ≤ E n := (mul_nonneg hα.le (sq_nonneg _)).trans (hE n)
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (hW0 n)
    have hst : s ≤ t := min_le_left _ _
    nlinarith [mul_le_mul_of_nonneg_right hst hE0]
  refine ⟨hsum, ?_⟩
  obtain ⟨n, hn⟩ := hWpos
  exact (mul_pos hn (Real.exp_pos _)).trans_le (hsum.le_tsum n (fun i _ => hnonneg i))

end UV.ResumeCollarSpectral
