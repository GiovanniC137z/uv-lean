import UV.ContinuationOpeningFock

/-! Position on the oscillator number core. The vacuum powers below are
formed with the literal lowering and raising weights. Their Taylor series
converges absolutely in the positive number space. -/

noncomputable section

namespace UV

open Filter
open scoped ENNReal Nat Topology

abbrev OpeningFock := ℓ²(ℕ, ℂ)

/-- The number coordinates of (a+a^†). The second term vanishes at
the boundary (n=0). -/
def openingJacobi (v : ℕ → ℂ) (n : ℕ) : ℂ :=
  (Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ) * v (n + 1) +
    (Real.sqrt (n : ℝ) : ℂ) * v (n - 1)

/-- Every iterate uses the actual raising and lowering rule. -/
def openingVacuumPowerSeq : ℕ → ℕ → ℂ
  | 0 => openingNumberState 0
  | k + 1 => openingJacobi (openingVacuumPowerSeq k)

theorem openingVacuumPowerSeq_support (k n : ℕ) (hn : k < n) :
    openingVacuumPowerSeq k n = 0 := by
  induction k generalizing n with
  | zero =>
    change (Pi.single 0 (1 : ℂ) : ℕ → ℂ) n = 0
    exact Pi.single_eq_of_ne (by omega : n ≠ 0) _
  | succ k ih =>
    simp [openingVacuumPowerSeq, openingJacobi, ih (n + 1) (by omega),
      ih (n - 1) (by omega)]

private theorem opening.memℓp_of_cutoff {v : ℕ → ℂ} {k : ℕ} (hv : ∀ n > k, v n = 0) :
    Memℓp v 2 := by
  refine memℓp_gen (summable_of_ne_finset_zero (s := Finset.range (k + 1)) ?_)
  intro n hn
  simp only [Finset.mem_range, not_lt] at hn
  simp [hv n (by omega)]

def openingVacuumPower (k : ℕ) : OpeningFock :=
  ⟨openingVacuumPowerSeq k, opening.memℓp_of_cutoff (fun n hn => openingVacuumPowerSeq_support k n hn)⟩

@[simp] theorem openingVacuumPower_apply (k n : ℕ) :
    openingVacuumPower k n = openingVacuumPowerSeq k n := rfl

@[simp] theorem openingVacuumPower_zero : openingVacuumPower 0 = openingNumberState 0 := by
  ext n
  rfl

private theorem opening.norm_sq_eq_cutoff (v : OpeningFock) {k : ℕ}
    (hv : ∀ n > k, v n = 0) :
    ‖v‖ ^ 2 = ∑ n ∈ Finset.range (k + 1), ‖v n‖ ^ 2 := by
  have ht := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) v
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at ht
  rw [ht, tsum_eq_sum]
  intro n hn
  have h : k < n := by
    simp only [Finset.mem_range, not_lt] at hn
    omega
  simp [hv n h]

private theorem opening.norm_mul_sqrt_sq (a : ℂ) (i : ℕ) :
    ‖(Real.sqrt (i : ℝ) : ℂ) * a‖ ^ 2 = i * ‖a‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

private theorem opening.sum_jacobi_le (v : OpeningFock) {k : ℕ}
    (hv : ∀ n > k, v n = 0) :
    ∑ n ∈ Finset.range (k + 2), ‖openingJacobi v n‖ ^ 2 ≤
      4 * (k + 1) * ∑ n ∈ Finset.range (k + 1), ‖v n‖ ^ 2 := by
  let u (i : ℕ) := ‖v i‖ ^ 2
  have hA :
      (∑ n ∈ Finset.range (k + 2), (n + 1 : ℝ) * u (n + 1)) ≤
        (k + 1 : ℝ) * ∑ n ∈ Finset.range (k + 1), u n := by
    have hs : (∑ n ∈ Finset.range (k + 2), (n + 1 : ℝ) * u (n + 1)) =
        ∑ n ∈ Finset.range (k + 1), (n : ℝ) * u n := by
      let f (n : ℕ) := (n : ℝ) * u n
      calc
        _ = ∑ n ∈ Finset.range ((k + 2) + 1), f n := by
          rw [Finset.sum_range_succ' f]
          simp [f, Nat.cast_add]
        _ = _ := by
          rw [Finset.sum_range_succ, Finset.sum_range_succ]
          simp [f, u, hv (k + 2) (by omega), hv (k + 1) (by omega)]
    rw [hs, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    gcongr
    exact_mod_cast Nat.le_of_lt (Finset.mem_range.1 hn)
  have hB :
      (∑ n ∈ Finset.range (k + 2), (n : ℝ) * u (n - 1)) ≤
        (k + 1 : ℝ) * ∑ n ∈ Finset.range (k + 1), u n := by
    rw [Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.cast_zero, zero_mul, add_zero, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    apply Finset.sum_le_sum
    intro n hn
    gcongr
    exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.1 hn)
  calc
    _ ≤ ∑ n ∈ Finset.range (k + 2), 2 *
        ((n + 1 : ℝ) * u (n + 1) + (n : ℝ) * u (n - 1)) := by
      apply Finset.sum_le_sum
      intro n _
      unfold openingJacobi
      let a := (Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ) * v (n + 1)
      let b := (Real.sqrt (n : ℝ) : ℂ) * v (n - 1)
      have h : ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
        have h₁ := pow_le_pow_left₀ (norm_nonneg (a + b)) (norm_add_le a b) 2
        nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
      dsimp [a, b] at h
      rw [opening.norm_mul_sqrt_sq, opening.norm_mul_sqrt_sq, Nat.cast_add, Nat.cast_one] at h
      simpa only [u, Nat.cast_add, Nat.cast_one] using h
    _ = 2 *
        ((∑ n ∈ Finset.range (k + 2), (n + 1 : ℝ) * u (n + 1)) +
          ∑ n ∈ Finset.range (k + 2), (n : ℝ) * u (n - 1)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := by linarith

theorem openingJacobi_support {v : ℕ → ℂ} {k : ℕ}
    (hv : ∀ n > k, v n = 0) (n : ℕ) (hn : k + 1 < n) : openingJacobi v n = 0 := by
  unfold openingJacobi
  rw [hv _ (by omega), hv _ (by omega), mul_zero, mul_zero, add_zero]

/-- The same single-step bound holds when all coordinates outside a
number cutoff are suppressed. -/
theorem openingJacobi_truncated_norm_sq_le (v w : OpeningFock) {k c : ℕ}
    (hv : ∀ n > k, v n = 0)
    (hw : ∀ n, w n = if n ≤ c then openingJacobi v n else 0) :
    ‖w‖ ^ 2 ≤ 4 * (k + 1 : ℝ) * ‖v‖ ^ 2 := by
  have hws (n : ℕ) (hn : k + 1 < n) : w n = 0 := by
    simp [hw, openingJacobi_support hv n hn]
  rw [opening.norm_sq_eq_cutoff _ hws, opening.norm_sq_eq_cutoff _ hv]
  exact le_trans (Finset.sum_le_sum fun n _ => by
    rw [hw]
    split <;> simp) (opening.sum_jacobi_le _ hv)

theorem openingVacuumPower_norm_sq_bound (k : ℕ) :
    ‖openingVacuumPower k‖ ^ 2 ≤ 4 ^ k * (k ! : ℝ) := by
  induction k with
  | zero => simp [openingNumberState, lp.norm_single]
  | succ k ih =>
    have hc := opening.sum_jacobi_le (openingVacuumPower k)
      (fun n hn => openingVacuumPowerSeq_support k n hn)
    have hc₂ : ‖openingVacuumPower (k + 1)‖ ^ 2 ≤
        4 * (k + 1 : ℝ) * ‖openingVacuumPower k‖ ^ 2 := by
      rw [opening.norm_sq_eq_cutoff _ (fun n hn => openingVacuumPowerSeq_support (k + 1) n hn),
        opening.norm_sq_eq_cutoff _ (fun n hn => openingVacuumPowerSeq_support k n hn)]
      exact hc
    calc
      _ ≤ _ := hc₂
      _ ≤ 4 * (k + 1 : ℝ) * (4 ^ k * (k ! : ℝ)) := by gcongr
      _ = _ := by rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]; ring

/-- Uniform square factorial estimate for the (k)-th vacuum iterate. -/
theorem openingVacuumPower_norm_bound (k : ℕ) :
    ‖openingVacuumPower k‖ ≤ 2 ^ k * Real.sqrt (k ! : ℝ) := by
  have h := openingVacuumPower_norm_sq_bound k
  have hs : (2 ^ k * Real.sqrt (k ! : ℝ)) ^ 2 = 4 ^ k * (k ! : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), ← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 (hs ▸ h)

private theorem opening.summable_pow_div_sqrt_factorial (r : ℝ) (hr : 0 ≤ r) :
    Summable (fun k : ℕ => r ^ k / Real.sqrt (k ! : ℝ)) := by
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  obtain ⟨N, hN⟩ := exists_nat_gt ((2 * r) ^ 2)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hle : 2 * r ≤ Real.sqrt ((n : ℝ) + 1) := by
    have hle' : (2 * r) ^ 2 ≤ (n : ℝ) + 1 := by
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    exact (Real.le_sqrt (by positivity) (by positivity)).2 hle'
  have hp : 0 < Real.sqrt ((n : ℝ) + 1) := by positivity
  have hratio : r / Real.sqrt ((n : ℝ) + 1) ≤ 1 / 2 := by
    apply (div_le_iff₀ hp).2
    linarith
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ r ^ n / Real.sqrt (n ! : ℝ)),
    abs_of_nonneg (by positivity : 0 ≤ r ^ (n + 1) / Real.sqrt ((n + 1) ! : ℝ))]
  rw [pow_succ', Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ,
    Real.sqrt_mul (by positivity : 0 ≤ (n : ℝ) + 1), ← div_mul_div_comm]
  exact mul_le_mul_of_nonneg_right hratio (by positivity)

/-- A scalar summable envelope for the powers of every number cutoff
and for the untruncated vacuum. -/
def openingVacuumTaylorMajorant (z : ℂ) (k : ℕ) : ℝ :=
  (2 * ‖z‖) ^ k / Real.sqrt (k ! : ℝ)

theorem openingVacuumTaylorMajorant_summable (z : ℂ) :
    Summable (openingVacuumTaylorMajorant z) :=
  opening.summable_pow_div_sqrt_factorial _ (by positivity)

theorem openingVacuumTaylorMajorant_bound (z : ℂ) (k : ℕ) (v : OpeningFock)
    (hv : ‖v‖ ≤ 2 ^ k * Real.sqrt (k ! : ℝ)) :
    ‖(z ^ k / (k ! : ℂ)) • v‖ ≤ openingVacuumTaylorMajorant z k := by
  have hs : 0 < Real.sqrt (k ! : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast Nat.factorial_pos k)
  have hs₂ : Real.sqrt (k ! : ℝ) ^ 2 = (k ! : ℝ) := Real.sq_sqrt (by positivity)
  rw [norm_smul, norm_div, norm_pow, Complex.norm_natCast, openingVacuumTaylorMajorant]
  calc
    _ ≤ (‖z‖ ^ k / (k ! : ℝ)) * (2 ^ k * Real.sqrt (k ! : ℝ)) := by gcongr
    _ = _ := by
      rw [mul_pow]
      field_simp
      rw [hs₂]

/-- The unscaled position power series is absolutely summable as a vector
for every complex displacement. -/
theorem openingVacuumTaylorTerm_norm_summable (z : ℂ) :
    Summable (fun k : ℕ => ‖(z ^ k / (k ! : ℂ)) • openingVacuumPower k‖) := by
  exact (openingVacuumTaylorMajorant_summable z).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => openingVacuumTaylorMajorant_bound z k _ (openingVacuumPower_norm_bound k))

/-- The vacuum vector of the oscillator position exponential, realized on
the analytic number-core vector by its norm-convergent Taylor series. -/
def openingVacuumTaylor (z : ℂ) : OpeningFock :=
  ∑' k : ℕ, (z ^ k / (k ! : ℂ)) • openingVacuumPower k

theorem openingVacuumTaylor_hasSum (z : ℂ) :
    HasSum (fun k : ℕ => (z ^ k / (k ! : ℂ)) • openingVacuumPower k)
      (openingVacuumTaylor z) :=
  (openingVacuumTaylorTerm_norm_summable z).of_norm.hasSum

end UV
