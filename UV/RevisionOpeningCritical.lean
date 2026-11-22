import UV.RevisionOpening

/-! Exact Poisson variance and the critical `M⁻¹/⁴` upper bound for the
inclusive density. The estimate uses the actual positive channel sum. -/

noncomputable section

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology NNReal Nat

namespace UV

lemma openingPoisson_succ_mul (rate : ℝ≥0) (n : ℕ) :
    poissonPMFReal rate (n + 1) * (n + 1 : ℝ) = (rate : ℝ) * poissonPMFReal rate n := by
  have hs : (n + 1 : ℝ) ≠ 0 := by positivity
  unfold poissonPMFReal
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

lemma openingPoisson_hasSum_first (rate : ℝ≥0) :
    HasSum (fun n : ℕ ↦ poissonPMFReal rate n * (n : ℝ)) (rate : ℝ) := by
  have h := (poissonPMFRealSum rate).mul_left (rate : ℝ)
  rw [mul_one] at h
  have hpred : HasSum (fun n : ℕ ↦ poissonPMFReal rate (n + 1) * ((n + 1 : ℕ) : ℝ)) (rate : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one, openingPoisson_succ_mul] using h
  apply (hasSum_nat_add_iff' 1).mp
  simpa only [Finset.sum_range_one, Nat.cast_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, sub_zero] using hpred

lemma openingPoisson_hasSum_second (rate : ℝ≥0) :
    HasSum (fun n : ℕ ↦ poissonPMFReal rate n * (n : ℝ) ^ 2) ((rate : ℝ) * (rate + 1)) := by
  have h := ((openingPoisson_hasSum_first rate).add (poissonPMFRealSum rate)).mul_left (rate : ℝ)
  have hpred : HasSum (fun n : ℕ ↦ poissonPMFReal rate (n + 1) * ((n + 1 : ℕ) : ℝ) ^ 2)
      ((rate : ℝ) * (rate + 1)) := by
    convert h using 1
    ext n
    push_cast
    calc
      _ = (poissonPMFReal rate (n + 1) * (n + 1 : ℝ)) * (n + 1) := by ring
      _ = _ := by rw [openingPoisson_succ_mul]; ring
  apply (hasSum_nat_add_iff' 1).mp
  simpa only [Finset.sum_range_one, Nat.cast_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, sub_zero] using hpred

theorem openingPoisson_hasSum_variance (rate : ℝ≥0) :
    HasSum (fun n : ℕ ↦ poissonPMFReal rate n * ((n : ℝ) - rate) ^ 2) (rate : ℝ) := by
  have h := ((openingPoisson_hasSum_second rate).sub
    ((openingPoisson_hasSum_first rate).mul_left (2 * rate : ℝ))).add
    ((poissonPMFRealSum rate).mul_left ((rate : ℝ) ^ 2))
  convert h using 1
  · ext n
    ring
  · ring

private theorem opening_sqrt_max_le (d : ℝ) : Real.sqrt (max d 0) ≤ 1 + d ^ 2 := by
  by_cases h : d ≤ 1
  · calc
      _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (max_le h zero_le_one)
      _ ≤ _ := by rw [Real.sqrt_one]; linarith [sq_nonneg d]
  · have hd : 1 < d := lt_of_not_ge h
    rw [max_eq_left (by linarith : 0 ≤ d)]
    calc
      _ ≤ d := (Real.sqrt_le_left (by linarith : 0 ≤ d)).mpr (by nlinarith [mul_nonneg (by linarith : 0 ≤ d - 1) (by linarith : 0 ≤ d)])
      _ ≤ _ := by nlinarith [mul_nonneg (by linarith : 0 ≤ d - 1) (by linarith : 0 ≤ d)]

lemma openingWeight_critical_pointwise {a₀ M n : ℝ} (ha : 0 ≤ a₀) (hM : 0 < M)
    (hn : 0 ≤ n) :
    openingWeight ((n + a₀) / M) ≤
      (3 / 2) / Real.sqrt (Real.sqrt M) * (1 + (n - M) ^ 2 / M) := by
  let s := Real.sqrt M
  let d := (M - n) / s
  have hs : 0 < s := Real.sqrt_pos.mpr hM
  have hs2 : s ^ 2 = M := Real.sq_sqrt hM.le
  by_cases hc : 1 ≤ (n + a₀) / M
  · rw [openingWeight_eq_zero hc]
    positivity
  · have hphase : 1 + (n + a₀) / M / 2 ≤ 3 / 2 := by linarith
    have hin : 1 - (n + a₀) / M ≤ max d 0 / s := by
      calc
        _ = (M - (n + a₀)) / M := by rw [sub_div, div_self hM.ne']
        _ ≤ (M - n) / M := div_le_div_of_nonneg_right (by linarith) hM.le
        _ = d / s := by
          dsimp [d]
          rw [div_div, ← pow_two, hs2]
        _ ≤ _ := div_le_div_of_nonneg_right (le_max_left _ _) hs.le
    have hh : d ^ 2 = (n - M) ^ 2 / M := by
      dsimp [d]
      rw [div_pow, hs2]
      congr 1
      ring
    have hbound : Real.sqrt (1 - (n + a₀) / M) ≤ (1 + (n - M) ^ 2 / M) / Real.sqrt s := by
      calc
        _ ≤ Real.sqrt (max d 0 / s) := Real.sqrt_le_sqrt hin
        _ = Real.sqrt (max d 0) / Real.sqrt s := Real.sqrt_div (le_max_right _ _) _
        _ ≤ _ := div_le_div_of_nonneg_right (hh ▸ opening_sqrt_max_le d) (Real.sqrt_nonneg _)
    rw [openingWeight_eq_of_nonneg (by positivity)]
    calc
      _ ≤ Real.sqrt (1 - (n + a₀) / M) * (3 / 2) :=
        mul_le_mul_of_nonneg_left hphase (Real.sqrt_nonneg _)
      _ ≤ ((1 + (n - M) ^ 2 / M) / Real.sqrt s) * (3 / 2) :=
        mul_le_mul_of_nonneg_right hbound (by norm_num)
      _ = _ := by ring

theorem openingPairDensity_critical_upper {a₀ M : ℝ} (ha : 0 ≤ a₀) (hM : 0 < M) :
    openingPairDensity 1 a₀ M ≤ 3 / Real.sqrt (Real.sqrt M) := by
  let rate : ℝ≥0 := M.toNNReal
  have hv : (rate : ℝ) = M := Real.coe_toNNReal M hM.le
  have hvsum := openingPoisson_hasSum_variance rate
  rw [hv] at hvsum
  have hsum := ((poissonPMFRealSum rate).add (hvsum.div_const M)).mul_left
    ((3 / 2) / Real.sqrt (Real.sqrt M))
  rw [div_self hM.ne'] at hsum
  have hpoint (n : ℕ) : poissonPMFReal rate n * openingWeight ((n + a₀) / M) ≤
      (3 / 2 / Real.sqrt (Real.sqrt M)) * (poissonPMFReal rate n +
        poissonPMFReal rate n * ((n : ℝ) - M) ^ 2 / M) := by
    calc
      _ ≤ poissonPMFReal rate n * ((3 / 2) / Real.sqrt (Real.sqrt M) *
          (1 + ((n : ℝ) - M) ^ 2 / M)) :=
        mul_le_mul_of_nonneg_left (openingWeight_critical_pointwise ha hM (Nat.cast_nonneg n))
          poissonPMFReal_nonneg
      _ = _ := by ring
  have hs := Summable.of_nonneg_of_le (fun n ↦ mul_nonneg poissonPMFReal_nonneg
      (openingWeight_nonneg _)) hpoint hsum.summable
  calc
    openingPairDensity 1 a₀ M = ∑' n : ℕ,
        poissonPMFReal rate n * openingWeight ((n + a₀) / M) := by simp [openingPairDensity, rate]
    _ ≤ _ := Summable.tsum_le_tsum hpoint hs hsum.summable
    _ = _ := by rw [hsum.tsum_eq]; ring

/-- The critical upper bound alone suffices for the unsubtracted tail.
This estimate is independent of the central limit asymptotic. -/
theorem openingPairDensity_critical_tail {a₀ : ℝ} (ha : 0 ≤ a₀) :
    IntegrableOn (fun M ↦ openingPairDensity 1 a₀ M / M) (Ioi 1) := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-5 / 4 : ℝ) < -1)
    zero_lt_one).const_mul (3 : ℝ)
  apply hi.mono' (((openingPairDensity_measurable 1 a₀).div measurable_id).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with M hM
  have hM0 : 0 < M := zero_lt_one.trans hM
  have hs : Real.sqrt (Real.sqrt M) = M ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow (Real.sqrt M), ← Real.rpow_div_two_eq_sqrt (1 / 2) hM0.le]
    norm_num
  change ‖openingPairDensity 1 a₀ M / M‖ ≤ 3 * M ^ (-5 / 4 : ℝ)
  rw [Real.norm_of_nonneg (div_nonneg (openingPairDensity_nonneg 1 a₀ M) hM0.le)]
  calc
    _ ≤ (3 / Real.sqrt (Real.sqrt M)) / M :=
      div_le_div_of_nonneg_right (openingPairDensity_critical_upper ha hM0) hM0.le
    _ = _ := by
      have hp : M ^ (1 / 4 : ℝ) * M = M ^ (1 / 4 + 1 : ℝ) := by
        rw [Real.rpow_add hM0, Real.rpow_one]
      rw [hs, div_div, hp, show (-5 / 4 : ℝ) = -(1 / 4 + 1) by norm_num,
        Real.rpow_neg hM0.le, div_eq_mul_inv]

end UV
