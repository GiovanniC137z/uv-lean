import UV.Subordination

noncomputable section
open MeasureTheory Set Real Filter
open scoped ENNReal Topology

namespace UV

def gaussianEvenMoment (b : ℝ) (n : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0, x ^ (2 * n) * subordinationGaussian b x

theorem gaussianEvenMoment_integrable (b : ℝ) (n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ (2 * n) * subordinationGaussian b x) (Ioi 0) := by
  have hg := integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num)
    (s := (2 * n : ℕ)) (by exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _))
  simp only [Real.rpow_natCast, neg_one_mul] at hg
  refine hg.mono' (by unfold subordinationGaussian; fun_prop) ?_
  filter_upwards with x
  unfold subordinationGaussian
  have hpow : 0 ≤ x ^ (2 * n) := by rw [pow_mul]; positivity
  rw [Real.norm_of_nonneg (mul_nonneg hpow (Real.exp_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ hpow
  apply Real.exp_le_exp.mpr
  have h := div_nonneg (sq_nonneg b) (sq_nonneg x)
  linarith

theorem subordinationGaussian_le_one (b x : ℝ) : subordinationGaussian b x ≤ 1 := by
  unfold subordinationGaussian
  apply Real.exp_le_one_iff.mpr
  have h := div_nonneg (sq_nonneg b) (sq_nonneg x)
  nlinarith [sq_nonneg x]

theorem gaussianOddProduct_continuous_zero (b : ℝ) (n : ℕ) :
    ContinuousWithinAt (fun x : ℝ => x ^ (n + 1) * subordinationGaussian b x) (Ici 0) 0 := by
  change Tendsto _ _ (𝓝 _)
  simp only [zero_pow (Nat.succ_ne_zero n), zero_mul]
  apply squeeze_zero' (g := fun x : ℝ => x ^ (n + 1))
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_nonneg (pow_nonneg hx _) (Real.exp_nonneg _)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_le_of_le_one_right (pow_nonneg hx _) (subordinationGaussian_le_one b x)
  have h : Tendsto (fun x : ℝ => x ^ (n + 1)) (𝓝 0) (𝓝 0) := by
    have h : ContinuousAt (fun x : ℝ => x ^ (n + 1)) 0 := by fun_prop
    simpa only [zero_pow (Nat.succ_ne_zero n)] using h.tendsto
  exact h.mono_left nhdsWithin_le_nhds

theorem gaussianOddProduct_tendsto_zero (b : ℝ) (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ (n + 1) * subordinationGaussian b x) atTop (𝓝 0) := by
  apply squeeze_zero' (g := fun x : ℝ => x ^ (n + 1) * Real.exp (-x))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact mul_nonneg (pow_nonneg hx _) (Real.exp_nonneg _)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith) _)
    unfold subordinationGaussian
    apply Real.exp_le_exp.mpr
    have h := div_nonneg (sq_nonneg b) (sq_nonneg x)
    have hs : x ≤ x ^ 2 := by nlinarith
    linarith
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((n + 1 : ℕ) : ℝ) 1 (by norm_num)
  simpa only [Real.rpow_natCast, neg_one_mul] using h

theorem subordinationGaussian_hasDerivAt (b : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (subordinationGaussian b)
      ((-2 * x + 2 * b ^ 2 / x ^ 3) * subordinationGaussian b x) x := by
  have hq := (hasDerivAt_const x (b ^ 2)).div ((hasDerivAt_id x).pow 2)
    (pow_ne_zero 2 hx.ne')
  have h := (((hasDerivAt_id x).pow 2).add hq).neg.exp
  convert h using 1
  dsimp [subordinationGaussian]
  field_simp [ne_of_gt (show 0 < x from hx)]
  ring

theorem gaussianOddProduct_hasDerivAt (b : ℝ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y ^ (n + 1) * subordinationGaussian b y)
      (((n + 1 : ℕ) : ℝ) * x ^ n * subordinationGaussian b x +
        x ^ (n + 1) * ((-2 * x + 2 * b ^ 2 / x ^ 3) * subordinationGaussian b x)) x := by
  convert ((hasDerivAt_id x).pow (n + 1)).mul (subordinationGaussian_hasDerivAt b hx) using 1
  simp only [Nat.add_sub_cancel, mul_one, id_eq, Pi.pow_apply]

theorem gaussianEvenMoment_one {b : ℝ} (hb : 0 < b) :
    gaussianEvenMoment b 1 = (b + 1 / 2) * gaussianEvenMoment b 0 := by
  have h0 := gaussianEvenMoment_integrable b 0
  have h1 := gaussianEvenMoment_integrable b 1
  norm_num only [Nat.mul_zero, Nat.mul_one, pow_zero, one_mul] at h0 h1
  have hw := subordinationGaussian_weighted_integrable hb
  have hi := (h0.sub (h1.const_mul 2)).add (hw.const_mul (2 * b))
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt
      (fun x : ℝ => x ^ (0 + 1) * subordinationGaussian b x)
      (subordinationGaussian b x - 2 * (x ^ 2 * subordinationGaussian b x) +
        (2 * b) * ((b / x ^ 2) * subordinationGaussian b x)) x := by
    intro x hx
    convert gaussianOddProduct_hasDerivAt b 0 hx using 1
    norm_num only [Nat.cast_zero, Nat.cast_one, zero_add, pow_zero, pow_one, one_mul]
    field_simp [ne_of_gt (show 0 < x from hx)]
    ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (gaussianOddProduct_continuous_zero b 0) hd hi (gaussianOddProduct_tendsto_zero b 0)
  have ha := integral_add (h0.sub (h1.const_mul 2)) (hw.const_mul (2 * b))
  have hs := integral_sub h0 (h1.const_mul 2)
  simp only [Pi.sub_apply] at ha
  rw [ha, hs, integral_const_mul, integral_const_mul,
    subordinationGaussian_inversion_integral hb] at h
  norm_num at h
  unfold gaussianEvenMoment
  norm_num only [Nat.mul_one, Nat.mul_zero, pow_zero, one_mul]
  linarith

theorem gaussianEvenMoment_two (b : ℝ) :
    gaussianEvenMoment b 2 = (3 / 2 : ℝ) * gaussianEvenMoment b 1 +
      b ^ 2 * gaussianEvenMoment b 0 := by
  have h0 := gaussianEvenMoment_integrable b 0
  have h1 := gaussianEvenMoment_integrable b 1
  have h2 := gaussianEvenMoment_integrable b 2
  norm_num only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul, pow_zero, one_mul] at h0 h1 h2
  have hi := ((h1.const_mul 3).sub (h2.const_mul 2)).add (h0.const_mul (2 * b ^ 2))
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt
      (fun x : ℝ => x ^ (2 + 1) * subordinationGaussian b x)
      (3 * (x ^ 2 * subordinationGaussian b x) - 2 * (x ^ 4 * subordinationGaussian b x) +
        (2 * b ^ 2) * subordinationGaussian b x) x := by
    intro x hx
    convert gaussianOddProduct_hasDerivAt b 2 hx using 1
    norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
    field_simp [ne_of_gt (show 0 < x from hx)]
    ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (gaussianOddProduct_continuous_zero b 2) hd hi (gaussianOddProduct_tendsto_zero b 2)
  have ha := integral_add ((h1.const_mul 3).sub (h2.const_mul 2)) (h0.const_mul (2 * b ^ 2))
  have hs := integral_sub (h1.const_mul 3) (h2.const_mul 2)
  simp only [Pi.sub_apply] at ha
  rw [ha, hs, integral_const_mul, integral_const_mul, integral_const_mul] at h
  norm_num only [Nat.reduceAdd, zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_mul, sub_zero] at h
  unfold gaussianEvenMoment
  norm_num only [Nat.mul_one, Nat.mul_zero, Nat.reduceMul, pow_zero, one_mul]
  linarith

theorem gaussianEvenMoment_three (b : ℝ) :
    gaussianEvenMoment b 3 = (5 / 2 : ℝ) * gaussianEvenMoment b 2 +
      b ^ 2 * gaussianEvenMoment b 1 := by
  have h1 := gaussianEvenMoment_integrable b 1
  have h2 := gaussianEvenMoment_integrable b 2
  have h3 := gaussianEvenMoment_integrable b 3
  norm_num only [Nat.mul_one, Nat.reduceMul] at h1 h2 h3
  have hi := ((h2.const_mul 5).sub (h3.const_mul 2)).add (h1.const_mul (2 * b ^ 2))
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt
      (fun x : ℝ => x ^ (4 + 1) * subordinationGaussian b x)
      (5 * (x ^ 4 * subordinationGaussian b x) - 2 * (x ^ 6 * subordinationGaussian b x) +
        (2 * b ^ 2) * (x ^ 2 * subordinationGaussian b x)) x := by
    intro x hx
    convert gaussianOddProduct_hasDerivAt b 4 hx using 1
    norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
    field_simp [ne_of_gt (show 0 < x from hx)]
    ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (gaussianOddProduct_continuous_zero b 4) hd hi (gaussianOddProduct_tendsto_zero b 4)
  have ha := integral_add ((h2.const_mul 5).sub (h3.const_mul 2)) (h1.const_mul (2 * b ^ 2))
  have hs := integral_sub (h2.const_mul 5) (h3.const_mul 2)
  simp only [Pi.sub_apply] at ha
  rw [ha, hs, integral_const_mul, integral_const_mul, integral_const_mul] at h
  norm_num only [Nat.reduceAdd, zero_pow (by norm_num : (5 : ℕ) ≠ 0), zero_mul, sub_zero] at h
  unfold gaussianEvenMoment
  norm_num only [Nat.mul_one, Nat.reduceMul]
  linarith

def oqedNatMomentReal (μ : ℝ) (n : ℕ) : ℝ :=
  ∫ τ : ℝ in Ioi 0, τ ^ (-(n : ℝ)) * oqedDensity μ τ

theorem oqedNatMomentReal_integrable (μ : ℝ) (n : ℕ) :
    IntegrableOn (fun τ : ℝ => τ ^ (-(n : ℝ)) * oqedDensity μ τ) (Ioi 0) :=
  oqedWeightedDensity_integrable μ (by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith)

theorem oqedNatMomentReal_eq_inverseMoment (μ : ℝ) (n : ℕ) :
    inverseMoment (oqedMeasure μ) n = ENNReal.ofReal (oqedNatMomentReal μ n) := by
  rw [oqedInverseMoment_eq]
  symm
  apply ofReal_integral_eq_lintegral_ofReal (oqedNatMomentReal_integrable μ n)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  exact mul_nonneg (Real.rpow_nonneg hτ.le _) (oqedDensity_nonneg μ τ hτ.le)

theorem oqedNatMomentReal_rpow_change (μ : ℝ) (n : ℕ) (x : ℝ) (hx : 0 < x) :
    (|(-2 : ℝ)| * x ^ ((-2 : ℝ) - 1)) •
      ((x ^ (-2 : ℝ)) ^ (-(n : ℝ)) * oqedDensity μ (x ^ (-2 : ℝ))) =
        2 * (Real.exp μ / (2 * Real.sqrt Real.pi)) *
          (x ^ (2 * n) * subordinationGaussian (μ / 2) (x / 2)) := by
  have hp : (x ^ (-2 : ℝ)) ^ (-(n : ℝ)) = x ^ (2 * n) := by
    rw [← Real.rpow_mul hx.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  rw [hp]
  unfold oqedDensity
  simp only [smul_eq_mul]
  calc
    _ = (Real.exp μ / (2 * Real.sqrt Real.pi)) * x ^ (2 * n) *
        ((|(-2 : ℝ)| * x ^ ((-2 : ℝ) - 1)) • oqedDensityCore μ (x ^ (-2 : ℝ))) := by
      rw [smul_eq_mul]
      ring
    _ = _ := by rw [subordinationCore_rpow_change μ x hx]; ring

theorem oqedNatMomentReal_eq_gaussian (μ : ℝ) (n : ℕ) :
    oqedNatMomentReal μ n =
      4 * (Real.exp μ / (2 * Real.sqrt Real.pi)) * (4 : ℝ) ^ n *
        gaussianEvenMoment (μ / 2) n := by
  unfold oqedNatMomentReal
  calc
    _ = ∫ x : ℝ in Ioi 0, (|(-2 : ℝ)| * x ^ ((-2 : ℝ) - 1)) •
        ((x ^ (-2 : ℝ)) ^ (-(n : ℝ)) * oqedDensity μ (x ^ (-2 : ℝ))) :=
      (integral_comp_rpow_Ioi
        (fun τ : ℝ => τ ^ (-(n : ℝ)) * oqedDensity μ τ) (p := -2) (by norm_num)).symm
    _ = ∫ x : ℝ in Ioi 0, 2 * (Real.exp μ / (2 * Real.sqrt Real.pi)) *
          (x ^ (2 * n) * subordinationGaussian (μ / 2) (x / 2)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      exact fun x hx => oqedNatMomentReal_rpow_change μ n x hx
    _ = (2 * (Real.exp μ / (2 * Real.sqrt Real.pi))) * (4 : ℝ) ^ n *
        (∫ x : ℝ in Ioi 0, (x / 2) ^ (2 * n) * subordinationGaussian (μ / 2) (x / 2)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hpow : x ^ (2 * n) = (4 : ℝ) ^ n * (x / 2) ^ (2 * n) := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← mul_pow]
        congr 1
        ring
      dsimp only
      rw [hpow]
      ring
    _ = _ := by
      have hs := integral_comp_mul_right_Ioi
        (fun x : ℝ => x ^ (2 * n) * subordinationGaussian (μ / 2) x) 0
        (b := (2 : ℝ)⁻¹) (by norm_num)
      norm_num only [zero_mul, inv_inv, smul_eq_mul] at hs
      simp only [div_eq_mul_inv, one_mul] at hs ⊢
      rw [hs]
      unfold gaussianEvenMoment
      ring

theorem oqedNatMomentReal_zero {μ : ℝ} (hμ : 0 ≤ μ) : oqedNatMomentReal μ 0 = 1 := by
  unfold oqedNatMomentReal
  simp only [Nat.cast_zero, neg_zero, Real.rpow_zero, one_mul]
  exact oqedDensity_integral hμ

theorem oqedGaussian_normalization {μ : ℝ} (hμ : 0 ≤ μ) :
    4 * (Real.exp μ / (2 * Real.sqrt Real.pi)) * gaussianEvenMoment (μ / 2) 0 = 1 := by
  have h := oqedNatMomentReal_eq_gaussian μ 0
  rw [oqedNatMomentReal_zero hμ] at h
  simpa only [pow_zero, mul_one] using h.symm

theorem oqedNatMomentReal_one {μ : ℝ} (hμ : 0 < μ) :
    oqedNatMomentReal μ 1 = 2 * (1 + μ) := by
  rw [oqedNatMomentReal_eq_gaussian, gaussianEvenMoment_one (half_pos hμ)]
  calc
    _ = (2 * (1 + μ)) *
        (4 * (Real.exp μ / (2 * Real.sqrt Real.pi)) * gaussianEvenMoment (μ / 2) 0) := by ring
    _ = _ := by rw [oqedGaussian_normalization hμ.le, mul_one]

theorem oqedNatMomentReal_two {μ : ℝ} (hμ : 0 < μ) :
    oqedNatMomentReal μ 2 = 4 * (μ ^ 2 + 3 * μ + 3) := by
  rw [oqedNatMomentReal_eq_gaussian, gaussianEvenMoment_two,
    gaussianEvenMoment_one (half_pos hμ)]
  calc
    _ = (4 * (μ ^ 2 + 3 * μ + 3)) *
        (4 * (Real.exp μ / (2 * Real.sqrt Real.pi)) * gaussianEvenMoment (μ / 2) 0) := by ring
    _ = _ := by rw [oqedGaussian_normalization hμ.le, mul_one]

theorem oqedNatMomentReal_three {μ : ℝ} (hμ : 0 < μ) :
    oqedNatMomentReal μ 3 = 8 * (μ ^ 3 + 6 * μ ^ 2 + 15 * μ + 15) := by
  rw [oqedNatMomentReal_eq_gaussian, gaussianEvenMoment_three, gaussianEvenMoment_two,
    gaussianEvenMoment_one (half_pos hμ)]
  calc
    _ = (8 * (μ ^ 3 + 6 * μ ^ 2 + 15 * μ + 15)) *
        (4 * (Real.exp μ / (2 * Real.sqrt Real.pi)) * gaussianEvenMoment (μ / 2) 0) := by ring
    _ = _ := by rw [oqedGaussian_normalization hμ.le, mul_one]

/-- The first exact inverse moment of the actual tempered stable-half measure. -/
theorem oqedInverseMoment_one {μ : ℝ} (hμ : 0 ≤ μ) :
    inverseMoment (oqedMeasure μ) 1 = ENNReal.ofReal (2 * (1 + μ)) := by
  rcases eq_or_lt_of_le hμ with heq | hpos
  · subst μ
    rw [oqedInverseMoment_zero_one]
    norm_num
  · have h := oqedNatMomentReal_eq_inverseMoment μ 1
    norm_num only [Nat.cast_one] at h
    rw [h, oqedNatMomentReal_one hpos]

theorem oqedInverseMoment_two {μ : ℝ} (hμ : 0 ≤ μ) :
    inverseMoment (oqedMeasure μ) 2 = ENNReal.ofReal (4 * (μ ^ 2 + 3 * μ + 3)) := by
  rcases eq_or_lt_of_le hμ with heq | hpos
  · subst μ
    rw [oqedInverseMoment_zero_two]
    norm_num
  · have h := oqedNatMomentReal_eq_inverseMoment μ 2
    norm_num only [Nat.cast_ofNat] at h
    rw [h, oqedNatMomentReal_two hpos]

theorem oqedInverseMoment_three {μ : ℝ} (hμ : 0 ≤ μ) :
    inverseMoment (oqedMeasure μ) 3 =
      ENNReal.ofReal (8 * (μ ^ 3 + 6 * μ ^ 2 + 15 * μ + 15)) := by
  rcases eq_or_lt_of_le hμ with heq | hpos
  · subst μ
    rw [oqedInverseMoment_zero_three]
    norm_num
  · have h := oqedNatMomentReal_eq_inverseMoment μ 3
    norm_num only [Nat.cast_ofNat] at h
    rw [h, oqedNatMomentReal_three hpos]

end UV
