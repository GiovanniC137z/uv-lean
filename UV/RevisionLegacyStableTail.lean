import UV.StableNonanalytic

/-! A quantified first correction to the actual four-dimensional
Green–Poisson covariance tail. -/

noncomputable section

open MeasureTheory Filter Set Real Metric

namespace UV

private theorem fifth_power_error {t M : ℝ} (ht : 0 ≤ t) (htM : t ≤ M) (hM : 1 ≤ M) :
    |t ^ 5 - 1| ≤ |t - 1| * 5 * M ^ 4 := by
  have h := abs_pow_sub_pow_le (a := t) (b := (1 : ℝ)) (n := 5)
  simp only [one_pow, Nat.cast_ofNat, abs_of_nonneg ht, abs_one, Nat.reduceSub] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (zero_le_one.trans (le_max_right t 1)) (max_le htM hM) _) (by positivity))

private theorem stablePoisson_difference_bound {a : ℝ} (ha : 0 < a)
    (x y : ScalarMomentum) (hx : 0 < ‖x‖) :
    |stablePoissonKernel a (x - y) - stablePoissonKernel a x| ≤
      ((3 * a / (4 * π ^ 2)) * (5 * a) / ‖x‖ ^ 6) * (1 + ‖y‖ / a) ^ 6 := by
  let r := stablePoissonRadius a x
  let s := stablePoissonRadius a (x - y)
  let M := 1 + ‖y‖ / a
  have hr : 0 < r := stablePoissonRadius_pos ha x
  have hs : 0 < s := stablePoissonRadius_pos ha (x - y)
  have hM : 1 ≤ M := by dsimp [M]; linarith [div_nonneg (norm_nonneg y) ha.le]
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hratio : r / s ≤ M := by
    apply (div_le_iff₀ hs).mpr
    have ht := stablePoissonRadius_triangle a (x - y) y
    simp only [sub_add_cancel] at ht
    have hb : a ≤ s := stablePoissonRadius_ge a _
    have hh := mul_nonneg (div_nonneg (norm_nonneg y) ha.le) (sub_nonneg.mpr hb)
    have hid : (‖y‖ / a) * a = ‖y‖ := div_mul_cancel₀ _ ha.ne'
    change r ≤ (1 + ‖y‖ / a) * s
    change r ≤ s + ‖y‖ at ht
    nlinarith
  have hinv : s⁻¹ ≤ M / r := by
    apply (le_div_iff₀ hr).mpr
    rwa [mul_comm, ← div_eq_mul_inv]
  have hd : |r / s - 1| ≤ ‖y‖ * (M / r) := by
    have he : r / s - 1 = (r - s) * s⁻¹ := by field_simp
    rw [he, abs_mul, abs_of_pos (inv_pos.mpr hs), abs_sub_comm]
    exact mul_le_mul (stablePoissonRadius_sub_abs a x y) hinv (inv_nonneg.mpr hs.le) (norm_nonneg y)
  have hym : ‖y‖ ≤ a * M := by dsimp [M]; rw [mul_add, mul_one, mul_div_cancel₀ _ ha.ne']; linarith
  have hpow := fifth_power_error (div_nonneg hr.le hs.le) hratio hM
  have hpow' : |(r / s) ^ 5 - 1| ≤ 5 * a * M ^ 6 / r := calc
    _ ≤ ‖y‖ * (M / r) * 5 * M ^ 4 := by
      exact hpow.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hd (by norm_num)) (pow_nonneg hM0 _))
    _ ≤ (a * M) * (M / r) * 5 * M ^ 4 := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hym (div_nonneg hM0 hr.le)) (by norm_num)) (pow_nonneg hM0 _)
    _ = _ := by ring
  let K := 3 * a / (4 * π ^ 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have he : stablePoissonKernel a (x - y) - stablePoissonKernel a x =
      (K / r ^ 5) * ((r / s) ^ 5 - 1) := by
    change K / s ^ 5 - K / r ^ 5 = _
    field_simp
  rw [he, abs_mul, abs_of_nonneg (div_nonneg hK (pow_nonneg hr.le _))]
  calc
    _ ≤ (K / r ^ 5) * (5 * a * M ^ 6 / r) :=
      mul_le_mul_of_nonneg_left hpow' (by positivity)
    _ = (K * (5 * a) / r ^ 6) * M ^ 6 := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hM0 6)
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos hx 6)
        (pow_le_pow_left₀ hx.le (stablePoissonRadius_ge_norm a x) 6)

private theorem stablePoisson_asymptotic_bound {a : ℝ} (ha : 0 < a)
    (x : ScalarMomentum) (hx : 0 < ‖x‖) :
    |stablePoissonKernel a x - (3 * a / (4 * π ^ 2)) / ‖x‖ ^ 5| ≤
      (3 * a / (4 * π ^ 2)) * (5 * a) / ‖x‖ ^ 6 := by
  let K := 3 * a / (4 * π ^ 2)
  let r := stablePoissonRadius a x
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hr : 0 < r := stablePoissonRadius_pos ha x
  have hxr : ‖x‖ ≤ r := stablePoissonRadius_ge_norm a x
  have hrx : r ≤ a + ‖x‖ := stablePoissonRadius_le ha.le x
  have ht : ‖x‖ / r ≤ 1 := (div_le_one hr).mpr hxr
  have hdiff : |‖x‖ / r - 1| ≤ a / ‖x‖ := by
    rw [abs_of_nonpos (sub_nonpos.mpr ht), neg_sub,
      show 1 - ‖x‖ / r = (r - ‖x‖) / r by field_simp]
    exact (div_le_div_of_nonneg_right (by linarith : r - ‖x‖ ≤ a) hr.le).trans
      (div_le_div_of_nonneg_left ha.le hx hxr)
  have h := fifth_power_error (div_nonneg hx.le hr.le) ht (le_rfl : (1 : ℝ) ≤ 1)
  have hp : |(‖x‖ / r) ^ 5 - 1| ≤ (a / ‖x‖) * 5 :=
    (by simpa only [one_pow, mul_one] using h : |(‖x‖ / r) ^ 5 - 1| ≤ |‖x‖ / r - 1| * 5).trans
      (mul_le_mul_of_nonneg_right hdiff (by norm_num))
  have he : stablePoissonKernel a x - K / ‖x‖ ^ 5 =
      (K / ‖x‖ ^ 5) * ((‖x‖ / r) ^ 5 - 1) := by
    change K / r ^ 5 - K / ‖x‖ ^ 5 = _
    field_simp
  rw [he, abs_mul, abs_of_nonneg (div_nonneg hK (pow_nonneg hx.le _))]
  exact (mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq (by ring)

private theorem stableGreen_sixth_envelope {a m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    Integrable (fun y : ScalarMomentum => (1 + ‖y‖ / a) ^ 6) (stableGreenMeasure m) := by
  obtain ⟨c, hc, hexp⟩ := stableGreenMeasure_has_exponential_moment hm
  apply (hexp.const_mul (((6 : ℕ).factorial : ℝ) / (c * a) ^ 6 * exp (c * a))).mono'
  · exact ((continuous_const.add (continuous_norm.div_const a)).pow 6).aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_of_nonneg (by positivity)]
    have hpow := pow_mul_exp_neg_le (mul_pos hc ha)
      (show 0 ≤ 1 + ‖y‖ / a by positivity) 6
    have he : (1 + ‖y‖ / a) ^ 6 =
        ((1 + ‖y‖ / a) ^ 6 * exp (-(c * a * (1 + ‖y‖ / a)))) *
          exp (c * a * (1 + ‖y‖ / a)) := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    rw [he]
    calc
      _ ≤ (((6 : ℕ).factorial : ℝ) / (c * a) ^ 6) * exp (c * a * (1 + ‖y‖ / a)) :=
        mul_le_mul_of_nonneg_right hpow (exp_nonneg _)
      _ = _ := by
        rw [show c * a * (1 + ‖y‖ / a) = c * a + c * ‖y‖ by field_simp, Real.exp_add]
        ring

/-- The revised coordinate covariance tail with the literal coefficient and
a uniform inverse-sixth-power error in all directions. -/
theorem revised_stable_coordinate_covariance_tail {a m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ScalarMomentum, 0 < ‖x‖ →
      |stableCoordinateCovariance a m x - (3 * a / (4 * π ^ 2 * m ^ 2)) / ‖x‖ ^ 5| ≤
        C / ‖x‖ ^ 6 := by
  let μ := stableGreenMeasure m
  letI := stableGreenMeasure_finite hm
  let K := 3 * a / (4 * π ^ 2)
  let M : ℝ := ∫ y : ScalarMomentum, (1 + ‖y‖ / a) ^ 6 ∂μ
  have hM : 0 ≤ M := integral_nonneg fun _ => by positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K * (5 * a) * (M + (m ^ 2)⁻¹), by positivity, fun x hx => ?_⟩
  have hΔ : |stableCoordinateCovariance a m x - stablePoissonKernel a x / m ^ 2| ≤
      (K * (5 * a) / ‖x‖ ^ 6) * M := by
    have he : stableCoordinateCovariance a m x - stablePoissonKernel a x / m ^ 2 =
        ∫ y, stablePoissonKernel a (x - y) - stablePoissonKernel a x ∂μ := by
      rw [integral_sub (stableCoordinateConvolution_integrable ha μ x) (integrable_const _)]
      change (∫ y, stablePoissonKernel a (x - y) ∂μ) - stablePoissonKernel a x / m ^ 2 = _
      simp only [integral_const, smul_eq_mul, Measure.real, μ, stableGreenMeasure_real_mass hm]
      ring
    rw [he]
    refine abs_integral_le_integral_abs.trans ?_
    change _ ≤ (K * (5 * a) / ‖x‖ ^ 6) * ∫ y : ScalarMomentum, (1 + ‖y‖ / a) ^ 6 ∂μ
    rw [← integral_const_mul]
    exact integral_mono
      ((stableCoordinateConvolution_integrable ha μ x).sub (integrable_const _)).abs
      ((stableGreen_sixth_envelope ha hm).const_mul _)
      (fun y => stablePoisson_difference_bound ha x y hx)
  have h2 := stablePoisson_asymptotic_bound ha x hx
  have he : (3 * a / (4 * π ^ 2 * m ^ 2)) / ‖x‖ ^ 5 =
      (K / ‖x‖ ^ 5) / m ^ 2 := by dsimp [K]; ring
  rw [he]
  calc
    _ ≤ |stableCoordinateCovariance a m x - stablePoissonKernel a x / m ^ 2| +
        |(stablePoissonKernel a x - K / ‖x‖ ^ 5) / m ^ 2| := by
      have h := abs_add_le (stableCoordinateCovariance a m x - stablePoissonKernel a x / m ^ 2)
        ((stablePoissonKernel a x - K / ‖x‖ ^ 5) / m ^ 2)
      convert h using 2
      ring
    _ ≤ (K * (5 * a) / ‖x‖ ^ 6) * M + (K * (5 * a) / ‖x‖ ^ 6) / m ^ 2 := by
      rw [abs_div, abs_of_nonneg (sq_nonneg m)]
      exact add_le_add hΔ (div_le_div_of_nonneg_right h2 (sq_nonneg m))
    _ = _ := by ring


/-- The explicit square tail used in the manuscript's sixth-moment
subtraction. The cutoff is at the inverse mass. -/
def stableCovarianceTailSquare (a m : ℝ) (x : ScalarMomentum) : ℝ :=
  if m⁻¹ < ‖x‖ then (3 * a / (4 * π ^ 2 * m ^ 2)) ^ 2 / ‖x‖ ^ 10 else 0

private theorem inverse_fifth_tail_integrable {R : ℝ} (hR : 0 < R) :
    Integrable (fun x : ScalarMomentum => (Ioi R).indicator (fun r => (r ^ 5)⁻¹) ‖x‖) := by
  refine (integrable_fun_norm_addHaar (E := ScalarMomentum) volume).mpr ?_
  have hP : IntegrableOn (fun r : ℝ => r ^ (-2 : ℝ)) (Ioi R) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hR
  have hi := (integrable_indicator_iff measurableSet_Ioi).mpr hP
  apply hi.integrableOn.congr_fun _ measurableSet_Ioi
  intro r hr
  have hr0 : 0 < r := hr
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
  by_cases h : R < r
  · rw [Set.indicator_of_mem (show r ∈ Ioi R from h),
      Set.indicator_of_mem (show r ∈ Ioi R from h), Real.rpow_neg hr0.le, Real.rpow_two]
    field_simp
  · rw [Set.indicator_of_notMem (show r ∉ Ioi R from h),
      Set.indicator_of_notMem (show r ∉ Ioi R from h), mul_zero]

/-- Subtracting the explicit square tail leaves an absolutely integrable
sixth coordinate moment. The proof uses the literal covariance and does
not assume a higher moment of it. -/
theorem revised_stable_square_tail_residual_sixth_moment {a m : ℝ}
    (ha : 0 < a) (hm : 0 < m) :
    Integrable (fun x : ScalarMomentum => ‖x‖ ^ 6 *
      (stableCoordinateCovariance a m x ^ 2 - stableCovarianceTailSquare a m x)) := by
  obtain ⟨D, hD, htail⟩ := revised_stable_coordinate_covariance_tail ha hm
  let c := 3 * a / (4 * π ^ 2 * m ^ 2)
  let K := stablePoissonKernel a 0 / m ^ 2
  let R := max 1 m⁻¹
  let f := fun x : ScalarMomentum => ‖x‖ ^ 6 *
    (stableCoordinateCovariance a m x ^ 2 - stableCovarianceTailSquare a m x)
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hK : 0 ≤ K := div_nonneg (stablePoissonKernel_pos ha _).le (sq_nonneg m)
  have hf : Measurable f := by
    dsimp [f, stableCovarianceTailSquare]
    have htest : MeasurableSet {x : ScalarMomentum | m⁻¹ < ‖x‖} :=
      measurableSet_lt measurable_const continuous_norm.measurable
    have hS := (stableCoordinateCovariance_continuous ha hm).measurable
    have hT : Measurable (fun x : ScalarMomentum => if m⁻¹ < ‖x‖ then c ^ 2 / ‖x‖ ^ 10 else 0) :=
      Measurable.piecewise htest (by fun_prop) measurable_const
    fun_prop
  have hout : IntegrableOn f (closedBall (0 : ScalarMomentum) R)ᶜ := by
    apply ((inverse_fifth_tail_integrable hR).const_mul (D * (D + 2 * c))).integrableOn.mono'
      hf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with x hx
    have hr : R < ‖x‖ := by
      simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hx
    have hm' : m⁻¹ < ‖x‖ := (le_max_right _ _).trans_lt hr
    have h1 : 1 ≤ ‖x‖ := (le_max_left _ _).trans hr.le
    have hp : 0 < ‖x‖ := hR.trans hr
    let b := c / ‖x‖ ^ 5
    have hb : 0 ≤ b := by dsimp [b]; positivity
    have hA := stableCoordinateCovariance_nonneg ha m x
    have he : stableCovarianceTailSquare a m x = b ^ 2 := by
      rw [stableCovarianceTailSquare, if_pos hm']
      dsimp [b, c]
      ring
    change ‖f x‖ ≤ (D * (D + 2 * c)) * (Ioi R).indicator (fun r => (r ^ 5)⁻¹) ‖x‖
    rw [Set.indicator_of_mem (show ‖x‖ ∈ Ioi R from hr)]
    dsimp [f]
    rw [abs_mul, abs_of_nonneg (pow_nonneg hp.le 6), he]
    rw [show stableCoordinateCovariance a m x ^ 2 - b ^ 2 =
      (stableCoordinateCovariance a m x - b) * (stableCoordinateCovariance a m x + b) by ring]
    rw [abs_mul, abs_of_nonneg (add_nonneg hA hb)]
    have hdiff : |stableCoordinateCovariance a m x - b| ≤ D / ‖x‖ ^ 6 := htail x hp
    have hden : ‖x‖ ^ 5 ≤ ‖x‖ ^ 6 := by
      change ‖x‖ ^ 5 ≤ ‖x‖ ^ 5 * ‖x‖
      exact le_mul_of_one_le_right (pow_nonneg hp.le _) h1
    have hsum : stableCoordinateCovariance a m x + b ≤ (D + 2 * c) / ‖x‖ ^ 5 := by
      have hdiff' : |stableCoordinateCovariance a m x - b| ≤ D / ‖x‖ ^ 5 :=
        hdiff.trans (div_le_div_of_nonneg_left hD (pow_pos hp _) hden)
      rw [add_div]
      dsimp [b] at *
      rw [mul_div_assoc]
      linarith [le_abs_self (stableCoordinateCovariance a m x - c / ‖x‖ ^ 5)]
    have hbd := mul_le_mul hdiff hsum (add_nonneg hA hb) (div_nonneg hD (pow_nonneg hp.le _))
    refine (mul_le_mul_of_nonneg_left hbd (pow_nonneg hp.le _)).trans_eq ?_
    field_simp
  have hin : IntegrableOn f (closedBall (0 : ScalarMomentum) R) := by
    haveI : IsFiniteMeasure ((volume : Measure ScalarMomentum).restrict (closedBall 0 R)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
    apply (integrable_const (R ^ 6 * (K ^ 2 + c ^ 2 * m ^ 10))).mono' hf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    have hxr : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hcov : stableCoordinateCovariance a m x ^ 2 ≤ K ^ 2 :=
      pow_le_pow_left₀ (stableCoordinateCovariance_nonneg ha m x)
        (stableCoordinateCovariance_le ha hm x) 2
    have hT0 : 0 ≤ stableCovarianceTailSquare a m x := by
      unfold stableCovarianceTailSquare
      split <;> positivity
    have hT : stableCovarianceTailSquare a m x ≤ c ^ 2 * m ^ 10 := by
      by_cases hx' : m⁻¹ < ‖x‖
      · rw [stableCovarianceTailSquare, if_pos hx']
        change c ^ 2 / ‖x‖ ^ 10 ≤ _
        have hpow := pow_le_pow_left₀ (inv_nonneg.mpr hm.le) hx'.le 10
        exact (div_le_div_of_nonneg_left (sq_nonneg c) (pow_pos (inv_pos.mpr hm) _) hpow).trans_eq
          (by rw [inv_pow, div_inv_eq_mul])
      · rw [stableCovarianceTailSquare, if_neg hx']
        positivity
    dsimp [f]
    rw [abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg x) 6)]
    have hs : |stableCoordinateCovariance a m x ^ 2 - stableCovarianceTailSquare a m x| ≤
        K ^ 2 + c ^ 2 * m ^ 10 := calc
      _ ≤ |stableCoordinateCovariance a m x ^ 2| + |stableCovarianceTailSquare a m x| := abs_sub _ _
      _ ≤ _ := by rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg hT0]; exact add_le_add hcov hT
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) hxr 6) hs (abs_nonneg _) (pow_nonneg hR.le _)
  simpa only [union_compl_self, integrableOn_univ] using hin.union hout

end UV
