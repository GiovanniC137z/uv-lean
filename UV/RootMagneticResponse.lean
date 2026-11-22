import UV.Obstructions
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The normal, vector and ghost traces of the specified charged root pair.
The scalar Landau levels and their degeneracy are the inputs of the trace
calculation. The lower endpoint tends to zero at fixed upper proper time. -/

noncomputable section

namespace UV.RootMagnetic

open Filter MeasureTheory Real Set
open scoped Topology Interval

theorem landau_level_sum {x : ℝ} (hx : 0 < x) :
    (2*x) * ∑' j : ℕ, exp (-((2*(j:ℝ)+1)*x)) = x/sinh x := by
  have he (j : ℕ) : exp (-((2*(j:ℝ)+1)*x)) = exp (-x) * (exp (-2*x))^j := by
    rw [← exp_nat_mul, ← exp_add]; congr 1; ring
  simp_rw [he, tsum_mul_left]
  rw [tsum_geometric_of_lt_one (exp_nonneg _) (exp_lt_one_iff.mpr (by linarith))]
  have hshift : exp (-2*x) = exp (-x) / exp x := by rw [← exp_sub]; congr 1; ring
  have he : 1 - exp (-x)/exp x = (exp x - exp (-x))/exp x := by field_simp
  have H : exp (-x) * exp x = 1 := by rw [← exp_add]; simp
  rw [hshift, he, inv_div, ← mul_div_assoc, H, sinh_eq, div_div_eq_mul_div]
  ring

def rootSpinGhostTrace (x : ℝ) : ℝ := 2 * ((exp (2*x) + exp (-(2*x)) + 3)/2 - 1)

theorem root_spin_ghost_trace (x : ℝ) : rootSpinGhostTrace x = 1 + 2*cosh (2*x) := by
  simp only [rootSpinGhostTrace, cosh_eq]; ring

private def cubicNumerator (x : ℝ) := x*(1+2*cosh (2*x))-3*sinh x

private theorem cubic_coefficient : Tendsto (fun x : ℝ => cubicNumerator x / x^3) (𝓝[≠] 0) (𝓝 (7/2)) := by
  let F (x : ℝ) := 1 + 2*cosh (2*x) + 4*x*sinh (2*x) - 3*cosh x
  let G (x : ℝ) := 8*sinh (2*x) + 8*x*cosh (2*x) - 3*sinh x
  let H (x : ℝ) := 24*cosh (2*x) + 16*x*sinh (2*x) - 3*cosh x
  have dx (x : ℝ) : HasDerivAt (fun y : ℝ => 2*y) 2 x := by simpa using (hasDerivAt_id x).const_mul 2
  have dF (x : ℝ) : HasDerivAt cubicNumerator (F x) x := by
    convert ((hasDerivAt_id x).mul ((hasDerivAt_const x 1).add ((dx x).cosh.const_mul 2))).sub
      ((hasDerivAt_sinh x).const_mul 3) using 1
    dsimp [F, cubicNumerator]
    ring
  have dG (x : ℝ) : HasDerivAt F (G x) x := by
    convert (((hasDerivAt_const x 1).add ((dx x).cosh.const_mul 2)).add
      (((hasDerivAt_id x).const_mul 4).mul (dx x).sinh)).sub ((hasDerivAt_cosh x).const_mul 3) using 1
    dsimp [F,G]
    ring
  have dH (x : ℝ) : HasDerivAt G (H x) x := by
    convert (((dx x).sinh.const_mul 8).add (((hasDerivAt_id x).const_mul 8).mul (dx x).cosh)).sub
      ((hasDerivAt_sinh x).const_mul 3) using 1
    dsimp [G,H]
    ring
  have hz {f : ℝ → ℝ} (hf : Continuous f) (h : f 0 = 0) : Tendsto f (𝓝[≠] 0) (𝓝 0) := by
    simpa only [h] using (hf.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hR : Tendsto (fun x => H x / 6) (𝓝[≠] 0) (𝓝 (7/2:ℝ)) := by
    have hc : Continuous (fun x => H x / 6) := by unfold H; fun_prop
    have hz' : H 0 / 6 = 7/2 := by norm_num [H]
    simpa only [hz'] using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hne : ∀ᶠ x : ℝ in 𝓝[≠] 0, x ≠ 0 := self_mem_nhdsWithin
  have h₂ : Tendsto (fun x => G x / (6*x)) (𝓝[≠] 0) (𝓝 (7/2:ℝ)) := by
    refine HasDerivAt.lhopital_zero_nhdsNE (Eventually.of_forall dH) (Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun _ => by norm_num) (hz (by unfold G; fun_prop) (by norm_num [G])) (hz (by fun_prop) (by norm_num)) hR
    simpa using (hasDerivAt_id x).const_mul 6
  have h₁ : Tendsto (fun x => F x / (3*x^2)) (𝓝[≠] 0) (𝓝 (7/2:ℝ)) := by
    refine HasDerivAt.lhopital_zero_nhdsNE (Eventually.of_forall dG) (Eventually.of_forall fun x => ?_)
      (hne.mono fun _ h => mul_ne_zero (by norm_num) h) (hz (by unfold F; fun_prop) (by norm_num [F])) (hz (by fun_prop) (by norm_num)) h₂
    convert (hasDerivAt_pow 2 x).const_mul 3 using 1
    norm_num
    ring
  refine HasDerivAt.lhopital_zero_nhdsNE (Eventually.of_forall dF) (Eventually.of_forall fun x => ?_)
    (hne.mono fun _ h => mul_ne_zero (by norm_num) (pow_ne_zero _ h)) (hz (by unfold cubicNumerator; fun_prop) (by norm_num [cubicNumerator]))
    (hz (continuous_pow 3) (by norm_num)) h₁
  simpa using hasDerivAt_pow 3 x

/-- Zero-field subtraction with the scalar heat factor continuously extended. -/
def heatBracket (x : ℝ) : ℝ := if x = 0 then 0 else x/sinh x * rootSpinGhostTrace x - 3

theorem root_heat_quadratic_coefficient : Tendsto (fun x => heatBracket x / x^2) (𝓝[≠] (0:ℝ)) (𝓝 (7/2)) := by
  have hs : Tendsto (fun x : ℝ => x⁻¹*sinh x) (𝓝[≠] 0) (𝓝 1) := by
    simpa [smul_eq_mul] using (Real.hasDerivAt_sinh 0).tendsto_slope_zero
  have h := cubic_coefficient.div hs (by norm_num)
  rw [div_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : x ≠ 0 := hx
  change (cubicNumerator x / x^3)/(x⁻¹ * sinh x) = heatBracket x/x^2
  simp only [heatBracket, if_neg hx', root_spin_ghost_trace, cubicNumerator]
  field_simp [hx', sinh_ne_zero.mpr hx']

private theorem heat_bracket_neg (x : ℝ) : heatBracket (-x) = heatBracket x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [heatBracket, hx, root_spin_ghost_trace, mul_neg]

/-- Scalar Landau multiplicity |B|/(2π) per unit area, the two free momentum
coordinates, both roots, and the vector/normal/ghost statistics at finite t. -/
def rootLevelHeat (B t v : ℝ) : ℝ := if B = 0 then 0 else
  exp (-t*v^2) * ((|B|/(2*Real.pi)) * (∑' j : ℕ, exp (-((2*(j:ℝ)+1)*(|B| * t)))) /
    (4*Real.pi*t) * rootSpinGhostTrace (|B| * t) - 3/(4*Real.pi*t)^2)

theorem root_landau_heat_difference (B v : ℝ) {t : ℝ} (ht : 0 < t) :
    rootLevelHeat B t v = exp (-t*v^2)/(4*Real.pi*t)^2 * heatBracket (B*t) := by
  by_cases hB : B = 0
  · simp [hB, rootLevelHeat, heatBracket]
  · have hx := mul_pos (abs_pos.mpr hB) ht
    have he : heatBracket (B*t) = heatBracket (|B| * t) := by
      rcases lt_or_gt_of_ne hB with h | h
      · rw [abs_of_neg h, neg_mul, heat_bracket_neg]
      · rw [abs_of_pos h]
    have hsum := (eq_div_iff (by positivity : 2*(|B| * t) ≠ 0)).mpr (by
      simpa only [mul_comm (2*(|B| * t))] using landau_level_sum hx)
    rw [rootLevelHeat, if_neg hB, he, heatBracket, if_neg hx.ne', hsum]
    field_simp [ht.ne', pi_ne_zero, abs_ne_zero.mpr hB, sinh_ne_zero.mpr hx.ne']
    ring

private def quadraticReadout := Function.update (fun x => heatBracket x / x^2) 0 (7/2 : ℝ)

private theorem quadratic_readout_continuous : Continuous quadraticReadout := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x; exact continuousAt_update_same.mpr root_heat_quadratic_coefficient
  · have hne := eventually_ne_nhds hx
    apply ContinuousAt.congr_of_eventuallyEq (f := fun y : ℝ => (y/sinh y * rootSpinGhostTrace y - 3)/y^2)
    · unfold rootSpinGhostTrace; fun_prop (disch := first | assumption | exact sinh_ne_zero.mpr hx | positivity)
    · exact hne.mono fun y hy => by simp only [quadraticReadout, Function.update_of_ne hy, heatBracket, if_neg hy]

/-- The lower and upper bounds define the finite proper-time interval before
extracting the B² coefficient. -/
def relativeRootAction (v ε T B : ℝ) : ℝ :=
  ∫ t in Ioc ε T, -(exp (-t*v^2) / (4*Real.pi*t)^2) * heatBracket (B*t) / t

/-- Coefficient of the integrated root-pair heat response for every fixed v. -/
theorem integrated_root_response (v : ℝ) {ε T : ℝ} (hε : 0 < ε) (hT : ε < T) :
    Tendsto (fun B => relativeRootAction v ε T B / B^2) (𝓝[≠] (0:ℝ))
      (𝓝 (-(7/(2*(4*Real.pi)^2)) * ∫ t in Ioc ε T, exp (-t*v^2) / t)) := by
  let W (t : ℝ) := -(exp (-t*v^2) / ((4*Real.pi)^2 * t))
  let K := (volume : Measure ℝ).restrict (Ioc ε T)
  have hW : ContinuousOn W (Icc ε T) := by
    apply ContinuousOn.neg
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    exact fun t ht => mul_ne_zero (pow_ne_zero _ (mul_ne_zero (by norm_num) pi_ne_zero)) (hε.trans_le ht.1).ne'
  have hi : Integrable W K := (hW.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn quadratic_readout_continuous.continuousOn
  have hT₀ := hε.trans hT
  have H := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[≠] (0:ℝ)) (μ := K)
    (F := fun B t => W t * quadraticReadout (B*t)) (f := fun t => W t * (7/2)) (fun t => ‖W t‖*C) ?_ ?_ (hi.norm.mul_const C) ?_
  · have he : (∫ t, W t * (7/2) ∂K) = -(7/(2*(4*Real.pi)^2)) * ∫ t in Ioc ε T, exp (-t*v^2)/t := by
      rw [← integral_const_mul]; apply integral_congr_ae
      exact Eventually.of_forall fun t => by dsimp only [W]; ring
    rw [he] at H
    refine H.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with B hB
    have hB' : B ≠ 0 := hB
    rw [relativeRootAction, ← integral_div]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have ht' := hε.trans ht.1
    dsimp only [W]
    rw [quadraticReadout, Function.update_of_ne (mul_ne_zero hB' ht'.ne')]
    ring
  · refine Eventually.of_forall fun B => hi.aestronglyMeasurable.mul ?_
    exact (quadratic_readout_continuous.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · have hn : ∀ᶠ B : ℝ in 𝓝 (0 : ℝ), |B| < 1 := continuous_abs.continuousAt (Iio_mem_nhds (by norm_num : |(0:ℝ)| < 1))
    have near := hn.filter_mono (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
    filter_upwards [near] with B hB
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht' := hε.trans ht.1
    have hb : |B*t| ≤ T := by rw [abs_mul, abs_of_pos ht']; exact (mul_le_of_le_one_left ht'.le hB.le).trans ht.2
    exact (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_left (hC _ (abs_le.mp hb)) (norm_nonneg _))
  · exact Eventually.of_forall fun t => by
      have h : Tendsto (fun B : ℝ => quadraticReadout (B*t)) (𝓝[≠] 0) (𝓝 (quadraticReadout (0*t))) :=
        (quadratic_readout_continuous.comp (continuous_id.mul continuous_const)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have hzero : quadraticReadout ((0:ℝ)*t) = 7/2 := by rw [zero_mul, quadraticReadout, Function.update_self]
      rw [hzero] at h
      exact h.const_mul (W t)

/-- Each term of the proper-time observable uses the same root-pair heat trace. -/
theorem root_level_action_response (v : ℝ) {ε T : ℝ} (hε : 0 < ε) (hT : ε < T) :
    Tendsto (fun B => (∫ t in Ioc ε T, -rootLevelHeat B t v / t) / B^2) (𝓝[≠] (0 : ℝ))
      (𝓝 (-(7/(2*(4*Real.pi)^2)) * ∫ t in Ioc ε T, exp (-t*v^2)/t)) := by
  apply (integrated_root_response v hε hT).congr
  intro B
  unfold relativeRootAction
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [root_landau_heat_difference B v (hε.trans ht.1)]
  ring

/-- At every finite normal background the absolute proper-time cost is infinite. -/
theorem root_proper_time_not_integrable (v : ℝ) {T : ℝ} (hT : 0 < T) :
    ¬IntegrableOn (fun t : ℝ => exp (-t*v^2)/t) (Ioc 0 T) := by
  intro hi
  have hL : IntegrableOn (fun t : ℝ => t^(-1:ℝ)) (Ioc 0 T) := by
    apply (hi.const_mul (exp (T*v^2))).mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.rpow_neg_one, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht.1)]
    have h : 1 ≤ exp (T*v^2) * exp (-t*v^2) := by
      rw [← exp_add, one_le_exp_iff]; nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sq_nonneg v)]
    calc
      t⁻¹ = 1/t := (one_div t).symm
      _ ≤ _ := by rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right h ht.1.le
  exact (lt_irrefl (-1 : ℝ)) ((intervalIntegral.integrableOn_Ioo_rpow_iff hT).mp (hL.mono_set Ioo_subset_Ioc_self))

/-- An explicit additive error for the leading logarithm, uniform in the UV cutoff. -/
theorem root_proper_time_log_bounds (v : ℝ) {ε T : ℝ} (hε : 0 < ε) (hT : ε ≤ T) :
    let cost := ∫ t in ε..T, exp (-t*v^2)/t
    0 ≤ log (T/ε) - cost ∧ log (T/ε) - cost ≤ (T-ε)*v^2 := by
  have hpos t (ht : t ∈ [[ε,T]]) : 0 < t := hε.trans_le ((uIcc_of_le hT) ▸ ht).1
  have hi : IntervalIntegrable (fun t : ℝ => t⁻¹) volume ε T :=
    (continuousOn_id.inv₀ (fun t ht => (hpos t ht).ne')).intervalIntegrable
  have hj : IntervalIntegrable (fun t : ℝ => exp (-t*v^2)/t) volume ε T :=
    (ContinuousOn.div (by fun_prop) continuousOn_id (fun t ht => (hpos t ht).ne')).intervalIntegrable
  have hle t (ht : t ∈ [[ε,T]]) : 0 ≤ t⁻¹ - exp (-t*v^2)/t ∧ t⁻¹ - exp (-t*v^2)/t ≤ v^2 := by
    have ht₀ := hpos t ht
    have htV := mul_nonneg ht₀.le (sq_nonneg v)
    have hl := Real.add_one_le_exp (-t*v^2)
    have hh : exp (-t*v^2) ≤ 1 := exp_le_one_iff.mpr (by linarith)
    rw [← one_div, ← sub_div]
    exact ⟨div_nonneg (sub_nonneg.mpr hh) ht₀.le, (div_le_iff₀ ht₀).mpr (by linarith [mul_comm t (v^2)])⟩
  dsimp only
  rw [← integral_inv_of_pos hε (hε.trans_le hT), ← intervalIntegral.integral_sub hi hj]
  refine ⟨intervalIntegral.integral_nonneg hT (fun t ht => (hle t ((uIcc_of_le hT).symm ▸ ht)).1), ?_⟩
  have h := intervalIntegral.integral_mono_on hT (hi.sub hj) (intervalIntegrable_const (c := v^2))
    (fun t ht => (hle t ((uIcc_of_le hT).symm ▸ ht)).2)
  simpa using h

end UV.RootMagnetic
