import UV.ContinueConeSquare

/-! The logarithmic obstruction for an actual compactly supported
radial test that is one on a neighbourhood of the tip. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Set Real Filter
open scoped Interval Topology

private theorem continuous_cone_radial_weight {h : ℝ} (hh : 0 < h) :
    Continuous (coneSquareRadialWeight h) := by
  unfold coneSquareRadialWeight
  exact (continuous_id.pow 5).div
    ((continuous_sqrt.comp (continuous_const.add (continuous_id.pow 4))).pow 3)
    (fun r => pow_ne_zero _ (sqrt_pos.mpr
      (add_pos_of_pos_of_nonneg (sq_pos_of_pos hh) (by positivity))).ne')

private theorem cone_radial_weight_nonneg_le_inv {h r : ℝ} (hr : 0 < r) :
    0 ≤ coneSquareRadialWeight h r ∧ coneSquareRadialWeight h r ≤ r⁻¹ := by
  rw [cone_square_radial_weight_eq hr]
  have hS : 1 ≤ sqrt (1 + (h / r ^ 2) ^ 2) := by
    calc
      1 = sqrt 1 := sqrt_one.symm
      _ ≤ _ := sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
  exact ⟨by positivity, div_le_self (inv_nonneg.mpr hr.le) (one_le_pow₀ hS)⟩

private theorem cone_square_radial_split {h d R : ℝ} (hh : 0 < h)
    (hd : 0 < d) (hdR : d ≤ R) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hone : ∀ r ∈ Icc 0 d, φ r = 1) (hs : ∀ r > R, φ r = 0) :
    (∫ r in Ioi (0 : ℝ), φ r * coneSquareRadialWeight h r) =
      (∫ r in (0 : ℝ)..d, coneSquareRadialWeight h r) +
      (∫ r in d..R, φ r * coneSquareRadialWeight h r) := by
  let f (r : ℝ) := φ r * coneSquareRadialWeight h r
  have hi : Continuous f := hc.mul (continuous_cone_radial_weight hh)
  have hzero (r : ℝ) (hr : r ∈ Ioi R) : f r = 0 := by simp [f, hs r hr]
  have hU : Ioc 0 R ∪ Ioi R = Ioi (0 : ℝ) := by
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact (hd.trans_le hdR).trans h
    · intro hx
      rcases le_or_gt x R with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
  have hOne : (∫ r in (0 : ℝ)..d, f r) =
      ∫ r in (0 : ℝ)..d, coneSquareRadialWeight h r := by
    rw [intervalIntegral.integral_of_le hd.le, intervalIntegral.integral_of_le hd.le]
    apply setIntegral_congr_fun measurableSet_Ioc
    exact fun r hr => by simp [f, hone r (Ioc_subset_Icc_self hr)]
  change (∫ r in Ioi (0 : ℝ), f r) = _
  rw [← hU, integral_union_eq_left_of_forall measurableSet_Ioi hzero,
    ← intervalIntegral.integral_of_le (hd.trans_le hdR).le,
    ← intervalIntegral.integral_add_adjacent_intervals (hi.intervalIntegrable 0 d)
      (hi.intervalIntegrable d R), hOne]

private theorem cone_square_tail_bound {h d R M : ℝ} (hd : 0 < d) (hdR : d ≤ R)
    {φ : ℝ → ℝ} (hφ : ∀ r ∈ Icc d R, ‖φ r‖ ≤ M) :
    ‖∫ r in d..R, φ r * coneSquareRadialWeight h r‖ ≤ (R - d) * (M / d) := by
  have H := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := d) (b := R) (C := M / d) (f := fun r => φ r * coneSquareRadialWeight h r)
  rw [abs_of_nonneg (sub_nonneg.mpr hdR)] at H
  rw [mul_comm (R - d)]
  apply H
  intro r hr
  rw [uIoc_of_le hdR] at hr
  have hr₀ : 0 < r := hd.trans hr.1
  obtain ⟨hw, hwr⟩ := cone_radial_weight_nonneg_le_inv (h := h) hr₀
  have hm : 0 ≤ M := (norm_nonneg _).trans (hφ d ⟨le_rfl, hdR⟩)
  rw [norm_mul, Real.norm_of_nonneg hw, div_eq_mul_inv]
  exact (mul_le_mul_of_nonneg_right (hφ r (Ioc_subset_Icc_self hr)) hw).trans
    (mul_le_mul_of_nonneg_left (hwr.trans (inv_anti₀ hd hr.1.le)) hm)

variable {E : Type*} [NormedAddCommGroup E]

/-- The radial test gives exactly the signed π² coefficient of
log(href / h), with a bounded error for all sufficiently small h. -/
theorem Plane.cone_square_pairing_log_budget (diamond : Plane E) (ε : Evolution)
    {d R href : ℝ} (hd : 0 < d) (hdR : d ≤ R) (hRef : 0 < href)
    {φ : ℝ → ℝ} (hc : Continuous φ) (hone : ∀ r ∈ Icc 0 d, φ r = 1)
    (hs : ∀ r > R, φ r = 0) :
    ∃ C : ℝ, ∀ h : Height, (h : ℝ) ≤ d ^ 2 →
      ‖(diamond.coneSquarePairing ε h φ).im -
        diamond.eta ε * π ^ 2 * log (href / (h : ℝ))‖ ≤ C := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc d R) hc.continuousOn
  refine ⟨π ^ 2 * (1 + log 3) + 2 * π ^ 2 * ((R - d) * (M / d)) +
    π ^ 2 * ‖log (d ^ 2 / href)‖, ?_⟩
  intro h hsmall
  have hη : ‖diamond.eta ε‖ = 1 := by
    rw [Real.norm_eq_abs]
    exact (sq_eq_sq₀ (abs_nonneg _) zero_le_one).mp (by
      rw [sq_abs, diamond.eta_sq, one_pow])
  have hLog : log (d ^ 2 / (h : ℝ)) - log (href / (h : ℝ)) = log (d ^ 2 / href) := by
    rw [log_div (sq_pos_of_pos hd).ne' h.property.ne', log_div hRef.ne' h.property.ne',
      log_div (sq_pos_of_pos hd).ne' hRef.ne']
    ring
  let A := ∫ r in (0 : ℝ)..d, coneSquareRadialWeight h r
  let B := ∫ r in d..R, φ r * coneSquareRadialWeight h r
  rw [diamond.cone_square_pairing_im ε h hc hs,
    cone_square_radial_split h.property hd hdR hc hone hs]
  change ‖diamond.eta ε * (2 * π ^ 2) * (A + B) -
        diamond.eta ε * π ^ 2 * log (href / (h : ℝ))‖ ≤ _
  have hRewrite : diamond.eta ε * (2 * π ^ 2) * (A + B) -
        diamond.eta ε * π ^ 2 * log (href / (h : ℝ)) =
      diamond.eta ε * ((2 * π ^ 2 * A - π ^ 2 * log (d ^ 2 / (h : ℝ)) + 2 * π ^ 2 * B) +
        π ^ 2 * log (d ^ 2 / href)) := by
    rw [← hLog]
    ring
  rw [hRewrite, norm_mul, hη, one_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_add_le _ _).trans (add_le_add (cone_square_radial_log_budget h.property hd hsmall) ?_)
    rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * π ^ 2)]
    exact mul_le_mul_of_nonneg_left (cone_square_tail_bound hd hdR hM) (by positivity)
  · rw [norm_mul, Real.norm_of_nonneg (sq_nonneg π)]


/-- Multiplication by the prescribed orientation puts the imaginary
divergence on the positive ray for either branch. -/
theorem Plane.cone_square_pairing_signed_im_tendsto (diamond : Plane E) (ε : Evolution)
    {d R : ℝ} (hd : 0 < d) (hdR : d ≤ R)
    {φ : ℝ → ℝ} (hc : Continuous φ) (hone : ∀ r ∈ Icc 0 d, φ r = 1)
    (hs : ∀ r > R, φ r = 0) :
    Tendsto (fun h : Height => diamond.eta ε * (diamond.coneSquarePairing ε h φ).im)
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))) atTop := by
  let H := (𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))
  have hHeight : Tendsto (fun h : Height => (h : ℝ)) H (𝓝[>] (0 : ℝ)) :=
    tendsto_comap
  have hSmall : ∀ᶠ h : Height in H, (h : ℝ) ≤ d ^ 2 :=
    (hHeight.mono_right nhdsWithin_le_nhds).eventually
      (ge_mem_nhds (sq_pos_of_pos hd))
  obtain ⟨C, hC⟩ := diamond.cone_square_pairing_log_budget ε hd hdR zero_lt_one hc hone hs
  have hLog : Tendsto (fun h : Height => π ^ 2 * log (1 / (h : ℝ))) H atTop :=
    (tendsto_log_atTop.comp (by
      simpa only [one_div] using tendsto_inv_nhdsGT_zero.comp hHeight)).const_mul_atTop
      (sq_pos_of_pos pi_pos)
  apply tendsto_atTop.2
  intro b
  filter_upwards [hSmall, hLog.eventually_ge_atTop (b + C)] with h hsmall hlarge
  have hη : ‖diamond.eta ε‖ = 1 := by
    rw [Real.norm_eq_abs]
    exact (sq_eq_sq₀ (abs_nonneg _) zero_le_one).mp (by
      rw [sq_abs, diamond.eta_sq, one_pow])
  have hB := hC h hsmall
  have hM : ‖diamond.eta ε * ((diamond.coneSquarePairing ε h φ).im -
      diamond.eta ε * π ^ 2 * log (1 / (h : ℝ)))‖ ≤ C := by
    rwa [norm_mul, hη, one_mul]
  rw [mul_sub, ← mul_assoc (diamond.eta ε) (diamond.eta ε * π ^ 2),
    ← mul_assoc, ← pow_two, diamond.eta_sq, one_mul, Real.norm_eq_abs, abs_le] at hM
  linarith only [hM.1, hlarge]

end UV.SectorPlane
