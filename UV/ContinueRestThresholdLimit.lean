import UV.ContinueRestThresholdAxial

/-! Degenerate threshold boundary after axial testing. At each positive
radius one has two simple axial boundary values, and the intrinsic r²
weight cancels their potentially singular separation at r = 0. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology NNReal ContDiff

variable {E : Type*} [NormedAddCommGroup E]

private theorem Plane.rest_threshold_root_continuous (diamond : Plane E) (ε : Evolution)
    (h : Height) {m : ℝ} (hm : 0 < m) :
    Continuous (diamond.restThresholdRoot ε h m) := by
  let w : ℝ → ℂ := fun r => (↑(m ^ 2 + r ^ 2) : ℂ) - Complex.I * ↑(diamond.eta ε * (h : ℝ))
  have hw : Continuous w := by unfold w; fun_prop
  apply continuous_iff_continuousAt.mpr
  intro r
  have hr : 0 < (w r).re := by
    unfold w
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
    positivity
  exact (principalSqrt_differentiableAt hr).continuousAt.comp hw.continuousAt

private theorem Plane.rest_threshold_root_norm_le (diamond : Plane E) (ε : Evolution)
    (h : Height) {m R r : ℝ} (hR : |r| ≤ R) (hh : (h : ℝ) ≤ 1) :
    ‖diamond.restThresholdRoot ε h m r‖ ≤ Real.sqrt (m ^ 2 + R ^ 2 + 1) := by
  have he : |diamond.eta ε| = 1 := by
    rw [← Real.sqrt_sq_eq_abs, diamond.eta_sq ε, Real.sqrt_one]
  have hr : r ^ 2 ≤ R ^ 2 := by
    have H := mul_le_mul hR hR (abs_nonneg r) ((abs_nonneg r).trans hR)
    simpa only [← pow_two, sq_abs] using H
  rw [Plane.restThresholdRoot, principalSqrt_norm]
  apply Real.sqrt_le_sqrt
  apply (norm_sub_le _ _).trans
  simp only [norm_mul, Complex.norm_real, Complex.norm_I, one_mul, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ m ^ 2 + r ^ 2 by positivity), he, abs_of_pos h.property]
  linarith only [hr, hh]

private theorem Plane.rest_threshold_root_re_tendsto (diamond : Plane E) (ε : Evolution)
    {m : ℝ} (hm : 0 < m) (r : ℝ) :
    Tendsto (fun h => (diamond.restThresholdRoot ε h m r).re)
      poleBoundaryHeights (𝓝 (Real.sqrt (m ^ 2 + r ^ 2))) := by
  have H := (diamond.rest_threshold_root_tendsto ε hm r).mono_left
    (show poleBoundaryHeights ≤ Filter.comap Subtype.val (𝓝 (0 : ℝ)) from
      Filter.comap_mono nhdsWithin_le_nhds)
  exact Complex.continuous_re.continuousAt.tendsto.comp H

/-- The two axial thresholds at each spatial radius, paired against a fixed
test by ordinary one-dimensional principal values and shell evaluations. -/
def restThresholdAxialBoundary (η₁ η₂ m : ℝ) (g : ℝ × ℝ → ℂ) (r : ℝ) : ℂ :=
  let a := Real.sqrt (m ^ 2 + r ^ 2) - m
  let gPlus (x : ℝ) := g (x + a, r)
  let gMinus (x : ℝ) := g (x - a, r)
  (complexShellPV gPlus - Complex.I * (Real.pi : ℂ) * (η₁ : ℂ) * gPlus 0) -
    (complexShellPV gMinus + Complex.I * (Real.pi : ℂ) * (η₂ : ℂ) * gMinus 0)

private theorem Plane.rest_threshold_axial_difference_continuous (diamond : Plane E)
    (ε₁ ε₂ : Evolution) (h : Height) {m : ℝ} (hm : 0 < m) :
    Continuous (diamond.restThresholdAxialDifference ε₁ ε₂ h m) := by
  have h₁ := (diamond.rest_threshold_root_continuous ε₁ h hm).comp
    (continuous_snd : Continuous (Prod.snd : ℝ × ℝ → ℝ))
  have h₂ := (diamond.rest_threshold_root_continuous ε₂ h hm).comp
    (continuous_snd : Continuous (Prod.snd : ℝ × ℝ → ℝ))
  have hx := Complex.continuous_ofReal.comp (continuous_fst : Continuous (Prod.fst : ℝ × ℝ → ℝ))
  have hA (z : ℝ × ℝ) : (z.1 : ℂ) - diamond.restThresholdNearPlus ε₁ h m z.2 ≠ 0 := by
    intro hz
    have hi := congrArg Complex.im hz
    simp only [Plane.restThresholdNearPlus, Complex.sub_im, Complex.ofReal_im,
      sub_zero, zero_sub, Complex.zero_im, neg_eq_zero] at hi
    exact diamond.rest_threshold_root_im_ne_zero ε₁ h hm z.2 hi
  have hB (z : ℝ × ℝ) : (z.1 : ℂ) - diamond.restThresholdNearMinus ε₂ h m z.2 ≠ 0 := by
    intro hz
    have hi := congrArg Complex.im hz
    simp only [Plane.restThresholdNearMinus, Complex.sub_im, Complex.ofReal_im,
      zero_sub, neg_neg, Complex.zero_im] at hi
    exact diamond.rest_threshold_root_im_ne_zero ε₂ h hm z.2 hi
  exact ((hx.sub (h₁.sub continuous_const)).inv₀ hA).sub
    ((hx.sub (continuous_const.sub h₂)).inv₀ hB)

private theorem Plane.rest_threshold_integral_axial_split (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) {m : ℝ} (hm : 0 < m) (r : ℝ)
    {f : ℝ → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) :
    (∫ x, diamond.restThresholdAxialDifference ε₁ ε₂ h m (x, r) * f x) =
      (∫ x, diamond.poleCoefficient ε₁ (diamond.restThresholdAxialHeight ε₁ h hm r) x *
        f (x + (diamond.restThresholdNearPlus ε₁ h m r).re)) -
      (∫ x, diamond.poleCoefficient (restThresholdReverse ε₂) (diamond.restThresholdAxialHeight ε₂ h hm r) x *
        f (x + (diamond.restThresholdNearMinus ε₂ h m r).re)) := by
  let k₁ := diamond.restThresholdAxialHeight ε₁ h hm r
  let k₂ := diamond.restThresholdAxialHeight ε₂ h hm r
  let a := (diamond.restThresholdNearPlus ε₁ h m r).re
  let b := (diamond.restThresholdNearMinus ε₂ h m r).re
  let P := diamond.poleCoefficient ε₁ k₁
  let Q := diamond.poleCoefficient (restThresholdReverse ε₂) k₂
  have hP : Integrable (fun x => P (x - a) * f x) :=
    (((diamond.pole_coefficient_continuous ε₁ k₁).comp (continuous_id.sub continuous_const)).mul hf)
      |>.integrable_of_hasCompactSupport hs.mul_left
  have hQ : Integrable (fun x => Q (x - b) * f x) :=
    (((diamond.pole_coefficient_continuous (restThresholdReverse ε₂) k₂).comp
      (continuous_id.sub continuous_const)).mul hf) |>.integrable_of_hasCompactSupport hs.mul_left
  simp_rw [Plane.restThresholdAxialDifference, diamond.rest_threshold_near_plus_cauchy ε₁ h hm,
    diamond.rest_threshold_near_minus_cauchy ε₂ h hm, sub_mul]
  change (∫ x, P (x - a) * f x - Q (x - b) * f x) = _
  rw [integral_sub hP hQ, rest_threshold_integral_shift_center P f a,
    rest_threshold_integral_shift_center Q f b]

/-- Tested local boundary at the degenerate equal-mass threshold. The
compact smooth amplitude is tested axially first. The radial integral
then has an ordinary integrable bound at the zero-radius intersection. -/
theorem Plane.rest_threshold_radial_difference_limit (diamond : Plane E) (ε₁ ε₂ : Evolution)
    {m : ℝ} (hm : 0 < m) {F : ℝ × (ℝ × ℝ) → ℂ}
    (hF : ContDiff ℝ 1 F) (hFs : HasCompactSupport F) :
    Tendsto (fun h : Height => ∫ z in univ ×ˢ Ioi (0 : ℝ),
      F ((h : ℝ), z) * diamond.restThresholdRadialCoefficient ε₁ ε₂ h m z.2 *
        diamond.restThresholdAxialDifference ε₁ ε₂ h m z)
      poleBoundaryHeights
      (𝓝 (∫ r in Ioi (0 : ℝ), (↑((Real.sqrt (m ^ 2 + r ^ 2) + m) / 2) : ℂ) *
        restThresholdAxialBoundary (diamond.eta ε₁) (diamond.eta ε₂) m (fun z => F (0, z)) r)) := by
  obtain ⟨R₀, hR₀⟩ := hFs.isBounded.subset_closedBall (0 : ℝ × (ℝ × ℝ))
  let R := max 1 R₀
  have hR : 1 ≤ R := le_max_left _ _
  have hSupp (h x r : ℝ) (hZ : F (h, (x, r)) ≠ 0) : |x| ≤ R ∧ |r| ≤ R := by
    have H := hR₀ (subset_tsupport _ hZ)
    simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, max_le_iff] at H
    exact ⟨H.2.1.trans (le_max_right _ _), H.2.2.trans (le_max_right _ _)⟩
  have hS (h r : ℝ) : HasCompactSupport (fun x => F (h, (x, r))) := by
    apply HasCompactSupport.intro isCompact_Icc
    intro x hx
    by_contra hh
    exact hx (abs_le.mp (hSupp h x r hh).1)
  obtain ⟨L, hL⟩ := hF.lipschitzWith_of_hasCompactSupport hFs le_rfl
  obtain ⟨B, hB⟩ := hF.continuous.bounded_above_of_compact_support hFs
  have hB₀ : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let W := Real.sqrt (m ^ 2 + R ^ 2 + 1)
  let T := R + (W + m)
  have hT : 1 ≤ T := by dsimp [T, W]; linarith [Real.sqrt_nonneg (m ^ 2 + R ^ 2 + 1)]
  have hh₁ : ∀ᶠ h : Height in poleBoundaryHeights, (h : ℝ) ≤ 1 :=
    pole_height_tendsto_zero (eventually_le_nhds zero_lt_one)
  let c (ε : Evolution) (σ : ℝ) (h : Height) (r : ℝ) :=
    σ * ((diamond.restThresholdRoot ε h m r).re - m)
  let c₀ (σ r : ℝ) := σ * (Real.sqrt (m ^ 2 + r ^ 2) - m)
  let g (ε : Evolution) (σ : ℝ) (h : Height) (r x : ℝ) := F ((h : ℝ), (x + c ε σ h r, r))
  let g₀ (σ r x : ℝ) := F (0, (x + c₀ σ r, r))
  have hgL (ε : Evolution) (σ : ℝ) (h : Height) (r : ℝ) : LipschitzWith L (g ε σ h r) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa [g, Prod.dist_eq] using hL.dist_le_mul
      ((h : ℝ), (x + c ε σ h r, r)) ((h : ℝ), (y + c ε σ h r, r))
  have hg₀L (σ r : ℝ) : LipschitzWith L (g₀ σ r) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa [g₀, Prod.dist_eq] using hL.dist_le_mul (0, (x + c₀ σ r, r)) (0, (y + c₀ σ r, r))
  have hc (ε : Evolution) (σ : ℝ) (hσ : |σ| = 1) (h : Height) (hh : (h : ℝ) ≤ 1)
      (r : ℝ) (hr : |r| ≤ R) : |c ε σ h r| ≤ W + m := by
    dsimp only [c]
    rw [abs_mul, hσ, one_mul, sub_eq_add_neg]
    calc
      _ ≤ |(diamond.restThresholdRoot ε h m r).re| + |-m| := abs_add_le _ _
      _ ≤ _ := add_le_add ((Complex.abs_re_le_norm _).trans
        (diamond.rest_threshold_root_norm_le ε h hr hh)) (by simp only [abs_neg, abs_of_pos hm, le_refl])
  have hc₀ (σ : ℝ) (hσ : |σ| = 1) (r : ℝ) (hr : |r| ≤ R) : |c₀ σ r| ≤ W + m := by
    have HH := mul_le_mul hr hr (abs_nonneg r) ((abs_nonneg r).trans hr)
    have he : r ^ 2 ≤ R ^ 2 := by simpa only [← pow_two, sq_abs] using HH
    have hW : Real.sqrt (m ^ 2 + r ^ 2) ≤ W := Real.sqrt_le_sqrt (by linarith)
    dsimp only [c₀]
    rw [abs_mul, hσ, one_mul, sub_eq_add_neg]
    exact (abs_add_le _ _).trans (by
      rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_neg, abs_of_pos hm]
      exact add_le_add_right hW _)
  have hgS (ε : Evolution) (σ : ℝ) (hσ : |σ| = 1) (h : Height) (hh : (h : ℝ) ≤ 1)
      (r : ℝ) (hr : |r| ≤ R) (x : ℝ) (hx : T < |x|) : g ε σ h r x = 0 := by
    by_contra! hn
    have ha := (hSupp _ _ _ hn).1
    have hd := abs_sub_abs_le_abs_sub x (-c ε σ h r)
    rw [sub_neg_eq_add, abs_neg] at hd
    have hm' := hc ε σ hσ h hh r hr
    dsimp [T] at hx
    linarith
  have hg₀S (σ : ℝ) (hσ : |σ| = 1) (r : ℝ) (hr : |r| ≤ R) (x : ℝ) (hx : T < |x|) :
      g₀ σ r x = 0 := by
    by_contra! hn
    have ha := (hSupp _ _ _ hn).1
    have hd := abs_sub_abs_le_abs_sub x (-c₀ σ r)
    rw [sub_neg_eq_add, abs_neg] at hd
    have hm' := hc₀ σ hσ r hr
    dsimp [T] at hx
    linarith
  let A := fun h : Height => fun r : ℝ => ∫ x, diamond.restThresholdAxialDifference ε₁ ε₂ h m (x,r) *
    F ((h : ℝ), (x,r))
  let A₀ := restThresholdAxialBoundary (diamond.eta ε₁) (diamond.eta ε₂) m (fun z => F (0, z))
  have hA (r : ℝ) (hr : |r| ≤ R) : Tendsto (fun h => A h r) poleBoundaryHeights (𝓝 (A₀ r)) := by
    have h1 (ε κ : Evolution) (σ : ℝ) (hσ : |σ| = 1) :
        Tendsto (fun h => ∫ x, diamond.poleCoefficient κ (diamond.restThresholdAxialHeight ε h hm r) x *
            g ε σ h r x) poleBoundaryHeights
          (𝓝 (complexShellPV (g₀ σ r) - Complex.I * (Real.pi : ℂ) * (diamond.eta κ : ℂ) * g₀ σ r 0)) := by
      refine diamond.rest_threshold_centered_cauchy_limit κ (B := B) (L := L)
        (diamond.rest_threshold_axial_height_tendsto ε hm r) _ _ hT
        (fun h => (hgL ε σ h r).continuous) ?_ (hg₀L σ r)
        (hh₁.mono (fun h hh => hgS ε σ hσ h hh r hr)) (hg₀S σ hσ r hr) ?_
      · exact Eventually.of_forall fun h => ⟨hgL ε σ h r, hB _⟩
      · intro x
        have ht := (((diamond.rest_threshold_root_re_tendsto ε hm r).sub_const m).const_mul σ).const_add x
        exact hF.continuous.continuousAt.tendsto.comp
          (pole_height_tendsto_zero.prodMk_nhds (ht.prodMk_nhds tendsto_const_nhds))
    have H := (h1 ε₁ ε₁ 1 (by norm_num)).sub
      (h1 ε₂ (restThresholdReverse ε₂) (-1) (by norm_num))
    rw [diamond.rest_threshold_reverse_eta, Complex.ofReal_neg] at H
    convert H using 1
    · ext h
      unfold A
      rw [diamond.rest_threshold_integral_axial_split ε₁ ε₂ h hm r
        (f := fun x => F ((h : ℝ), (x,r)))
          (by simpa only [g, c, zero_mul, add_zero] using (hgL ε₁ 0 h r).continuous) (hS _ r)]
      simp only [g, c, one_mul, neg_one_mul, Plane.restThresholdNearPlus, Plane.restThresholdNearMinus,
        Complex.sub_re, Complex.ofReal_re, neg_sub]
    · simp only [A₀, restThresholdAxialBoundary, g₀, c₀, one_mul, neg_one_mul, ← sub_eq_add_neg]
      congr 2
      ring
  obtain ⟨C₁, hC₁, hB₁⟩ := diamond.rest_threshold_centered_cauchy_eventual_bound ε₁ T hT L hB₀
  obtain ⟨C₂, hC₂, hB₂⟩ :=
    diamond.rest_threshold_centered_cauchy_eventual_bound (restThresholdReverse ε₂) T hT L hB₀
  have hBound : ∀ᶠ h : Height in poleBoundaryHeights, ∀ r, |r| ≤ R → ‖A h r‖ ≤ C₁ + C₂ := by
    filter_upwards [diamond.rest_threshold_axial_height_eventually ε₁ hm hB₁,
      diamond.rest_threshold_axial_height_eventually ε₂ hm hB₂, hh₁] with h h₁ h₂ hh r hr
    unfold A
    rw [diamond.rest_threshold_integral_axial_split ε₁ ε₂ h hm r
      (f := fun x => F ((h : ℝ), (x,r)))
          (by simpa only [g, c, zero_mul, add_zero] using (hgL ε₁ 0 h r).continuous) (hS _ r)]
    apply (norm_sub_le _ _).trans
    apply add_le_add
    · have H := h₁ r (g ε₁ 1 h r) (hgL ε₁ 1 h r) (hB _) (hgS ε₁ 1 (by norm_num) h hh r hr)
      simpa only [g, c, one_mul, Plane.restThresholdNearPlus, Complex.sub_re,
        Complex.ofReal_re] using H
    · have H := h₂ r (g ε₂ (-1) h r) (hgL ε₂ (-1) h r) (hB _)
          (hgS ε₂ (-1) (by norm_num) h hh r hr)
      simpa only [g, c, neg_one_mul, neg_sub, Plane.restThresholdNearMinus, Complex.sub_re,
        Complex.ofReal_re] using H
  have hAoff (h : Height) (r : ℝ) (hr : R < |r|) : A h r = 0 := by
    have H (x : ℝ) : F ((h : ℝ), (x,r)) = 0 := by
      by_contra hn
      exact hr.not_ge (hSupp _ _ _ hn).2
    simp [A, H]
  have hA₀off (r : ℝ) (hr : R < |r|) : A₀ r = 0 := by
    have H (x : ℝ) : F (0, (x,r)) = 0 := by
      by_contra hn
      exact hr.not_ge (hSupp _ _ _ hn).2
    simp [A₀, restThresholdAxialBoundary, complexShellPV, H, symmetricTest]
  let C := diamond.restThresholdRadialCoefficient ε₁ ε₂
  let M := (Icc 0 R).indicator (fun r : ℝ => ((Real.sqrt (m ^ 2 + r ^ 2) + m) / 2) * (C₁ + C₂))
  have hM : Integrable M :=
    IntegrableOn.integrable_indicator ((rest_threshold_radial_majorant_integrable m R).mul_const (C₁ + C₂))
      measurableSet_Icc
  have hJ (h : Height) :
      Continuous (fun z : ℝ × ℝ => diamond.restThresholdAxialDifference ε₁ ε₂ h m z *
        F ((h : ℝ), z)) :=
    (diamond.rest_threshold_axial_difference_continuous ε₁ ε₂ h hm).mul
      (hF.continuous.comp (continuous_const.prodMk continuous_id))
  have hConv : Tendsto (fun h : Height => ∫ r in Ioi (0 : ℝ), C h m r * A h r)
      poleBoundaryHeights
      (𝓝 (∫ r in Ioi (0 : ℝ), (↑((Real.sqrt (m ^ 2 + r ^ 2) + m) / 2) : ℂ) * A₀ r)) := by
    refine tendsto_integral_filter_of_dominated_convergence M ?_ ?_ hM.integrableOn ?_
    · refine Eventually.of_forall fun h => ?_
      have hAm : StronglyMeasurable (A h) :=
        (hJ h).stronglyMeasurable.integral_prod_left'
      exact ((diamond.rest_threshold_radial_coefficient_continuous ε₁ ε₂ h hm).measurable.mul
        hAm.measurable).aestronglyMeasurable
    · filter_upwards [hBound] with h hb
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hpos : 0 < r := hr
      by_cases hR' : r ≤ R
      · dsimp only [M]
        rw [norm_mul, indicator_of_mem (show r ∈ Icc (0 : ℝ) R from ⟨hpos.le, hR'⟩)]
        exact mul_le_mul (diamond.rest_threshold_radial_coefficient_bound ε₁ ε₂ h hm r)
          (hb r (by rwa [abs_of_pos hpos])) (norm_nonneg _) (by positivity)
      · have Hoff : R < |r| := by rw [abs_of_pos hpos]; exact lt_of_not_ge hR'
        dsimp only [M]
        rw [hAoff h r Hoff, mul_zero, norm_zero, indicator_of_notMem (fun hh => hR' hh.2)]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hp : 0 < r := hr
      by_cases hR' : r ≤ R
      · exact (diamond.rest_threshold_radial_coefficient_tendsto ε₁ ε₂ hm hp.ne').mul
          (hA r (by rwa [abs_of_pos hp]))
      · have Hoff : R < |r| := by rw [abs_of_pos hp]; exact lt_of_not_ge hR'
        simp only [hAoff _ r Hoff, hA₀off r Hoff, mul_zero, tendsto_const_nhds]
  refine hConv.congr fun h => ?_
  let J (z : ℝ × ℝ) := C h m z.2 * (diamond.restThresholdAxialDifference ε₁ ε₂ h m z *
    F ((h : ℝ), z))
  have hJc : Continuous J :=
    ((diamond.rest_threshold_radial_coefficient_continuous ε₁ ε₂ h hm).comp continuous_snd).mul (hJ h)
  have hJs : HasCompactSupport J := by
    apply HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc :
      IsCompact (Icc (-R) R ×ˢ Icc (-R) R))
    intro z hz
    have hf : F ((h : ℝ), z) = 0 := by
      by_contra hh
      have hb := hSupp _ _ _ hh
      exact hz ⟨abs_le.mp hb.1, abs_le.mp hb.2⟩
    simp [J, hf]
  calc
    _ = ∫ r in Ioi (0 : ℝ), ∫ x in univ, J (x,r) := by
      simp only [setIntegral_univ, integral_const_mul, J, A]
    _ = ∫ z in univ ×ˢ Ioi (0 : ℝ), J z := by
      have hμ : (volume : Measure (ℝ × ℝ)).restrict (univ ×ˢ Ioi (0 : ℝ)) =
          (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))) := by
        change ((volume : Measure ℝ).prod volume).restrict (univ ×ˢ Ioi 0) = _
        rw [← Measure.prod_restrict, Measure.restrict_univ]
      rw [hμ]
      simp only [setIntegral_univ]
      apply (integral_prod_symm J _).symm
      rw [← hμ]
      exact (hJc.integrable_of_hasCompactSupport hJs).integrableOn
    _ = _ := by
      apply setIntegral_congr_fun (MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi)
      intro z _
      dsimp [J, C]
      ring

end UV.SectorPlane
