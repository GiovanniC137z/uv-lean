import UV.ContinueThresholdExpansionReadout

/-! The ordinary integrable radial pairing after testing both translated
axial poles at the same positive height. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology NNReal ContDiff

variable {E : Type*} [NormedAddCommGroup E]

def unequalThresholdAxialBoundary (η₁ η₂ m₁ m₂ : ℝ) (g : ℝ × ℝ → ℂ) (r : ℝ) : ℂ :=
  let f₁ (x : ℝ) := g (x + (Real.sqrt (m₁ ^ 2 + r ^ 2) - m₁), r)
  let f₂ (x : ℝ) := g (x - (Real.sqrt (m₂ ^ 2 + r ^ 2) - m₂), r)
  (complexShellPV f₁ - Complex.I * (Real.pi : ℂ) * (η₁ : ℂ) * f₁ 0) -
    (complexShellPV f₂ + Complex.I * (Real.pi : ℂ) * (η₂ : ℂ) * f₂ 0)

private theorem Plane.threshold_expansion_root_continuous (diamond : Plane E) (ε : Evolution)
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

private theorem Plane.expansion_root_norm_le (diamond : Plane E) (ε : Evolution)
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

private def Plane.thresholdExpansionAxialComponent (diamond : Plane E) (ε κ : Evolution)
    (m : ℝ) (hm : 0 < m) (σ : ℝ) (F : ℝ × (ℝ × ℝ) → ℂ) (h : Height) (r : ℝ) : ℂ :=
  ∫ x, diamond.poleCoefficient κ (diamond.restThresholdAxialHeight ε h hm r) x *
    F ((h : ℝ), (x + σ * ((diamond.restThresholdRoot ε h m r).re - m), r))

private theorem Plane.threshold_expansion_component_limit_bound (diamond : Plane E) (ε κ : Evolution)
    {m : ℝ} (hm : 0 < m) {σ : ℝ} (hσ : |σ| = 1) {F : ℝ × (ℝ × ℝ) → ℂ}
    (hF : ContDiff ℝ 1 F) (hFs : HasCompactSupport F) {R : ℝ} (hR : 1 ≤ R)
    (hSupp : ∀ (h x r : ℝ), F (h,(x,r)) ≠ 0 → |x| ≤ R) :
    let J := diamond.thresholdExpansionAxialComponent ε κ m hm σ F
    (∃ C ≥ 0, ∀ᶠ h in poleBoundaryHeights, ∀ r, |r| ≤ R → ‖J h r‖ ≤ C) ∧
    (∀ r, |r| ≤ R →
      let g (x : ℝ) := F (0,(x + σ * (Real.sqrt (m ^ 2 + r ^ 2) - m), r))
      Tendsto (fun h => J h r) poleBoundaryHeights
        (𝓝 (complexShellPV g - Complex.I * (Real.pi : ℂ) * (diamond.eta κ : ℂ) * g 0))) := by
  intro J
  obtain ⟨L, hL⟩ := hF.lipschitzWith_of_hasCompactSupport hFs le_rfl
  obtain ⟨B, hB⟩ := hF.continuous.bounded_above_of_compact_support hFs
  let W := Real.sqrt (m ^ 2 + R ^ 2 + 1)
  let T := R + (W + m)
  have hT : 1 ≤ T := by dsimp [T, W]; linarith [Real.sqrt_nonneg (m ^ 2 + R ^ 2 + 1)]
  let c (u : ℝ) := σ * (u - m)
  let g (t u r x : ℝ) := F (t, (x + c u, r))
  have hg (t u r : ℝ) : LipschitzWith L (g t u r) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa [g, Prod.dist_eq] using hL.dist_le_mul (t, (x + c u, r)) (t, (y + c u, r))
  have hgS (t u r : ℝ) (hu : |u| ≤ W) (x : ℝ) (hx : T < |x|) : g t u r x = 0 := by
    by_contra hn
    have hcx : |c u| ≤ W + m := by
      dsimp only [c]
      rw [abs_mul, hσ, one_mul, sub_eq_add_neg]
      exact (abs_add_le _ _).trans (add_le_add hu (by simp [abs_of_pos hm]))
    have hd := abs_sub_abs_le_abs_sub x (-c u)
    rw [sub_neg_eq_add, abs_neg] at hd
    have he := hSupp _ _ _ hn
    dsimp [T] at hx
    linarith
  let u (h : Height) (r : ℝ) := (diamond.restThresholdRoot ε h m r).re
  let u₀ (r : ℝ) := Real.sqrt (m ^ 2 + r ^ 2)
  have hnear : ∀ᶠ h : Height in poleBoundaryHeights, ∀ r, |r| ≤ R → |u h r| ≤ W := by
    filter_upwards [pole_height_tendsto_zero (eventually_le_nhds zero_lt_one)] with h hh r hr
    exact (Complex.abs_re_le_norm _).trans (diamond.expansion_root_norm_le ε h hr hh)
  have h0 (r : ℝ) (hr : |r| ≤ R) : |u₀ r| ≤ W := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_sqrt
    have H := mul_le_mul hr hr (abs_nonneg r) ((abs_nonneg r).trans hr)
    have he : r ^ 2 ≤ R ^ 2 := by simpa only [← pow_two, sq_abs] using H
    linarith
  refine ⟨?_, ?_⟩
  · obtain ⟨C, hC, hc⟩ := diamond.rest_threshold_centered_cauchy_eventual_bound κ T hT L
      ((norm_nonneg _).trans (hB 0))
    refine ⟨C, hC, ?_⟩
    filter_upwards [diamond.rest_threshold_axial_height_eventually ε hm hc, hnear] with h hh hn r hr
    exact hh r (g h (u h r) r) (hg h (u h r) r) (hB _) (hgS h (u h r) r (hn r hr))
  · intro r hr
    refine diamond.rest_threshold_centered_cauchy_limit κ (B := B) (L := L)
      (diamond.rest_threshold_axial_height_tendsto ε hm r) (fun h => g h (u h r) r) (g 0 (u₀ r) r)
      hT (fun h => (hg _ _ _).continuous)
      (Eventually.of_forall fun h => ⟨hg _ _ _, hB _⟩) (hg 0 (u₀ r) r)
      (hnear.mono fun h hh => hgS _ _ _ (hh r hr)) (hgS _ _ _ (h0 r hr)) ?_
    intro x
    have H := (diamond.rest_threshold_root_tendsto ε hm r).mono_left
      (show poleBoundaryHeights ≤ Filter.comap Subtype.val (𝓝 (0 : ℝ)) from Filter.comap_mono nhdsWithin_le_nhds)
    have hu : Tendsto (fun h => u h r) poleBoundaryHeights (𝓝 (u₀ r)) :=
      Complex.continuous_re.continuousAt.tendsto.comp H
    have hconst : Tendsto (fun _ : Height => r) poleBoundaryHeights (𝓝 r) := tendsto_const_nhds
    have ht := (((hu.sub_const m).const_mul σ).const_add x).prodMk_nhds hconst
    exact hF.continuous.continuousAt.tendsto.comp (pole_height_tendsto_zero.prodMk_nhds ht)

private theorem Plane.unequal_threshold_axial_difference_continuous (diamond : Plane E)
    (ε₁ ε₂ : Evolution) (h : Height) {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    Continuous (diamond.unequalThresholdAxialDifference ε₁ ε₂ h m₁ m₂) := by
  have h₁ := (diamond.threshold_expansion_root_continuous ε₁ h hm₁).comp
    (continuous_snd : Continuous (Prod.snd : ℝ × ℝ → ℝ))
  have h₂ := (diamond.threshold_expansion_root_continuous ε₂ h hm₂).comp
    (continuous_snd : Continuous (Prod.snd : ℝ × ℝ → ℝ))
  have hx := Complex.continuous_ofReal.comp (continuous_fst : Continuous (Prod.fst : ℝ × ℝ → ℝ))
  have hA (z : ℝ × ℝ) : (z.1 : ℂ) - diamond.restThresholdNearPlus ε₁ h m₁ z.2 ≠ 0 := by
    intro hz
    have hi := congrArg Complex.im hz
    simp only [Plane.restThresholdNearPlus, Complex.sub_im, Complex.ofReal_im,
      sub_zero, zero_sub, Complex.zero_im, neg_eq_zero] at hi
    exact diamond.rest_threshold_root_im_ne_zero ε₁ h hm₁ z.2 hi
  have hB (z : ℝ × ℝ) : (z.1 : ℂ) - diamond.restThresholdNearMinus ε₂ h m₂ z.2 ≠ 0 := by
    intro hz
    have hi := congrArg Complex.im hz
    simp only [Plane.restThresholdNearMinus, Complex.sub_im, Complex.ofReal_im,
      zero_sub, neg_neg, Complex.zero_im] at hi
    exact diamond.rest_threshold_root_im_ne_zero ε₂ h hm₂ z.2 hi
  exact ((hx.sub (h₁.sub continuous_const)).inv₀ hA).sub
    ((hx.sub (continuous_const.sub h₂)).inv₀ hB)

private theorem Plane.unequal_threshold_radial_coefficient_continuous (diamond : Plane E)
    (ε₁ ε₂ : Evolution) (h : Height) {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    Continuous (diamond.unequalThresholdRadialCoefficient ε₁ ε₂ h m₁ m₂) := by
  have h₁ := diamond.threshold_expansion_root_continuous ε₁ h hm₁
  have h₂ := diamond.threshold_expansion_root_continuous ε₂ h hm₂
  exact (Complex.continuous_ofReal.comp (continuous_id.pow 2)).div
    ((h₁.sub continuous_const).sub (continuous_const.sub h₂))
    (diamond.unequal_threshold_gap_ne_zero ε₁ ε₂ h hm₁ hm₂)

private theorem Plane.unequal_threshold_integral_axial_split (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (r : ℝ)
    {f : ℝ → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) :
    (∫ x, diamond.unequalThresholdAxialDifference ε₁ ε₂ h m₁ m₂ (x, r) * f x) =
      (∫ x, diamond.poleCoefficient ε₁ (diamond.restThresholdAxialHeight ε₁ h hm₁ r) x *
        f (x + (diamond.restThresholdNearPlus ε₁ h m₁ r).re)) -
      (∫ x, diamond.poleCoefficient (restThresholdReverse ε₂) (diamond.restThresholdAxialHeight ε₂ h hm₂ r) x *
        f (x + (diamond.restThresholdNearMinus ε₂ h m₂ r).re)) := by
  let k₁ := diamond.restThresholdAxialHeight ε₁ h hm₁ r
  let k₂ := diamond.restThresholdAxialHeight ε₂ h hm₂ r
  let a := (diamond.restThresholdNearPlus ε₁ h m₁ r).re
  let b := (diamond.restThresholdNearMinus ε₂ h m₂ r).re
  let P := diamond.poleCoefficient ε₁ k₁
  let Q := diamond.poleCoefficient (restThresholdReverse ε₂) k₂
  have hP : Integrable (fun x => P (x - a) * f x) :=
    (((diamond.pole_coefficient_continuous ε₁ k₁).comp (continuous_id.sub continuous_const)).mul hf)
      |>.integrable_of_hasCompactSupport hs.mul_left
  have hQ : Integrable (fun x => Q (x - b) * f x) :=
    (((diamond.pole_coefficient_continuous (restThresholdReverse ε₂) k₂).comp
      (continuous_id.sub continuous_const)).mul hf) |>.integrable_of_hasCompactSupport hs.mul_left
  simp_rw [Plane.unequalThresholdAxialDifference, diamond.rest_threshold_near_plus_cauchy ε₁ h hm₁,
    diamond.rest_threshold_near_minus_cauchy ε₂ h hm₂, sub_mul]
  change (∫ x, P (x - a) * f x - Q (x - b) * f x) = _
  rw [integral_sub hP hQ, rest_threshold_integral_shift_center P f a,
    rest_threshold_integral_shift_center Q f b]

/-- The unequal-mass threshold has an explicit tested boundary supported
by an integrable uniform radial bound after the axial pairing. -/
theorem Plane.unequal_threshold_radial_difference_limit (diamond : Plane E) (ε₁ ε₂ : Evolution)
    {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) {F : ℝ × (ℝ × ℝ) → ℂ}
    (hF : ContDiff ℝ 1 F) (hFs : HasCompactSupport F) :
    Tendsto (fun h : Height => ∫ z in univ ×ˢ Ioi (0 : ℝ),
      F ((h : ℝ), z) * diamond.unequalThresholdRadialCoefficient ε₁ ε₂ h m₁ m₂ z.2 *
        diamond.unequalThresholdAxialDifference ε₁ ε₂ h m₁ m₂ z)
      poleBoundaryHeights
      (𝓝 (∫ r in Ioi (0 : ℝ), (↑(unequalThresholdRadialWeight m₁ m₂ r) : ℂ) *
        unequalThresholdAxialBoundary (diamond.eta ε₁) (diamond.eta ε₂) m₁ m₂ (fun z => F (0, z)) r)) := by
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
  obtain ⟨⟨C₁, hC₁, hB₁⟩, hL₁⟩ := diamond.threshold_expansion_component_limit_bound ε₁ ε₁ hm₁
    (show |(1 : ℝ)| = 1 by norm_num) hF hFs hR (fun _ _ _ h => (hSupp _ _ _ h).1)
  obtain ⟨⟨C₂, hC₂, hB₂⟩, hL₂⟩ := diamond.threshold_expansion_component_limit_bound ε₂
    (restThresholdReverse ε₂) hm₂ (show |(-1 : ℝ)| = 1 by norm_num) hF hFs hR
    (fun _ _ _ h => (hSupp _ _ _ h).1)
  let A (h : Height) (r : ℝ) := ∫ x, diamond.unequalThresholdAxialDifference ε₁ ε₂ h m₁ m₂ (x,r) *
    F ((h : ℝ), (x,r))
  let A₀ := unequalThresholdAxialBoundary (diamond.eta ε₁) (diamond.eta ε₂) m₁ m₂ (fun z => F (0, z))
  let J₁ := diamond.thresholdExpansionAxialComponent ε₁ ε₁ m₁ hm₁ 1 F
  let J₂ := diamond.thresholdExpansionAxialComponent ε₂ (restThresholdReverse ε₂) m₂ hm₂ (-1) F
  have hA (h : Height) (r : ℝ) : A h r = J₁ h r - J₂ h r := by
    have hcont : Continuous (fun x : ℝ => F ((h : ℝ), (x,r))) := by
      have hf := hF.continuous
      fun_prop
    unfold A
    rw [diamond.unequal_threshold_integral_axial_split ε₁ ε₂ h hm₁ hm₂ r hcont (hS _ r)]
    simp only [J₁, J₂, Plane.thresholdExpansionAxialComponent, Plane.restThresholdNearPlus,
      Plane.restThresholdNearMinus, Complex.sub_re, Complex.ofReal_re, one_mul, neg_one_mul, neg_sub]
  have hLim (r : ℝ) (hr : |r| ≤ R) : Tendsto (fun h => A h r) poleBoundaryHeights (𝓝 (A₀ r)) := by
    simp_rw [hA]
    have H := (hL₁ r hr).sub (hL₂ r hr)
    rw [diamond.rest_threshold_reverse_eta, Complex.ofReal_neg] at H
    convert H using 1
    simp only [A₀, unequalThresholdAxialBoundary, one_mul, neg_one_mul, sub_eq_add_neg]
    congr 2
    ring
  have hBound : ∀ᶠ h : Height in poleBoundaryHeights, ∀ r, |r| ≤ R → ‖A h r‖ ≤ C₁ + C₂ := by
    filter_upwards [hB₁, hB₂] with h h₁ h₂ r hr
    rw [hA]
    exact (norm_sub_le _ _).trans (add_le_add (h₁ r hr) (h₂ r hr))
  have hAoff (h : Height) (r : ℝ) (hr : R < |r|) : A h r = 0 := by
    have H (x : ℝ) : F ((h : ℝ), (x,r)) = 0 := by
      by_contra hn
      exact hr.not_ge (hSupp _ _ _ hn).2
    simp [A, H]
  have hA₀off (r : ℝ) (hr : R < |r|) : A₀ r = 0 := by
    have H (x : ℝ) : F (0, (x,r)) = 0 := by
      by_contra hn
      exact hr.not_ge (hSupp _ _ _ hn).2
    simp [A₀, unequalThresholdAxialBoundary, complexShellPV, H, symmetricTest]
  let C := diamond.unequalThresholdRadialCoefficient ε₁ ε₂
  let M := (Icc 0 R).indicator (fun r : ℝ => unequalThresholdRadialWeight m₁ m₂ r * (C₁ + C₂))
  have hM : Integrable M :=
    IntegrableOn.integrable_indicator ((unequal_threshold_radial_weight_integrable hm₁ hm₂ R).mul_const (C₁ + C₂))
      measurableSet_Icc
  have hJ (h : Height) :
      Continuous (fun z : ℝ × ℝ => diamond.unequalThresholdAxialDifference ε₁ ε₂ h m₁ m₂ z * F ((h : ℝ), z)) :=
    (diamond.unequal_threshold_axial_difference_continuous ε₁ ε₂ h hm₁ hm₂).mul
      (hF.continuous.comp (continuous_const.prodMk continuous_id))
  have hConv : Tendsto (fun h : Height => ∫ r in Ioi (0 : ℝ), C h m₁ m₂ r * A h r)
      poleBoundaryHeights
      (𝓝 (∫ r in Ioi (0 : ℝ), (↑(unequalThresholdRadialWeight m₁ m₂ r) : ℂ) * A₀ r)) := by
    refine tendsto_integral_filter_of_dominated_convergence M ?_ ?_ hM.integrableOn ?_
    · refine Eventually.of_forall fun h => ?_
      have hAm : StronglyMeasurable (A h) := (hJ h).stronglyMeasurable.integral_prod_left'
      exact ((diamond.unequal_threshold_radial_coefficient_continuous ε₁ ε₂ h hm₁ hm₂).measurable.mul
        hAm.measurable).aestronglyMeasurable
    · filter_upwards [hBound] with h hb
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hpos : 0 < r := hr
      by_cases hR' : r ≤ R
      · dsimp only [M]
        rw [norm_mul, indicator_of_mem (show r ∈ Icc (0 : ℝ) R from ⟨hpos.le, hR'⟩)]
        have hd := diamond.unequal_threshold_radial_coefficient_bound ε₁ ε₂ h hm₁ hm₂ r
        exact mul_le_mul hd (hb r (by rwa [abs_of_pos hpos])) (norm_nonneg _) ((norm_nonneg _).trans hd)
      · have Hoff : R < |r| := by rw [abs_of_pos hpos]; exact lt_of_not_ge hR'
        dsimp only [M]
        rw [hAoff h r Hoff, mul_zero, norm_zero, indicator_of_notMem (fun hh => hR' hh.2)]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hp : 0 < r := hr
      by_cases hR' : r ≤ R
      · exact (diamond.unequal_threshold_radial_coefficient_tendsto ε₁ ε₂ hm₁ hm₂ hp.ne').mul
          (hLim r (by rwa [abs_of_pos hp]))
      · have Hoff : R < |r| := by rw [abs_of_pos hp]; exact lt_of_not_ge hR'
        simp only [hAoff _ r Hoff, hA₀off r Hoff, mul_zero, tendsto_const_nhds]
  refine hConv.congr fun h => ?_
  let J (z : ℝ × ℝ) := C h m₁ m₂ z.2 * (diamond.unequalThresholdAxialDifference ε₁ ε₂ h m₁ m₂ z * F ((h : ℝ), z))
  have hJc : Continuous J :=
    ((diamond.unequal_threshold_radial_coefficient_continuous ε₁ ε₂ h hm₁ hm₂).comp continuous_snd).mul (hJ h)
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
