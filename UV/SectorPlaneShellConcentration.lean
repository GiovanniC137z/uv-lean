import UV.SectorPlaneResolventProduct

/-! The common positive-height Poisson kernel on the full Lorentzian shell.
Jointly continuous moving numerators are tested on compact four-momentum
supports. This includes the vertex of the massless cone. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology

def complexShellTest (m : ℝ) (f : MassiveMomentum → ℂ) : ℂ :=
  (fullShellTest m (fun q => (f q).re) : ℂ) + Complex.I * (fullShellTest m (fun q => (f q).im) : ℝ)

private theorem tested_poisson_integrable (h : Height) (m : ℝ) {f : MassiveMomentum → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) :
    Integrable (fun q => (polePoisson h (massiveD m q) : ℂ) * f q) := by
  have hc : Continuous (polePoisson (h:ℝ)) := continuous_iff_continuousAt.mpr
    (fun D => (polePoisson_hasDerivAt h.property D).continuousAt)
  exact ((Complex.continuous_ofReal.comp (hc.comp (massiveD_continuous m))).mul hf).integrable_of_hasCompactSupport hs.mul_left

theorem complex_poisson_shell_limit (m : ℝ) {f : MassiveMomentum → ℂ} (hf : Continuous f)
    (hs : HasCompactSupport f) :
    Tendsto (fun h : Height => ∫ q, (polePoisson h (massiveD m q) : ℂ) * f q)
      poleBoundaryHeights (𝓝 ((Real.pi : ℂ) * complexShellTest m f)) := by
  have part (p : ℂ → ℝ) (hp : Continuous p) (hz : p 0 = 0) :=
    (pole_poisson_full_shell_limit m (hp.comp hf) (hs.comp_left hz)).comp
      (tendsto_comap (f := fun h : Height => (h:ℝ)))
  have hr := Complex.continuous_ofReal.continuousAt.tendsto.comp (part _ Complex.continuous_re Complex.zero_re)
  have hi := Complex.continuous_ofReal.continuousAt.tendsto.comp (part _ Complex.continuous_im Complex.zero_im)
  have H := hr.add (hi.const_mul Complex.I)
  convert H.congr (f₂ := fun h : Height => ∫ q, (polePoisson h (massiveD m q) : ℂ) * f q) (fun h => ?_) using 2
  · unfold complexShellTest; simp only [Function.comp_def]; push_cast; ring
  · have hc : Continuous (polePoisson (h:ℝ)) := continuous_iff_continuousAt.mpr
      (fun D => (polePoisson_hasDerivAt h.property D).continuousAt)
    have hiv (p : ℂ → ℝ) (hp : Continuous p) (hz : p 0 = 0) :
        Integrable (fun q => polePoisson h (massiveD m q) * p (f q)) :=
      ((hc.comp (massiveD_continuous m)).mul (hp.comp hf)).integrable_of_hasCompactSupport (hs.comp_left hz).mul_left
    change ((∫ q, polePoisson h (massiveD m q) * (f q).re : ℝ) : ℂ) +
      Complex.I * ((∫ q, polePoisson h (massiveD m q) * (f q).im : ℝ) : ℂ) = _
    rw [← integral_complex_ofReal, ← integral_complex_ofReal, ← integral_const_mul,
      ← integral_add (hiv _ Complex.continuous_re Complex.zero_re).ofReal
        ((hiv _ Complex.continuous_im Complex.zero_im).ofReal.const_mul _)]
    apply integral_congr_ae
    exact Eventually.of_forall fun q => by
      simp only [Complex.ofReal_mul]
      rw [show (polePoisson h (massiveD m q) : ℂ) * ((f q).re : ℂ) +
          Complex.I * ((polePoisson h (massiveD m q) : ℂ) * ((f q).im : ℂ)) =
          (polePoisson h (massiveD m q) : ℂ) * ((f q).re + (f q).im * Complex.I) by ring, Complex.re_add_im]

/-- Only the limiting value of the numerator on the two mass sheets
enters the residue, even when the numerator moves with the pole height. -/
theorem moving_poisson_shell_limit (m : ℝ) (U : ℝ → MassiveMomentum → ℂ)
    (hc : Continuous (Function.uncurry U)) {f : MassiveMomentum → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) :
    Tendsto (fun h : Height => ∫ q, (polePoisson h (massiveD m q) : ℂ) * (U h q * f q))
      poleBoundaryHeights (𝓝 ((Real.pi : ℂ) * complexShellTest m (fun q => U 0 q * f q))) := by
  let K := tsupport f
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hs
  let V (t : ℝ) (q : K) := U t q.val
  have hV : Continuous (Function.uncurry V) :=
    hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hunif := Metric.tendstoUniformly_iff.mp (Continuous.tendstoUniformly V hV (0:ℝ))
  have hu (t : ℝ) : Continuous (U t) := hc.comp ((continuous_const (y := t)).prodMk continuous_id)
  have hlim := complex_poisson_shell_limit m ((hu 0).mul hf) hs.mul_left
  have hb := (pole_poisson_full_shell_limit m hf.norm hs.norm).comp (tendsto_comap (f := fun h : Height => (h:ℝ)))
  let C := |Real.pi * fullShellTest m (fun q => ‖f q‖)| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hB : ∀ᶠ h : Height in poleBoundaryHeights, (∫ q, polePoisson h (massiveD m q) * ‖f q‖) < C :=
    hb.eventually_lt_const (by dsimp [C]; linarith [le_abs_self (Real.pi * fullShellTest m (fun q => ‖f q‖))])
  have hdiff : Tendsto (fun h : Height => ∫ q, (polePoisson h (massiveD m q) : ℂ) *
      ((U h q-U 0 q)*f q)) poleBoundaryHeights (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    have hd : 0 < δ/C := div_pos hδ hC
    filter_upwards [pole_height_tendsto_zero.eventually (hunif _ hd), hB] with h hh hsmall
    rw [dist_zero_right]
    have hp : Continuous (polePoisson (h:ℝ)) := continuous_iff_continuousAt.mpr
      (fun D => (polePoisson_hasDerivAt h.property D).continuousAt)
    have hi : Integrable (fun q => polePoisson h (massiveD m q) * ‖f q‖) :=
      ((hp.comp (massiveD_continuous m)).mul hf.norm).integrable_of_hasCompactSupport hs.norm.mul_left
    have hbound := norm_integral_le_of_norm_le (μ := volume) (f := fun q =>
      (polePoisson h (massiveD m q) : ℂ) * ((U h q-U 0 q)*f q)) (hi.const_mul (δ/C))
      (Eventually.of_forall fun q => by
        have hq₀ : 0 ≤ polePoisson h (massiveD m q) := by unfold polePoisson; exact div_nonneg h.property.le (by positivity)
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq₀]
        by_cases hq : q ∈ K
        · have he : ‖U h q - U 0 q‖ ≤ δ/C := by
            simpa only [V, dist_eq_norm, norm_sub_rev (U 0 q)] using (hh ⟨q,hq⟩).le
          calc
            _ ≤ polePoisson h (massiveD m q) * ((δ/C)*‖f q‖) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (norm_nonneg _)) hq₀
            _ = _ := by ring
        · simp [image_eq_zero_of_notMem_tsupport hq])
    rw [integral_const_mul] at hbound
    exact hbound.trans_lt ((mul_lt_mul_of_pos_left hsmall hd).trans_eq (div_mul_cancel₀ δ hC.ne'))
  simpa only [zero_add] using (hdiff.add hlim).congr (fun h => by
    rw [← integral_add (tested_poisson_integrable h m (((hu h).sub (hu 0)).mul hf) hs.mul_left)
      (tested_poisson_integrable h m ((hu 0).mul hf) hs.mul_left)]
    apply integral_congr_ae
    exact Eventually.of_forall fun q => by ring)

theorem complex_shell_test_congr {m : ℝ} {f g : MassiveMomentum → ℂ}
    (hfg : ∀ q, massiveD m q = 0 → f q = g q) : complexShellTest m f = complexShellTest m g := by
  have he (p : Spatial) : shellFrequency m p ^ 2 = ‖p‖^2 + m^2 :=
    Real.sq_sqrt (by positivity)
  have hp (p : Spatial) : f (shellFrequency m p,p) = g (shellFrequency m p,p) := by
    apply hfg; unfold massiveD shellSquare; dsimp only; rw [he]; ring
  have hn (p : Spatial) : f (-shellFrequency m p,p) = g (-shellFrequency m p,p) := by
    apply hfg; unfold massiveD shellSquare; dsimp only; rw [neg_sq, he]; ring
  simp only [complexShellTest, fullShellTest, hp, hn]

theorem complex_shell_test_const_mul (m : ℝ) {f : MassiveMomentum → ℂ} (hf : Continuous f)
    (hs : HasCompactSupport f) (c : ℂ) :
    complexShellTest m (fun q => c*f q) = c * complexShellTest m f := by
  letI : poleBoundaryHeights.NeBot := pole_boundary_heights_neBot
  have h := (complex_poisson_shell_limit m hf hs).const_mul c
  have ha := complex_poisson_shell_limit m ((continuous_const (y := c)).mul hf) hs.mul_left
  have he := tendsto_nhds_unique ha (h.congr (f₂ := fun h : Height =>
    ∫ q, (polePoisson h (massiveD m q) : ℂ) * (c*f q)) fun h => by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun q => by ring)
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  apply mul_left_cancel₀ hp
  exact he.trans (by ring)

end UV.SectorPlane
