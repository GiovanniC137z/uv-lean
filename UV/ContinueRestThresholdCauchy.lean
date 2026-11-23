import UV.ContinueTransverseChartProduct

/-! One-dimensional bounds and moving tests for the two refracted axial
heights. The positive regulators may move at different rates after
factoring a pair with a single common original height. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E]

private def centeredRemainder (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  f x - transverseNormalCutoff x * f 0

private def cauchyMajorant (R C : ℝ) : ℝ → ℝ :=
  (Icc (-R) R).indicator (fun _ => C)

private theorem cauchy_majorant_integrable (R C : ℝ) : Integrable (cauchyMajorant R C) :=
  (integrableOn_const (C := C) isCompact_Icc.measure_lt_top.ne).integrable_indicator measurableSet_Icc

private theorem centered_remainder_continuous {f : ℝ → ℂ} (hf : Continuous f) :
    Continuous (centeredRemainder f) :=
  hf.sub (transverse_normal_cutoff_lipschitz.continuous.mul continuous_const)

private theorem centered_remainder_zero {f : ℝ → ℂ} {R : ℝ} (hR : 1 ≤ R)
    (hs : ∀ x, R < |x| → f x = 0) {x : ℝ} (hx : R < |x|) : centeredRemainder f x = 0 := by
  have hcut : transverseNormalCutoff x = 0 := by
    unfold transverseNormalCutoff
    rw [massive_normal_cutoff_zero zero_lt_one (hR.trans hx.le), Complex.ofReal_zero]
  simp [centeredRemainder, hs x hx, hcut]

private theorem cauchy_compact {f : ℝ → ℂ} {R : ℝ} (hs : ∀ x, R < |x| → f x = 0) :
    HasCompactSupport f := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R))
  intro x hx
  exact hs x (lt_of_not_ge (fun hh => hx (abs_le.mp hh)))

private theorem centered_remainder_bound {f : ℝ → ℂ} {L : ℝ≥0} {B : ℝ}
    (hL : LipschitzWith L f) (hB : ‖f 0‖ ≤ B) (x : ℝ) :
    ‖centeredRemainder f x‖ ≤ ((L : ℝ) + B) * |x| := by
  rw [show centeredRemainder f x = (f x - f 0) + (1 - transverseNormalCutoff x) * f 0 by
    unfold centeredRemainder; ring]
  apply (norm_add_le _ _).trans
  rw [add_mul, norm_mul]
  apply add_le_add
  · simpa [Real.norm_eq_abs] using hL.norm_sub_le x 0
  · rw [mul_comm B]
    exact mul_le_mul (transverse_cutoff_defect_bound x) hB (norm_nonneg _) (abs_nonneg _)

private theorem Plane.centered_cauchy_split (diamond : Plane E) (ε : Evolution)
    (k : Height) {f : ℝ → ℂ} {R : ℝ} (hR : 1 ≤ R) (hf : Continuous f)
    (hs : ∀ x, R < |x| → f x = 0) :
    (∫ x, diamond.poleCoefficient ε k x * f x) =
      (∫ x, diamond.poleCoefficient ε k x * centeredRemainder f x) +
        f 0 * (∫ x, diamond.poleCoefficient ε k x * transverseNormalCutoff x) := by
  have hp := diamond.pole_coefficient_continuous ε k
  have hI : Integrable (fun x => diamond.poleCoefficient ε k x * centeredRemainder f x) :=
    (hp.mul (centered_remainder_continuous hf)).integrable_of_hasCompactSupport
      (cauchy_compact (fun _ hx => centered_remainder_zero hR hs hx)).mul_left
  have hJ : Integrable (fun x => diamond.poleCoefficient ε k x * transverseNormalCutoff x) :=
    (hp.mul transverse_normal_cutoff_lipschitz.continuous).integrable_of_hasCompactSupport
      transverse_normal_cutoff_compact.mul_left
  rw [← integral_const_mul, ← integral_add hI (hJ.const_mul _)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by dsimp [centeredRemainder]; ring

private theorem Plane.centered_cauchy_remainder_le (diamond : Plane E) (ε : Evolution)
    (k : Height) {f : ℝ → ℂ} {R B : ℝ} (hR : 1 ≤ R) {L : ℝ≥0}
    (hs : ∀ x, R < |x| → f x = 0) (hL : LipschitzWith L f) (hB : ‖f 0‖ ≤ B) :
    ∀ᵐ x : ℝ ∂volume,
      ‖diamond.poleCoefficient ε k x * centeredRemainder f x‖ ≤ cauchyMajorant R ((L : ℝ) + B) x := by
  have hnon : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [hnon] with x hx
  by_cases hb : x ∈ Icc (-R) R
  · rw [cauchyMajorant, indicator_of_mem hb, norm_mul]
    calc
      _ ≤ |x|⁻¹ * (((L : ℝ) + B) * |x|) :=
        mul_le_mul (diamond.pole_coefficient_off_shell_bound ε k hx)
          (centered_remainder_bound hL hB x) (norm_nonneg _) (by positivity)
      _ = _ := by field_simp [abs_ne_zero.mpr hx]
  · simp [cauchyMajorant, indicator_of_notMem hb,
      centered_remainder_zero hR hs (lt_of_not_ge fun H => hb (abs_le.mp H))]

/-- The same eventual bound works for all centered tests with the
specified radius, Lipschitz constant and value at the pole. -/
theorem Plane.rest_threshold_centered_cauchy_eventual_bound (diamond : Plane E)
    (ε : Evolution) (R : ℝ) (hR : 1 ≤ R) (L : ℝ≥0) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C ≥ 0, ∀ᶠ k : Height in poleBoundaryHeights,
      ∀ f : ℝ → ℂ, LipschitzWith L f → ‖f 0‖ ≤ B → (∀ x, R < |x| → f x = 0) →
        ‖∫ x, diamond.poleCoefficient ε k x * f x‖ ≤ C := by
  let c := ‖-(Complex.I * (Real.pi : ℂ) * (diamond.eta ε : ℂ))‖ + 1
  have hc : 0 ≤ c := by positivity
  let M := cauchyMajorant R ((L : ℝ) + B)
  have hM := cauchy_majorant_integrable R ((L : ℝ) + B)
  have hMp : 0 ≤ ∫ x, M x := integral_nonneg (fun x => indicator_nonneg (fun _ _ => by positivity) x)
  refine ⟨(∫ x, M x) + B * c, by positivity, ?_⟩
  have hk := (diamond.transverse_normal_cutoff_limit ε).norm
    (eventually_le_nhds (lt_add_one _))
  filter_upwards [hk] with k hk f hL hf0 hs
  rw [diamond.centered_cauchy_split ε k hR hL.continuous hs]
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  exact add_le_add
    (norm_integral_le_of_norm_le hM (diamond.centered_cauchy_remainder_le ε k hR hs hL hf0))
    (mul_le_mul hf0 hk (norm_nonneg _) hB)

/-- Moving centered axial tests converge with a rescaled positive
height, while preserving the side fixed by the evolution label. -/
theorem Plane.rest_threshold_centered_cauchy_limit (diamond : Plane E) (ε : Evolution)
    {k : Height → Height} (hk : Tendsto k poleBoundaryHeights poleBoundaryHeights)
    (f : Height → ℝ → ℂ) (f₀ : ℝ → ℂ) {R B : ℝ} (hR : 1 ≤ R)
    {L L₀ : ℝ≥0} (hfc : ∀ h, Continuous (f h))
    (hfL : ∀ᶠ h in poleBoundaryHeights, LipschitzWith L (f h) ∧ ‖f h 0‖ ≤ B)
    (hf₀ : LipschitzWith L₀ f₀)
    (hfs : ∀ᶠ h in poleBoundaryHeights, ∀ x, R < |x| → f h x = 0) (hf₀s : ∀ x, R < |x| → f₀ x = 0)
    (hf : ∀ x, Tendsto (fun h => f h x) poleBoundaryHeights (𝓝 (f₀ x))) :
    Tendsto (fun h => ∫ x, diamond.poleCoefficient ε (k h) x * f h x) poleBoundaryHeights
      (𝓝 (complexShellPV f₀ - Complex.I * (Real.pi : ℂ) * (diamond.eta ε : ℂ) * f₀ 0)) := by
  let g (h : Height) (x : ℝ) := f h x - f₀ x
  have hg (x : ℝ) : Tendsto (fun h => g h x) poleBoundaryHeights (𝓝 0) := by
    simpa only [g, sub_self] using (hf x).sub_const (f₀ x)
  have hgs : ∀ᶠ h in poleBoundaryHeights, ∀ x, R < |x| → g h x = 0 := by
    filter_upwards [hfs] with h hs x hx
    simp [g, hs x hx, hf₀s x hx]
  have hgc (h : Height) : Continuous (g h) := (hfc h).sub hf₀.continuous
  have hrest :
      Tendsto (fun h => ∫ x, diamond.poleCoefficient ε (k h) x * centeredRemainder (g h) x)
        poleBoundaryHeights (𝓝 0) := by
    rw [← integral_zero (μ := (volume : Measure ℝ)) (G := ℂ)]
    refine tendsto_integral_filter_of_dominated_convergence _
      (Eventually.of_forall fun h => ((diamond.pole_coefficient_continuous ε (k h)).mul
        (centered_remainder_continuous (hgc h))).aestronglyMeasurable)
      ?_ (cauchy_majorant_integrable R (↑(L + L₀ : ℝ≥0) + (B + ‖f₀ 0‖))) ?_
    · filter_upwards [hfL, hgs] with h hh hs
      apply diamond.centered_cauchy_remainder_le ε (k h) hR hs (hh.1.sub hf₀)
      exact (norm_sub_le _ _).trans (add_le_add_right hh.2 _)
    · have hnon : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
      filter_upwards [hnon] with x hx
      have H := ((diamond.pole_coefficient_off_shell_limit ε hx).comp hk).mul
        ((hg x).sub ((hg 0).const_mul (transverseNormalCutoff x)))
      simpa only [centeredRemainder, mul_zero, sub_zero, Function.comp_def] using H
  have hzero : Tendsto (fun h => ∫ x, diamond.poleCoefficient ε (k h) x * g h x)
      poleBoundaryHeights (𝓝 0) := by
    have H := hrest.add ((hg 0).mul ((diamond.transverse_normal_cutoff_limit ε).comp hk))
    simp only [zero_mul, add_zero] at H
    apply H.congr'
    filter_upwards [hgs] with h hs
    exact (diamond.centered_cauchy_split ε (k h) hR (hgc h) hs).symm
  have H := ((diamond.transverse_normal_single_test ε hf₀ (cauchy_compact hf₀s)).comp hk).add hzero
  simp only [add_zero] at H
  apply H.congr'
  filter_upwards [hgs] with h hs
  have hp := diamond.pole_coefficient_continuous ε (k h)
  have hi : Integrable (fun x => diamond.poleCoefficient ε (k h) x * f₀ x) :=
    (hp.mul hf₀.continuous).integrable_of_hasCompactSupport (cauchy_compact hf₀s).mul_left
  have hj : Integrable (fun x => diamond.poleCoefficient ε (k h) x * g h x) :=
    (hp.mul (hgc h)).integrable_of_hasCompactSupport (cauchy_compact hs).mul_left
  change (∫ x, diamond.poleCoefficient ε (k h) x * f₀ x) +
    (∫ x, diamond.poleCoefficient ε (k h) x * g h x) = _
  rw [← integral_add hi hj]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by dsimp only [g]; ring

end UV.SectorPlane
