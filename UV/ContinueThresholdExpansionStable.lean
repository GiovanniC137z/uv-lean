import UV.ContinueThresholdExpansionLimit

/-! Common-height boundary of the canonical stable-half scalar pair
at the positive unequal-mass sum threshold. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology ContDiff UV.SectorPlane

variable {E : Type*} [NormedAddCommGroup E]

private def thresholdExpansionHeightCutoff : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

private def Plane.thresholdExpansionRoot (diamond : Plane E) (ε : Evolution)
    (m : ℝ) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  principalSqrt ((↑(m ^ 2 + p.2.2 ^ 2) : ℂ) - Complex.I * ↑(diamond.eta ε * p.1))

private theorem Plane.threshold_expansion_root_contDiff (diamond : Plane E) (ε : Evolution)
    {m : ℝ} (hm : 0 < m) :
    ContDiff ℝ 1 (diamond.thresholdExpansionRoot ε m) := by
  let w : ℝ × (ℝ × ℝ) → ℂ := fun p => (↑(m ^ 2 + p.2.2 ^ 2) : ℂ) -
    Complex.I * ↑(diamond.eta ε * p.1)
  have hw : ContDiff ℝ 1 w :=
    (Complex.ofRealCLM.contDiff.comp (by fun_prop : ContDiff ℝ 1 (fun p : ℝ × (ℝ × ℝ) =>
      m ^ 2 + p.2.2 ^ 2))).sub (contDiff_const.mul
        (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst)))
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hwp : w p ∈ {z : ℂ | 0 < z.re} := by
    change 0 < (w p).re
    simp only [w, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
    positivity
  exact ((principalSqrt_analyticOnNhd_rightHalfPlane _ hwp).contDiffAt.restrict_scalars ℝ).comp p hw.contDiffAt

private theorem Plane.threshold_expansion_root_re (diamond : Plane E) (ε : Evolution)
    (m : ℝ) (p : ℝ × (ℝ × ℝ)) :
    Real.sqrt (m ^ 2 + p.2.2 ^ 2) ≤ (diamond.thresholdExpansionRoot ε m p).re := by
  have H := principalSqrt_re_lower
    ((↑(m ^ 2 + p.2.2 ^ 2) : ℂ) - Complex.I * ↑(diamond.eta ε * p.1))
  simpa only [Plane.thresholdExpansionRoot, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero] using H

private def unequalThresholdShellSquares (m₁ m₂ : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  ((z.1 + m₁) ^ 2 - z.2 ^ 2, (z.1 - m₂) ^ 2 - z.2 ^ 2)

def Plane.unequalThresholdStableNumerator (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (m₁ m₂ a b : ℝ) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  diamond.restStableNormalNumerator ε₁ ε₂ 0 a b p.1 (unequalThresholdShellSquares m₁ m₂ p.2)

private theorem Plane.unequal_threshold_stable_numerator_continuous (diamond : Plane E)
    (ε₁ ε₂ : Evolution) (h : Height) (m₁ m₂ a b : ℝ) :
    Continuous (fun z => diamond.unequalThresholdStableNumerator ε₁ ε₂ m₁ m₂ a b ((h : ℝ), z)) :=
  (diamond.rest_stable_normal_numerator_continuous ε₁ ε₂ 0 a b h).comp
    (by unfold unequalThresholdShellSquares; fun_prop)

private theorem Plane.unequal_threshold_stable_numerator_eq (diamond : Plane E)
    (ε₁ ε₂ : Evolution) (h : Height) {a b m₁ m₂ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (q : MassiveMomentum) (hq : |q.1| ≤ min m₁ m₂ / 2) :
    let φ := fun z => Complex.exp (-principalSqrt z)
    diamond.unequalThresholdStableNumerator ε₁ ε₂ m₁ m₂ a b ((h : ℝ), (q.1, ‖q.2‖)) =
      diamond.shiftedScalarNumerator ε₁ ε₂ h φ φ a b (axialTransfer m₁) (axialTransfer (-m₂)) q := by
  intro φ
  have h₁ : |q.1| ≤ m₁ / 2 := hq.trans (by linarith [min_le_left m₁ m₂])
  have h₂ : |q.1| ≤ m₂ / 2 := hq.trans (by linarith [min_le_right m₁ m₂])
  have hp := (threshold_axial_signs hm₁ h₁).1
  have hn := (threshold_axial_signs hm₂ h₂).2
  simp only [Plane.shiftedScalarNumerator, axial_transfer_coordinates, Prod.fst_add, Prod.snd_add,
    add_zero, shellSquare, ← sub_eq_add_neg, axialSign, if_pos hp, if_neg hn.not_gt, if_pos hn,
    Complex.ofReal_one, Complex.ofReal_neg, mul_one]
  rw [diamond.stable_scalar_kernel_readout ε₁ ha h, diamond.stable_scalar_kernel_readout ε₂ hb h,
    diamond.stable_half_analytic_form ε₁ h, diamond.stable_half_analytic_form ε₂ h]
  simp only [Plane.unequalThresholdStableNumerator, Plane.restStableNormalNumerator,
    Plane.shiftedShellCoefficient, unequalThresholdShellSquares, zero_pow (by norm_num : 2 ≠ 0), add_zero]
  have hphase : -(diamond.eta ε₁ : ℂ) * (diamond.eta ε₂ : ℂ) * (-1 : ℂ) =
      (diamond.eta ε₁ : ℂ) * (diamond.eta ε₂ : ℂ) := by ring
  rw [hphase]
  rfl

/-- Analytic extension of the remote factors and stable numerator on the
two timelike rims, with the original normalized spatial average. -/
def Plane.unequalThresholdStableAmplitude (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (m₁ m₂ a b : ℝ) (f : MassiveMomentum → ℂ) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  (thresholdExpansionHeightCutoff p.1 : ℂ) * coneSpatialMean f p.2 *
    diamond.unequalThresholdStableNumerator ε₁ ε₂ m₁ m₂ a b p *
    ((((p.2.1 : ℂ) + (m₁ : ℂ) + diamond.thresholdExpansionRoot ε₁ m₁ p) *
      ((p.2.1 : ℂ) - (m₂ : ℂ) - diamond.thresholdExpansionRoot ε₂ m₂ p))⁻¹)

private theorem threshold_expansion_mean_support {f : MassiveMomentum → ℂ} (hs : HasCompactSupport f) :
    HasCompactSupport (coneSpatialMean f) := by
  obtain ⟨R, hR⟩ := hs.isBounded.subset_closedBall (0 : MassiveMomentum)
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × ℝ) R)
  intro z hz
  have he (w : ConeSpatialSphere) : f (z.1, z.2 • (w : Spatial)) = 0 := by
    by_contra hw
    apply hz
    have h := hR (subset_tsupport f hw)
    simpa [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, norm_smul,
      Real.norm_eq_abs, cone_spatial_direction_norm] using h
  simp [coneSpatialMean, he]

private theorem Plane.unequal_threshold_stable_amplitude_contDiff (diamond : Plane E)
    (ε₁ ε₂ : Evolution) (a b : ℝ) {m₁ m₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) {f : MassiveMomentum → ℂ}
    (hf : ContDiff ℝ 2 f)
    (hSupp : ∀ q, f q ≠ 0 → |q.1| ≤ min m₁ m₂ / 2 ∧ ‖q.2‖ ≤ min m₁ m₂ / 8) :
    ContDiff ℝ 1 (diamond.unequalThresholdStableAmplitude ε₁ ε₂ m₁ m₂ a b f) := by
  let M := min m₁ m₂
  have hM : 0 < M := lt_min hm₁ hm₂
  have hle₁ : M ≤ m₁ := min_le_left _ _
  have hle₂ : M ≤ m₂ := min_le_right _ _
  let X := ℝ × (ℝ × ℝ)
  let N (p : X) := (p.1, unequalThresholdShellSquares m₁ m₂ p.2)
  have hN : ContDiff ℝ 1 N := by unfold N unequalThresholdShellSquares; fun_prop
  have hMean : ContDiff ℝ 1 (coneSpatialMean f) := (cone_spatial_mean_contDiff hf).of_le (by norm_num)
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : |p.2.1| < 3 * M / 4 ∧ |p.2.2| < M / 4
  · have hx := abs_lt.mp hp.1
    have hplus : |p.2.2| < p.2.1 + m₁ := by linarith only [hp.2, hx.1, hle₁]
    have hminus : |p.2.2| < m₂ - p.2.1 := by linarith only [hp.2, hx.2, hle₂]
    have h₁ : 0 < (N p).2.1 + 0 ^ 2 := by
      have H := (sq_lt_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hplus.le)).mpr hplus
      rw [sq_abs] at H
      dsimp [N, unequalThresholdShellSquares]
      linarith only [H]
    have h₂ : 0 < (N p).2.2 + 0 ^ 2 := by
      have H := (sq_lt_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hminus.le)).mpr hminus
      rw [sq_abs] at H
      dsimp [N, unequalThresholdShellSquares]
      nlinarith only [H]
    have hU : ContDiffAt ℝ 1 (diamond.unequalThresholdStableNumerator ε₁ ε₂ m₁ m₂ a b) p :=
      ((diamond.rest_stable_normal_numerator_contDiffAt ε₁ ε₂ 0 a b (N p) h₁ h₂).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp p hN.contDiffAt
    let A (p : X) := (p.2.1 : ℂ) + (m₁ : ℂ) + diamond.thresholdExpansionRoot ε₁ m₁ p
    let B (p : X) := (p.2.1 : ℂ) - (m₂ : ℂ) - diamond.thresholdExpansionRoot ε₂ m₂ p
    have hX := Complex.ofRealCLM.contDiff.comp (contDiff_fst.comp
      (contDiff_snd : ContDiff ℝ 1 (Prod.snd : X → ℝ × ℝ)))
    have hA : ContDiff ℝ 1 A := (hX.add contDiff_const).add (diamond.threshold_expansion_root_contDiff ε₁ hm₁)
    have hB : ContDiff ℝ 1 B := (hX.sub contDiff_const).sub (diamond.threshold_expansion_root_contDiff ε₂ hm₂)
    have hAn : A p ≠ 0 := by
      intro hn
      have H := congrArg Complex.re hn
      simp only [A, Complex.add_re, Complex.ofReal_re, Complex.zero_re] at H
      linarith only [H, hx.1, hm₁, hle₁, diamond.threshold_expansion_root_re ε₁ m₁ p,
        rest_threshold_mass_le_radius_root hm₁ p.2.2]
    have hBn : B p ≠ 0 := by
      intro hn
      have H := congrArg Complex.re hn
      simp only [B, Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at H
      linarith only [H, hx.2, hm₂, hle₂, diamond.threshold_expansion_root_re ε₂ m₂ p,
        rest_threshold_mass_le_radius_root hm₂ p.2.2]
    have hcut : ContDiff ℝ 1 (fun p : X => (thresholdExpansionHeightCutoff p.1 : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (thresholdExpansionHeightCutoff.contDiff.comp contDiff_fst)
    exact ((hcut.mul (hMean.comp contDiff_snd)).contDiffAt.mul hU).mul
      ((hA.mul hB).contDiffAt.inv (mul_ne_zero hAn hBn))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    push_neg at hp
    have hloc : ∀ᶠ q in 𝓝 p, M / 2 < |q.2.1| ∨ M / 8 < |q.2.2| := by
      by_cases hx : |p.2.1| < 3 * M / 4
      · have hr : M / 8 < |p.2.2| := by linarith only [hM, hp hx]
        have hc : Continuous (fun p : X => |p.2.2|) := by fun_prop
        exact (hc.continuousAt.eventually (eventually_gt_nhds hr)).mono (fun _ h => Or.inr h)
      · have ha : M / 2 < |p.2.1| := by linarith only [hM, le_of_not_gt hx]
        have hc : Continuous (fun p : X => |p.2.1|) := by fun_prop
        exact (hc.continuousAt.eventually (eventually_gt_nhds ha)).mono (fun _ h => Or.inl h)
    filter_upwards [hloc] with q hq
    have hz (w : ConeSpatialSphere) : f (q.2.1, q.2.2 • (w : Spatial)) = 0 := by
      by_contra hw
      have H := hSupp _ hw
      have Hr : |q.2.2| ≤ M / 8 := by
        simpa [norm_smul, cone_spatial_direction_norm w, Real.norm_eq_abs, M] using H.2
      exact hq.elim (fun h => h.not_ge H.1) (fun h => h.not_ge Hr)
    simp [Plane.unequalThresholdStableAmplitude, coneSpatialMean, hz]

private theorem Plane.unequal_threshold_stable_amplitude_compact (diamond : Plane E)
    (ε₁ ε₂ : Evolution) (m₁ m₂ a b : ℝ) {f : MassiveMomentum → ℂ} (hs : HasCompactSupport f) :
    HasCompactSupport (diamond.unequalThresholdStableAmplitude ε₁ ε₂ m₁ m₂ a b f) := by
  let S := tsupport (coneSpatialMean f)
  have hS : IsCompact S := threshold_expansion_mean_support hs
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) 2 |>.prod hS)
  intro p hp
  by_cases h : p.1 ∈ Metric.closedBall (0 : ℝ) 2
  · have hz : coneSpatialMean f p.2 = 0 := by
      by_contra hn
      exact hp ⟨h, subset_tsupport _ hn⟩
    simp [Plane.unequalThresholdStableAmplitude, hz]
  · have hd : 2 ≤ dist p.1 0 := le_of_lt (lt_of_not_ge h)
    simp [Plane.unequalThresholdStableAmplitude, thresholdExpansionHeightCutoff.zero_of_le_dist hd]

/-- The canonical stable-half scalar pair, in the actual symmetric
routing at transfer m₁+m₂. Compact C² tests are localized around the
common zero in the translated axial strip and the stated spatial ball. -/
theorem Plane.unequal_threshold_stable_scalar_pairing_tendsto (diamond : Plane E) (ε₁ ε₂ : Evolution)
    {a b m₁ m₂ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    {f : MassiveMomentum → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)
    (hSupp : ∀ q, f (q + thresholdRestCenter m₁ m₂) ≠ 0 →
      |q.1| ≤ min m₁ m₂ / 2 ∧ ‖q.2‖ ≤ min m₁ m₂ / 8) :
    let φ := fun z => Complex.exp (-principalSqrt z)
    let g := fun q => f (q + thresholdRestCenter m₁ m₂)
    Tendsto (fun h : Height => diamond.shiftedScalarPairing ε₁ ε₂ h φ φ a b m₁ m₂
        (axialTransfer ((m₁ + m₂) / 2)) (axialTransfer (-((m₁ + m₂) / 2))) f)
      poleBoundaryHeights
      (𝓝 (directed ((4 * Real.pi) • ∫ r in Ioi (0 : ℝ), (↑(unequalThresholdRadialWeight m₁ m₂ r) : ℂ) *
        unequalThresholdAxialBoundary (diamond.eta ε₁) (diamond.eta ε₂) m₁ m₂
          (fun z => diamond.unequalThresholdStableAmplitude ε₁ ε₂ m₁ m₂ a b g (0,z)) r))) := by
  intro φ g
  have hg : ContDiff ℝ 2 g := hf.comp (contDiff_id.add contDiff_const)
  have hgS : HasCompactSupport g := hs.comp_homeomorph (Homeomorph.addRight (thresholdRestCenter m₁ m₂))
  have hF := diamond.unequal_threshold_stable_amplitude_contDiff ε₁ ε₂ a b hm₁ hm₂ hg hSupp
  have hFs := diamond.unequal_threshold_stable_amplitude_compact ε₁ ε₂ m₁ m₂ a b hgS
  have hlim := (diamond.unequal_threshold_radial_difference_limit ε₁ ε₂ hm₁ hm₂ hF hFs).const_smul (4 * Real.pi)
  apply (directed_shell_readout_continuous.continuousAt.tendsto.comp hlim).congr'
  have hheight : ∀ᶠ h : Height in poleBoundaryHeights, (h : ℝ) ≤ 1 :=
    pole_height_tendsto_zero (eventually_le_nhds zero_lt_one)
  filter_upwards [hheight] with h hh
  rw [diamond.unequal_threshold_translate_pairing ε₁ ε₂ h φ φ a b m₁ m₂ f]
  rw [diamond.unequal_threshold_pairing_radial_of_numerator ε₁ ε₂ h φ φ a b hm₁ hm₂ hg.continuous hgS
    (diamond.unequal_threshold_stable_numerator_continuous ε₁ ε₂ h m₁ m₂ a b)
    (fun q hq => diamond.unequal_threshold_stable_numerator_eq ε₁ ε₂ h ha hb hm₁ hm₂ q (hSupp q hq).1)]
  have hcut : thresholdExpansionHeightCutoff (h : ℝ) = 1 := by
    apply thresholdExpansionHeightCutoff.one_of_mem_closedBall
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_pos h.property] using hh
  simp only [Function.comp_apply, Plane.unequalThresholdStableAmplitude, hcut, Complex.ofReal_one, one_mul,
    Plane.thresholdExpansionRoot, Plane.restThresholdRoot, Plane.unequalThresholdRemoteFactor]

end UV.SectorPlane
