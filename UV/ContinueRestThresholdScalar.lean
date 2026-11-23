import UV.ContinueRestThresholdLimit
import UV.ContinueTransverseSphere
import UV.ContinueTransverseRestScalar
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Boundary limit of the actual shifted scalar pair at the degenerate
rest threshold. The compact test is localized where the two normalized
running units remain on the forward and backward rays of one plane. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology ContDiff UV.SectorPlane

variable {E : Type*} [NormedAddCommGroup E]

private def thresholdHeightCutoff : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

private def Plane.restThresholdAnalyticRoot (diamond : Plane E) (ε : Evolution)
    (m : ℝ) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  principalSqrt ((↑(m ^ 2 + p.2.2 ^ 2) : ℂ) - Complex.I * ↑(diamond.eta ε * p.1))

private theorem Plane.rest_threshold_analytic_root_re (diamond : Plane E) (ε : Evolution)
    (m : ℝ) (p : ℝ × (ℝ × ℝ)) :
    Real.sqrt (m ^ 2 + p.2.2 ^ 2) ≤ (diamond.restThresholdAnalyticRoot ε m p).re := by
  have H := principalSqrt_re_lower
    ((↑(m ^ 2 + p.2.2 ^ 2) : ℂ) - Complex.I * ↑(diamond.eta ε * p.1))
  simpa only [Plane.restThresholdAnalyticRoot, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero] using H

private theorem Plane.rest_threshold_analytic_root_contDiff (diamond : Plane E) (ε : Evolution)
    {m : ℝ} (hm : 0 < m) :
    ContDiff ℝ 1 (diamond.restThresholdAnalyticRoot ε m) := by
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

private def Plane.restThresholdAnalyticKernel (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (φ₁ φ₂ : ℂ → ℂ) (a₁ a₂ m : ℝ) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  (diamond.eta ε₁ : ℂ) * (diamond.eta ε₂ : ℂ) *
    (φ₁ (-(a₁ : ℂ)^2 * (↑((p.2.1 + m) ^ 2 - p.2.2 ^ 2) + Complex.I * ↑(diamond.eta ε₁ * p.1))) *
      φ₂ (-(a₂ : ℂ)^2 * (↑((p.2.1 - m) ^ 2 - p.2.2 ^ 2) + Complex.I * ↑(diamond.eta ε₂ * p.1))))

private theorem Plane.rest_threshold_analytic_kernel_contDiff (diamond : Plane E)
    (ε₁ ε₂ : Evolution) {φ₁ φ₂ : ℂ → ℂ} (hφ₁ : ContDiff ℝ 1 φ₁) (hφ₂ : ContDiff ℝ 1 φ₂)
    (a₁ a₂ m : ℝ) :
    ContDiff ℝ 1 (diamond.restThresholdAnalyticKernel ε₁ ε₂ φ₁ φ₂ a₁ a₂ m) := by
  let X := ℝ × (ℝ × ℝ)
  have hZ (c : ℝ) (ε : Evolution) : ContDiff ℝ 1 (fun p : X =>
      (↑((p.2.1 + c) ^ 2 - p.2.2 ^ 2) : ℂ) + Complex.I * ↑(diamond.eta ε * p.1)) :=
    (Complex.ofRealCLM.contDiff.comp (by fun_prop : ContDiff ℝ 1
      (fun p : X => (p.2.1 + c) ^ 2 - p.2.2 ^ 2))).add
        (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst)))
  exact contDiff_const.mul ((hφ₁.comp (contDiff_const.mul (hZ m ε₁))).mul
    (hφ₂.comp (contDiff_const.mul (by simpa only [sub_eq_add_neg] using hZ (-m) ε₂))))

private theorem threshold_spatial_mean_support {f : MassiveMomentum → ℂ} (hs : HasCompactSupport f) :
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

private theorem threshold_spatial_mean_strip {f : MassiveMomentum → ℂ} {m : ℝ}
    (hfStrip : ∀ q, f q ≠ 0 → |q.1| ≤ m / 2) {z : ℝ × ℝ} (hz : m / 2 < |z.1|) :
    coneSpatialMean f z = 0 := by
  have hf (w : ConeSpatialSphere) : f (z.1, z.2 • (w : Spatial)) = 0 := by
    by_contra h
    exact hz.not_ge (hfStrip _ h)
  simp [coneSpatialMean, hf]

/-- Local threshold amplitude after angular averaging and remote-root
factoring. Height zero is included by analytic continuation of the
remote factors and the specified smooth profiles. -/
def Plane.restThresholdTestAmplitude (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (m : ℝ) (f : MassiveMomentum → ℂ) (U : ℝ × (ℝ × ℝ) → ℂ) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  (thresholdHeightCutoff p.1 : ℂ) * coneSpatialMean f p.2 * U p *
    ((((p.2.1 : ℂ) + (m : ℂ) + diamond.restThresholdAnalyticRoot ε₁ m p) *
      ((p.2.1 : ℂ) - (m : ℂ) - diamond.restThresholdAnalyticRoot ε₂ m p))⁻¹)

private theorem Plane.rest_threshold_test_amplitude_contDiff (diamond : Plane E)
    (ε₁ ε₂ : Evolution) {m ρ : ℝ} (hm : 0 < m) {f : MassiveMomentum → ℂ}
    (hMean : ContDiff ℝ 1 (coneSpatialMean f))
    {U : ℝ × (ℝ × ℝ) → ℂ} (hU : ∀ p, |p.2.1| < 3 * m / 4 → |p.2.2| < ρ → ContDiffAt ℝ 1 U p)
    {R : ℝ} (hR : R < ρ)
    (hfStrip : ∀ q, f q ≠ 0 → |q.1| ≤ m / 2)
    (hfRadius : ∀ q, f q ≠ 0 → ‖q.2‖ ≤ R) :
    ContDiff ℝ 1 (diamond.restThresholdTestAmplitude ε₁ ε₂ m f U) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : |p.2.1| < 3 * m / 4 ∧ |p.2.2| < ρ
  · let A := fun p : ℝ × (ℝ × ℝ) =>
      (p.2.1 : ℂ) + (m : ℂ) + diamond.restThresholdAnalyticRoot ε₁ m p
    let B := fun p : ℝ × (ℝ × ℝ) =>
      (p.2.1 : ℂ) - (m : ℂ) - diamond.restThresholdAnalyticRoot ε₂ m p
    have hx := Complex.ofRealCLM.contDiff.comp (contDiff_fst.comp
      (contDiff_snd : ContDiff ℝ 1 (Prod.snd : ℝ × (ℝ × ℝ) → ℝ × ℝ)))
    have hAc : ContDiff ℝ 1 A := (hx.add contDiff_const).add
      (diamond.rest_threshold_analytic_root_contDiff ε₁ hm)
    have hBc : ContDiff ℝ 1 B := (hx.sub contDiff_const).sub
      (diamond.rest_threshold_analytic_root_contDiff ε₂ hm)
    have hAp : A p ≠ 0 := by
      intro hh
      have H := congrArg Complex.re hh
      simp only [A, Complex.add_re, Complex.ofReal_re, Complex.zero_re] at H
      linarith only [H, (abs_lt.mp hp.1).1, hm, diamond.rest_threshold_analytic_root_re ε₁ m p,
        rest_threshold_mass_le_radius_root hm p.2.2]
    have hBp : B p ≠ 0 := by
      intro hh
      have H := congrArg Complex.re hh
      simp only [B, Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at H
      linarith only [H, (abs_lt.mp hp.1).2, hm, diamond.rest_threshold_analytic_root_re ε₂ m p,
        rest_threshold_mass_le_radius_root hm p.2.2]
    have hcut : ContDiff ℝ 1 (fun p : ℝ × (ℝ × ℝ) => (thresholdHeightCutoff p.1 : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (thresholdHeightCutoff.contDiff.comp contDiff_fst)
    exact ((hcut.mul (hMean.comp contDiff_snd)).contDiffAt.mul (hU p hp.1 hp.2)).mul
      ((hAc.mul hBc).contDiffAt.inv (mul_ne_zero hAp hBp))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    push_neg at hp
    by_cases ht : |p.2.1| < 3 * m / 4
    · have hlt : R < |p.2.2| := hR.trans_le (hp ht)
      have hc : Continuous (fun p : ℝ × (ℝ × ℝ) => |p.2.2|) := by fun_prop
      filter_upwards [hc.continuousAt.eventually (eventually_gt_nhds hlt)] with q hq
      have hz (w : ConeSpatialSphere) : f (q.2.1, q.2.2 • (w : Spatial)) = 0 := by
        by_contra hw
        have H := hfRadius _ hw
        change ‖q.2.2 • (w : Spatial)‖ ≤ R at H
        rw [norm_smul, cone_spatial_direction_norm w, mul_one, Real.norm_eq_abs] at H
        exact hq.not_ge H
      simp [Plane.restThresholdTestAmplitude, coneSpatialMean, hz]
    · have hlt : m / 2 < |p.2.1| := by linarith [le_of_not_gt ht]
      have hc : Continuous (fun p : ℝ × (ℝ × ℝ) => |p.2.1|) := by fun_prop
      filter_upwards [hc.continuousAt.eventually (eventually_gt_nhds hlt)] with q hq
      simp [Plane.restThresholdTestAmplitude, threshold_spatial_mean_strip hfStrip hq]

private theorem Plane.rest_threshold_test_amplitude_compact (diamond : Plane E)
    (ε₁ ε₂ : Evolution) (m : ℝ) {f : MassiveMomentum → ℂ} (U : ℝ × (ℝ × ℝ) → ℂ)
    (hf : HasCompactSupport f) :
    HasCompactSupport (diamond.restThresholdTestAmplitude ε₁ ε₂ m f U) := by
  let S := tsupport (coneSpatialMean f)
  have hS : IsCompact S := threshold_spatial_mean_support hf
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) 2 |>.prod hS)
  intro p hp
  by_cases h : p.1 ∈ Metric.closedBall (0 : ℝ) 2
  · have hnot : p.2 ∉ S := fun h' => hp ⟨h, h'⟩
    have hz : coneSpatialMean f p.2 = 0 := by
      by_contra hn
      exact hnot (subset_tsupport _ hn)
    simp [Plane.restThresholdTestAmplitude, hz]
  · have hdist : 2 ≤ dist p.1 0 := le_of_lt (lt_of_not_ge h)
    simp [Plane.restThresholdTestAmplitude, thresholdHeightCutoff.zero_of_le_dist hdist]

private theorem Plane.rest_threshold_scalar_pairing_tendsto_of_numerator
    (diamond : Plane E) (ε₁ ε₂ : Evolution) (φ₁ φ₂ : ℂ → ℂ) (a₁ a₂ : ℝ)
    {m : ℝ} (hm : 0 < m) {f : MassiveMomentum → ℂ} (hf : Continuous f)
    (hs : HasCompactSupport f) {U : ℝ × (ℝ × ℝ) → ℂ}
    (hF : ContDiff ℝ 1 (diamond.restThresholdTestAmplitude ε₁ ε₂ m f U))
    (hUc : ∀ h : Height, Continuous (fun z => U ((h : ℝ), z)))
    (hU : ∀ (h : Height) q, f q ≠ 0 → U ((h : ℝ), (q.1, ‖q.2‖)) =
      diamond.shiftedScalarNumerator ε₁ ε₂ h φ₁ φ₂ a₁ a₂ (axialTransfer m) (axialTransfer (-m)) q) :
    Tendsto (fun h : Height =>
      diamond.shiftedScalarPairing ε₁ ε₂ h φ₁ φ₂ a₁ a₂ m m (axialTransfer m) (axialTransfer (-m)) f)
      poleBoundaryHeights
      (𝓝 (directed ((4 * Real.pi) • ∫ r in Ioi (0 : ℝ),
        (↑((Real.sqrt (m ^ 2 + r ^ 2) + m) / 2) : ℂ) *
          restThresholdAxialBoundary (diamond.eta ε₁) (diamond.eta ε₂) m
            (fun z => diamond.restThresholdTestAmplitude ε₁ ε₂ m f U (0, z)) r))) := by
  have hFs := diamond.rest_threshold_test_amplitude_compact ε₁ ε₂ m U hs
  have hlim := (diamond.rest_threshold_radial_difference_limit ε₁ ε₂ hm hF hFs).const_smul (4 * Real.pi)
  apply (directed_shell_readout_continuous.continuousAt.tendsto.comp hlim).congr'
  have hheight : ∀ᶠ h : Height in poleBoundaryHeights, (h : ℝ) ≤ 1 :=
    pole_height_tendsto_zero (eventually_le_nhds zero_lt_one)
  filter_upwards [hheight] with h hh
  rw [diamond.rest_threshold_scalar_pairing_radial_of_numerator ε₁ ε₂ h φ₁ φ₂ a₁ a₂ hm
    hf hs (hUc h) (hU h)]
  have hcut : thresholdHeightCutoff (h : ℝ) = 1 := by
    apply thresholdHeightCutoff.one_of_mem_closedBall
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_pos h.property] using hh
  simp only [Function.comp_apply, Plane.restThresholdTestAmplitude, hcut, Complex.ofReal_one, one_mul,
    Plane.restThresholdAnalyticRoot, Plane.restThresholdRoot, Plane.restThresholdRemoteFactor]

/-- For positive mass and a compact C² strip-supported test, the shifted
scalar pair at transfer 2m has the tested common-height boundary for
C¹ profiles at their complex arguments. -/
theorem Plane.rest_threshold_scalar_pairing_tendsto (diamond : Plane E) (ε₁ ε₂ : Evolution)
    {φ₁ φ₂ : ℂ → ℂ} (hφ₁ : ContDiff ℝ 1 φ₁) (hφ₂ : ContDiff ℝ 1 φ₂) (a₁ a₂ : ℝ)
    {m : ℝ} (hm : 0 < m) {f : MassiveMomentum → ℂ} (hf : ContDiff ℝ 2 f)
    (hs : HasCompactSupport f) (hfStrip : ∀ q, f q ≠ 0 → |q.1| ≤ m / 2) :
    let U := diamond.restThresholdAnalyticKernel ε₁ ε₂ φ₁ φ₂ a₁ a₂ m
    Tendsto (fun h : Height =>
      diamond.shiftedScalarPairing ε₁ ε₂ h φ₁ φ₂ a₁ a₂ m m (axialTransfer m) (axialTransfer (-m)) f)
      poleBoundaryHeights
      (𝓝 (directed ((4 * Real.pi) • ∫ r in Ioi (0 : ℝ),
        (↑((Real.sqrt (m ^ 2 + r ^ 2) + m) / 2) : ℂ) *
          restThresholdAxialBoundary (diamond.eta ε₁) (diamond.eta ε₂) m
            (fun z => diamond.restThresholdTestAmplitude ε₁ ε₂ m f U (0, z)) r))) := by
  intro U
  have hK : ContDiff ℝ 1 U := diamond.rest_threshold_analytic_kernel_contDiff ε₁ ε₂ hφ₁ hφ₂ a₁ a₂ m
  have hMean : ContDiff ℝ 1 (coneSpatialMean f) := (cone_spatial_mean_contDiff hf).of_le (by norm_num)
  obtain ⟨R, hR⟩ := hs.isBounded.subset_closedBall (0 : MassiveMomentum)
  have hRadius (q : MassiveMomentum) (hq : f q ≠ 0) : ‖q.2‖ ≤ R := by
    have H := hR (subset_tsupport f hq)
    simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff] at H
    exact H.2
  have hF := diamond.rest_threshold_test_amplitude_contDiff ε₁ ε₂ hm hMean
    (fun _ _ _ => hK.contDiffAt) (lt_add_one R) hfStrip hRadius
  refine diamond.rest_threshold_scalar_pairing_tendsto_of_numerator ε₁ ε₂ φ₁ φ₂ a₁ a₂ hm
    hf.continuous hs hF (fun _ => hK.continuous.comp (continuous_const.prodMk continuous_id)) ?_
  intro h q hq
  exact diamond.rest_threshold_kernel_product_eq ε₁ ε₂ h φ₁ φ₂ a₁ a₂ hm q (hfStrip q hq)

/-- Continuous positive-height stable-half readout, analytically
extended through height zero where both shifted shell squares are positive. -/
def Plane.restThresholdStableNumerator (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (m a b : ℝ) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  diamond.restStableNormalNumerator ε₁ ε₂ m a b p.1 (restAxialRadialNormals m (2 * m) p.2)

private theorem Plane.rest_threshold_stable_readout (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (h : Height) (m : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (z : ℝ × ℝ) :
    diamond.restThresholdStableNumerator ε₁ ε₂ m a b ((h : ℝ), z) =
      diamond.restThresholdKernelProduct ε₁ ε₂ h (fun w => Complex.exp (-principalSqrt w))
        (fun w => Complex.exp (-principalSqrt w)) a b m z := by
  rw [Plane.restThresholdKernelProduct, diamond.stable_scalar_kernel_readout ε₁ ha h,
    diamond.stable_scalar_kernel_readout ε₂ hb h, diamond.stable_half_analytic_form ε₁ h,
    diamond.stable_half_analytic_form ε₂ h]
  have him : (2 * m) / 2 = m := by ring
  simp only [Plane.restThresholdStableNumerator, Plane.restStableNormalNumerator,
    Plane.shiftedShellCoefficient, restAxialRadialNormals, him, sub_add_cancel]
  rfl

/-- At the actual degenerate threshold the stable-half profiles have a
common-height tested boundary in the strip |x| ≤ m/2 and ball r ≤ m/8.
There both translated shell arguments stay on their timelike rims. -/
theorem Plane.rest_threshold_stable_scalar_pairing_tendsto (diamond : Plane E) (ε₁ ε₂ : Evolution)
    {a b m : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hm : 0 < m)
    {f : MassiveMomentum → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)
    (hfStrip : ∀ q, f q ≠ 0 → |q.1| ≤ m / 2)
    (hfRadius : ∀ q, f q ≠ 0 → ‖q.2‖ ≤ m / 8) :
    let φ := fun z => Complex.exp (-principalSqrt z)
    let U := diamond.restThresholdStableNumerator ε₁ ε₂ m a b
    Tendsto (fun h : Height =>
      diamond.shiftedScalarPairing ε₁ ε₂ h φ φ a b m m (axialTransfer m) (axialTransfer (-m)) f)
      poleBoundaryHeights
      (𝓝 (directed ((4 * Real.pi) • ∫ r in Ioi (0 : ℝ),
        (↑((Real.sqrt (m ^ 2 + r ^ 2) + m) / 2) : ℂ) *
          restThresholdAxialBoundary (diamond.eta ε₁) (diamond.eta ε₂) m
            (fun z => diamond.restThresholdTestAmplitude ε₁ ε₂ m f U (0, z)) r))) := by
  intro φ U
  let X := ℝ × (ℝ × ℝ)
  let N (p : X) := (p.1, restAxialRadialNormals m (2 * m) p.2)
  have htime : (2 * m) / 2 = m := by ring
  have hN : ContDiff ℝ 1 N := by unfold N restAxialRadialNormals; fun_prop
  have hU (p : X) (hx : |p.2.1| < 3 * m / 4) (hr : |p.2.2| < m / 4) :
      ContDiffAt ℝ 1 U p := by
    have hplus : |p.2.2| < p.2.1 + m := by linarith only [hr, (abs_lt.mp hx).1]
    have hminus : |p.2.2| < m - p.2.1 := by linarith only [hr, (abs_lt.mp hx).2]
    have h₁ : 0 < (N p).2.1 + m ^ 2 := by
      dsimp [N, restAxialRadialNormals]
      rw [htime, sub_add_cancel]
      have H := (sq_lt_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hplus.le)).mpr hplus
      rw [sq_abs] at H
      linarith
    have h₂ : 0 < (N p).2.2 + m ^ 2 := by
      dsimp [N, restAxialRadialNormals]
      rw [htime, sub_add_cancel]
      have H := (sq_lt_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hminus.le)).mpr hminus
      rw [sq_abs] at H
      nlinarith only [H]
    exact ((diamond.rest_stable_normal_numerator_contDiffAt ε₁ ε₂ m a b (N p) h₁ h₂).of_le
      (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp p hN.contDiffAt
  have hMean : ContDiff ℝ 1 (coneSpatialMean f) := (cone_spatial_mean_contDiff hf).of_le (by norm_num)
  have hF := diamond.rest_threshold_test_amplitude_contDiff ε₁ ε₂ hm hMean hU
    (by linarith : m / 8 < m / 4) hfStrip hfRadius
  refine diamond.rest_threshold_scalar_pairing_tendsto_of_numerator ε₁ ε₂ φ φ a b hm
    hf.continuous hs hF ?_ ?_
  · intro h
    exact (diamond.rest_stable_normal_numerator_continuous ε₁ ε₂ m a b h).comp
      (by unfold restAxialRadialNormals; fun_prop)
  · intro h q hq
    rw [show U ((h : ℝ), (q.1, ‖q.2‖)) =
        diamond.restThresholdKernelProduct ε₁ ε₂ h φ φ a b m (q.1, ‖q.2‖) from
      diamond.rest_threshold_stable_readout ε₁ ε₂ h m ha hb _]
    exact diamond.rest_threshold_kernel_product_eq ε₁ ε₂ h φ φ a b hm q (hfStrip q hq)

end UV.SectorPlane
