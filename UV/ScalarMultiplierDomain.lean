import UV.SectorPlaneLineDistributions

/-! A concrete common test domain on which multiplication by the normalized
running axial sign can be performed before or after the boundary limit. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology

theorem running_test_contDiff_away_from_axis {f : MassiveMomentum → ℂ} (hf : ContDiff ℝ 2 f)
    {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ q : MassiveMomentum, |q.1| < δ → f q = 0) :
    ContDiff ℝ 2 (runningAxialTest f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  rcases lt_trichotomy q.1 0 with hn | hz | hp
  · apply hf.neg.contDiffAt.congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt (Iio_mem_nhds hn)] with p hp
    change p.1 < 0 at hp
    simp [runningAxialTest, axialSign, hp.not_gt, hp]
  · apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    have hn : |q.1| < δ := by simpa [hz] using hδ
    filter_upwards [(continuous_abs.comp continuous_fst).continuousAt (Iio_mem_nhds hn)] with p hp
    simp [runningAxialTest, hgap p hp]
  · apply hf.contDiffAt.congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt (Ioi_mem_nhds hp)] with p hp
    simp [runningAxialTest, axialSign, (show 0 < p.1 from hp)]

theorem running_test_compact {f : MassiveMomentum → ℂ} (hs : HasCompactSupport f) :
    HasCompactSupport (runningAxialTest f) := hs.mul_left

variable {E : Type*} [NormedAddCommGroup E]

/-- The extracted resolvent has the kernel at the same displaced invariant as
the original carrier line. The test does not contain a running sign by definition. -/
def Plane.extractedResolventPair (diamond : Plane E) (ε : Evolution) (h : Height)
    (φ : ℂ → ℂ) (a m : ℝ) (f : MassiveMomentum → ℂ) : ℂ :=
  ∫ q, f q * (diamond.scalarKernelReadout ε a φ h (shellSquare q.1 q.2) * diamond.poleCoefficient ε h (massiveD m q))

/-- On a domain admitting sign multiplication, the two descriptions of the
line agree on the tested boundary. The equivalence retains the direction η. -/
theorem Plane.scalar_line_on_multiplier_domain (diamond : Plane E) (ε : Evolution)
    (φ : ℂ → ℂ) (a m : ℝ) (hK : ∀ h, Continuous (diamond.scalarKernelReadout ε a φ h))
    {f : MassiveMomentum → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) {z : ℂ} :
    Tendsto (fun h => diamond.extractedResolventPair ε h φ a m (runningAxialTest f)) poleBoundaryHeights (𝓝 z) ↔
      Tendsto (fun h => diamond.scalarLinePairing ε h φ a m f) poleBoundaryHeights
        (𝓝 (directed ((Complex.I * (diamond.eta ε : ℂ)) * z))) := by
  let c := Complex.I * (diamond.eta ε : ℂ)
  have hc : c ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (fun hz => by
    have := diamond.eta_sq ε; rw [hz] at this; norm_num at this))
  have he (h : Height) : diamond.scalarLinePairing ε h φ a m f =
      directed (c * diamond.extractedResolventPair ε h φ a m (runningAxialTest f)) :=
    diamond.scalar_line_pairing_eq ε h φ a m (hK h) hf hs
  constructor
  · intro H
    exact (directed_shell_readout_continuous.continuousAt.tendsto.comp (H.const_mul c)).congr fun h => (he h).symm
  · intro H
    have hread : Continuous (fun x : QuotientCarrier => (quotientCharacterEquiv x).1) :=
      continuous_fst.comp quotientCharacterIsometry.continuous
    have H' := (hread.continuousAt.tendsto.comp H).const_mul c⁻¹
    simp only [Function.comp_apply, he, directed, AlgEquiv.apply_symm_apply, ← mul_assoc, c,
      inv_mul_cancel₀ hc, one_mul] at H'
    exact H'

/-- On a test separated from the axial hyperplane, the extracted coefficient
itself has a boundary for the smooth kernels. Zero extension preserves C². -/
theorem Plane.smooth_extracted_limit_away_from_axis (diamond : Plane E) (ε : Evolution)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) (a : ℝ) {m : ℝ} (hm : 0 ≤ m)
    {f : MassiveMomentum → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)
    {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ q : MassiveMomentum, |q.1| < δ → f q = 0) :
    ∃ z : ℂ, Tendsto (fun h => diamond.extractedResolventPair ε h φ a m f) poleBoundaryHeights (𝓝 z) := by
  let g := runningAxialTest f
  have hg := running_test_contDiff_away_from_axis hf hδ hgap
  have hgs := running_test_compact hs
  have H := diamond.scalar_kernel_bounds_of_contDiff ε a (m^2) hφ
  have hP : ∃ z : ℂ, Tendsto (fun h => diamond.runningKernelPair ε h m (diamond.scalarKernelReadout ε a φ) g) poleBoundaryHeights (𝓝 z) := by
    rcases hm.eq_or_lt with he | hm
    · subst m
      simp only [zero_pow (by decide : (2:ℕ) ≠ 0)] at H
      obtain ⟨_, _, hz⟩ := diamond.massless_running_kernel_limit ε H hg hgs
      exact ⟨_, hz⟩
    · obtain ⟨_, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgs hg (by norm_num)
      exact ⟨_, diamond.massive_running_kernel_limit ε hm H hL hgs⟩
  obtain ⟨z, hz⟩ := hP
  refine ⟨z, hz.congr fun h => ?_⟩
  apply integral_congr_ae
  filter_upwards [real_axial_nonzero_ae] with q hq
  rcases lt_or_gt_of_ne hq with hn | hp
  · simp [g, runningAxialTest, axialSign, hn.not_gt, hn]
  · simp [g, runningAxialTest, axialSign, hp]

end UV.SectorPlane
