import UV.SectorPlaneResolventProduct

/-! Two literal scalar lines evaluated at the same routed four-momentum.
The numerator carries two normalized running units before coefficient
extraction; the two vectorial denominators use the same positive height. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology UV.SectorPlane

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

variable {E : Type*} [NormedAddCommGroup E]

def Plane.twoLinePairing (diamond : Plane E) (ε₁ ε₂ : Evolution) (h : Height)
    (φ₁ φ₂ : ℂ → ℂ) (a₁ a₂ m₁ m₂ : ℝ) (f : MassiveMomentum → ℂ) : QuotientCarrier :=
  ∫ q : MassiveMomentum, directed (f q) * (if hq : q.1 ≠ 0 then
    diamond.scalarLine ε₁ h φ₁ a₁ m₁ q.1 q.2 hq *
    diamond.scalarLine ε₂ h φ₂ a₂ m₂ q.1 q.2 hq else 0)

def Plane.twoLineNumerator (diamond : Plane E) (ε₁ ε₂ : Evolution) (φ₁ φ₂ : ℂ → ℂ)
    (a₁ a₂ t : ℝ) (q : MassiveMomentum) : ℂ :=
  let z (ε : Evolution) := (shellSquare q.1 q.2 : ℂ) + Complex.I * ((diamond.eta ε * t : ℝ) : ℂ)
  show ℂ from -(diamond.eta ε₁ : ℂ) * (diamond.eta ε₂ : ℂ) *
    (φ₁ (-(a₁:ℂ)^2 * z ε₁) * φ₂ (-(a₂:ℂ)^2 * z ε₂))

theorem Plane.two_scalar_lines_readout (diamond : Plane E) (ε₁ ε₂ : Evolution) (h : Height)
    (φ₁ φ₂ : ℂ → ℂ) (a₁ a₂ m₁ m₂ : ℝ) (q : MassiveMomentum) (hq : q.1 ≠ 0) :
    diamond.scalarLine ε₁ h φ₁ a₁ m₁ q.1 q.2 hq * diamond.scalarLine ε₂ h φ₂ a₂ m₂ q.1 q.2 hq =
    directed (diamond.twoLineNumerator ε₁ ε₂ φ₁ φ₂ a₁ a₂ h q *
      (diamond.poleCoefficient ε₁ h (massiveD m₁ q) * diamond.poleCoefficient ε₂ h (massiveD m₂ q))) := by
  have hs : (axialSign q.1 : ℂ)^2 = 1 := by
    exact_mod_cast (show (axialSign q.1)^2 = 1 by rw [← sq_abs, axialSign_abs hq, one_pow])
  simp only [Plane.scalarLine, Plane.twoLineNumerator, diamond.pole_coefficient_eq_inv,
    Plane.shiftedShellCoefficient, massiveD, diamond.pole_inverse_complex, ← directed_mul, Complex.ofReal_mul]
  congr 1
  ring_nf
  rw [hs, Complex.I_sq]
  ring

theorem Plane.two_line_pairing_readout (diamond : Plane E) (ε₁ ε₂ : Evolution) (h : Height)
    (φ₁ φ₂ : ℂ → ℂ) (a₁ a₂ m₁ m₂ : ℝ) {f : MassiveMomentum → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f)
    (hU : Continuous (diamond.twoLineNumerator ε₁ ε₂ φ₁ φ₂ a₁ a₂ h)) :
    diamond.twoLinePairing ε₁ ε₂ h φ₁ φ₂ a₁ a₂ m₁ m₂ f =
      directed (∫ q, f q * (diamond.twoLineNumerator ε₁ ε₂ φ₁ φ₂ a₁ a₂ h q *
        (diamond.poleCoefficient ε₁ h (massiveD m₁ q) * diamond.poleCoefficient ε₂ h (massiveD m₂ q)))) := by
  let P (ε : Evolution) (m : ℝ) (q : MassiveMomentum) := diamond.poleCoefficient ε h (massiveD m q)
  have hp (ε : Evolution) (m : ℝ) : Continuous (P ε m) :=
    (diamond.pole_coefficient_continuous ε h).comp (massiveD_continuous m)
  rw [← directed_integral ((hf.mul (hU.mul ((hp ε₁ m₁).mul (hp ε₂ m₂)))).integrable_of_hasCompactSupport
    (μ := volume) hs.mul_right)]
  apply integral_congr_ae
  filter_upwards [real_axial_nonzero_ae] with q hq
  simp only [dif_pos hq, diamond.two_scalar_lines_readout, directed_mul, P]

theorem Plane.two_line_numerator_contDiff (diamond : Plane E) (ε₁ ε₂ : Evolution) (a₁ a₂ : ℝ)
    {φ₁ φ₂ : ℂ → ℂ} (hφ₁ : ContDiff ℝ 2 φ₁) (hφ₂ : ContDiff ℝ 2 φ₂) :
    ContDiff ℝ 2 (Function.uncurry (diamond.twoLineNumerator ε₁ ε₂ φ₁ φ₂ a₁ a₂)) := by
  have hw : ContDiff ℝ 2 (fun q : MassiveMomentum => shellSquare q.1 q.2) :=
    (contDiff_fst.pow 2).sub (contDiff_snd.norm_sq ℝ)
  have hz (ε : Evolution) (a : ℝ) : ContDiff ℝ 2 (fun y : ℝ × MassiveMomentum =>
    -(a:ℂ)^2 * ((shellSquare y.2.1 y.2.2 : ℂ) + Complex.I * ((diamond.eta ε*y.1 : ℝ) : ℂ))) :=
    contDiff_const.mul ((Complex.ofRealCLM.contDiff.comp (hw.comp contDiff_snd)).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst))))
  exact contDiff_const.mul ((hφ₁.comp (hz ε₁ a₁)).mul (hφ₂.comp (hz ε₂ a₂)))

private theorem continuous_height_slice {U : ℝ → MassiveMomentum → ℂ}
    (hu : Continuous (Function.uncurry U)) (t : ℝ) : Continuous (U t) :=
  hu.comp ((continuous_const (y := t)).prodMk continuous_id)

/-- Transfer a common-height bare product boundary through a jointly C²
numerator of the two directed lines on a fixed compact test space. -/
theorem Plane.smooth_two_line_distribution_of_bare (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (K : TopologicalSpace.Compacts MassiveMomentum) (m₁ m₂ a₁ a₂ : ℝ)
    {φ₁ φ₂ : ℂ → ℂ} (hφ₁ : ContDiff ℝ 2 φ₁) (hφ₂ : ContDiff ℝ 2 φ₂)
    (hlim : ∀ f : CompactMomentumTest K, ∃ z, Tendsto (fun h : Height => ∫ q, f.value q *
      (diamond.poleCoefficient ε₁ h (massiveD m₁ q) * diamond.poleCoefficient ε₂ h (massiveD m₂ q)))
      poleBoundaryHeights (𝓝 z)) :
    ∃ T : CompactMomentumTest K →L[ℂ] ℂ, ∀ f : CompactMomentumTest K,
      Tendsto (fun h => diamond.twoLinePairing ε₁ ε₂ h φ₁ φ₂ a₁ a₂ m₁ m₂ f.value)
        poleBoundaryHeights (𝓝 (directed (T f))) := by
  let W (h : Height) (q : MassiveMomentum) :=
    diamond.poleCoefficient ε₁ h (massiveD m₁ q) * diamond.poleCoefficient ε₂ h (massiveD m₂ q)
  have hw (h : Height) : Continuous (W h) :=
    ((diamond.pole_coefficient_continuous ε₁ h).comp (massiveD_continuous m₁)).mul
      ((diamond.pole_coefficient_continuous ε₂ h).comp (massiveD_continuous m₂))
  let U := diamond.twoLineNumerator ε₁ ε₂ φ₁ φ₂ a₁ a₂
  have hu : ContDiff ℝ 2 (Function.uncurry U) := diamond.two_line_numerator_contDiff ε₁ ε₂ a₁ a₂ hφ₁ hφ₂
  obtain ⟨T,hT⟩ := compact_momentum_multiplier_distribution K W
    (fun h => (hw h).continuousOn.integrableOn_compact K.isCompact) hlim U hu
  refine ⟨T, fun f => ?_⟩
  have H : Tendsto (fun h : Height => directed (∫ q, f.value q * (U h q * W h q)))
      poleBoundaryHeights (𝓝 (directed (T f))) :=
    directed_shell_readout_continuous.continuousAt.tendsto.comp (hT f)
  apply H.congr
  intro h
  have hU := continuous_height_slice (U := U) hu.continuous (h:ℝ)
  exact (diamond.two_line_pairing_readout ε₁ ε₂ h φ₁ φ₂ a₁ a₂ m₁ m₂ f.contDiff.continuous f.compact_support hU).symm

/-- A continuous functional on each compact C² test space, for the actual
product with two distinct shells. Both orientations and the zero-mass
endpoint are permitted. No separate product of limiting distributions enters. -/
theorem Plane.distinct_scalar_product_distribution (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (K : TopologicalSpace.Compacts MassiveMomentum) {m₁ m₂ : ℝ} (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂)
    (hne : m₁^2 ≠ m₂^2) (a₁ a₂ : ℝ) {φ₁ φ₂ : ℂ → ℂ} (hφ₁ : ContDiff ℝ 2 φ₁) (hφ₂ : ContDiff ℝ 2 φ₂) :
    ∃ T : CompactMomentumTest K →L[ℂ] ℂ, ∀ f : CompactMomentumTest K,
      Tendsto (fun h => diamond.twoLinePairing ε₁ ε₂ h φ₁ φ₂ a₁ a₂ m₁ m₂ f.value)
        poleBoundaryHeights (𝓝 (directed (T f))) := by
  exact diamond.smooth_two_line_distribution_of_bare ε₁ ε₂ K m₁ m₂ a₁ a₂ hφ₁ hφ₂
    (fun f => ⟨_, diamond.distinct_shell_product_limit ε₁ ε₂ hm₁ hm₂ hne f.contDiff f.compact_support⟩)

end UV.SectorPlane
