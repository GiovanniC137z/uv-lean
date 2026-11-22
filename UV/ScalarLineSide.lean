import UV.ScalarProfileBounds

/-! Boundary of the literal oriented scalar line in its sector-plane
quotient, including the stable-half residue with its full phase. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology NNReal

theorem directed_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g : X → ℂ} (hg : Integrable g μ) :
    (∫ x, directed (g x) ∂μ) = directed (∫ x, g x ∂μ) := by
  have hi : Integrable (fun x => directed (g x)) μ := by
    apply hg.norm.mono' (directed_shell_readout_continuous.comp_aestronglyMeasurable hg.aestronglyMeasurable)
    exact Eventually.of_forall fun x => by simp [quotient_character_norm, directed]
  apply quotientCharacterEquiv.injective
  rw [quotient_character_integral_reconstruction hi]
  simp only [directed, AlgEquiv.apply_symm_apply]
  exact congrArg (fun z : ℂ => (∫ x, g x ∂μ, z)) (integral_conj (f := g))

variable {E : Type*} [NormedAddCommGroup E]

/-- A complex test is itself embedded in the directed real algebra.
The value chosen on the null axial hyperplane is a scalar totalization. -/
def Plane.scalarLinePairing (diamond : Plane E) (ε : Evolution) (h : Height)
    (φ : ℂ → ℂ) (a m : ℝ) (f : MassiveMomentum → ℂ) : QuotientCarrier :=
  ∫ q : MassiveMomentum, directed (f q) *
    (if hq : q.1 ≠ 0 then diamond.scalarLine ε h φ a m q.1 q.2 hq else 0)

theorem Plane.scalar_line_pairing_eq (diamond : Plane E) (ε : Evolution) (h : Height)
    (φ : ℂ → ℂ) (a m : ℝ) (hK : Continuous (diamond.scalarKernelReadout ε a φ h))
    {f : MassiveMomentum → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) :
    diamond.scalarLinePairing ε h φ a m f = directed ((Complex.I * (diamond.eta ε : ℂ)) *
      diamond.runningKernelPair ε h m (diamond.scalarKernelReadout ε a φ) f) := by
  unfold Plane.scalarLinePairing Plane.runningKernelPair
  rw [← integral_const_mul, ← directed_integral ((diamond.running_kernel_pair_integrable ε h m hK hf hs).const_mul _)]
  apply integral_congr_ae
  filter_upwards [real_axial_nonzero_ae] with q hq
  rw [dif_pos hq, Plane.scalarLine, diamond.pole_inverse_complex]
  simp only [← directed_mul, diamond.pole_coefficient_eq_inv, Plane.scalarKernelReadout,
    Plane.shiftedShellCoefficient, massiveD, runningAxialTest, Complex.ofReal_mul]
  congr 1
  ring

/-- On the proved test domain this is an integral of the original
carrier-valued numerator and vectorial pole on one prescribed side. -/
theorem Plane.massive_scalar_line_pairing_limit (diamond : Plane E) (ε : Evolution)
    (φ : ℂ → ℂ) (a : ℝ) {m : ℝ} (hm : 0 < m) {F : ℝ → ℂ}
    (H : diamond.ShellKernelBounds ε (m ^ 2) (diamond.scalarKernelReadout ε a φ) F)
    {f : MassiveMomentum → ℂ} {L : ℝ≥0} (hf : LipschitzWith L f) (hs : HasCompactSupport f) :
    Tendsto (fun h => diamond.scalarLinePairing ε h φ a m f) poleBoundaryHeights
      (𝓝 (directed ((Complex.I * (diamond.eta ε : ℂ)) *
        (F (m ^ 2) * massiveComplexSignedPoleBoundary (diamond.eta ε) m f +
          ∫ q, runningKernelRemainder m F f q)))) := by
  have h := (diamond.massive_running_kernel_limit ε hm H hf hs).const_mul (Complex.I * (diamond.eta ε : ℂ))
  exact (directed_shell_readout_continuous.continuousAt.tendsto.comp h).congr fun h =>
    (diamond.scalar_line_pairing_eq ε h φ a m (H.continuous_heights h) hf.continuous hs).symm

theorem Plane.massless_scalar_line_pairing_limit (diamond : Plane E) (ε : Evolution)
    (φ : ℂ → ℂ) (a : ℝ) {F : ℝ → ℂ} (H : diamond.ShellKernelBounds ε 0 (diamond.scalarKernelReadout ε a φ) F)
    {f : MassiveMomentum → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    ∃ Z : ℂ, Tendsto (fun h => diamond.scalarLinePairing ε h φ a 0 f)
      poleBoundaryHeights (𝓝 (directed Z)) := by
  obtain ⟨_, _, h⟩ := diamond.massless_running_kernel_limit ε H hf hs
  have h := h.const_mul (Complex.I * (diamond.eta ε : ℂ))
  exact ⟨_, (directed_shell_readout_continuous.continuousAt.tendsto.comp h).congr fun h =>
    (diamond.scalar_line_pairing_eq ε h φ a 0 (H.continuous_heights h) hf.continuous hs).symm⟩

theorem Plane.smooth_scalar_line_pairing_limit (diamond : Plane E) (ε : Evolution)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) (a : ℝ) {m : ℝ} (hm : 0 ≤ m)
    {f : MassiveMomentum → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    ∃ Z : ℂ, Tendsto (fun h => diamond.scalarLinePairing ε h φ a m f)
      poleBoundaryHeights (𝓝 (directed Z)) := by
  rcases hm.eq_or_lt with he | hm
  · subst m
    exact diamond.massless_scalar_line_pairing_limit ε φ a (diamond.scalar_kernel_bounds_of_contDiff ε a 0 hφ) hf hs
  · obtain ⟨_, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hf (by norm_num)
    exact ⟨_, diamond.massive_scalar_line_pairing_limit ε φ a hm
      (diamond.scalar_kernel_bounds_of_contDiff ε a (m ^ 2) hφ) hL hs⟩

theorem Plane.stable_scalar_kernel_readout (diamond : Plane E) (ε : Evolution)
    {a : ℝ} (ha : 0 ≤ a) (h : Height) (w : ℝ) :
    diamond.scalarKernelReadout ε a (fun z => Complex.exp (-principalSqrt z)) h w =
      diamond.stableHalfCoefficient ε a w h := by
  rw [Plane.stableHalfCoefficient, dif_pos h.property,
    diamond.stable_half_numerator_scalar_argument ε h ha w]
  simp [Plane.scalarKernelReadout, directed]

theorem Plane.massive_stable_scalar_line_side (diamond : Plane E) (ε : Evolution)
    {a m : ℝ} (ha : 0 ≤ a) (hm : 0 < m)
    {f : MassiveMomentum → ℂ} {L : ℝ≥0} (hf : LipschitzWith L f) (hs : HasCompactSupport f) :
    let η := diamond.eta ε
    Tendsto (fun h => diamond.scalarLinePairing ε h (fun z => Complex.exp (-principalSqrt z)) a m f)
      poleBoundaryHeights (𝓝 (directed ((Complex.I * (η : ℂ)) *
        (Complex.exp (Complex.I * (η : ℂ) * (a : ℂ) * (m : ℂ)) *
          massiveComplexSignedPoleBoundary η m f +
          ∫ q, runningKernelRemainder m (stableSideValue η a) f q)))) := by
  dsimp only
  have hK : diamond.scalarKernelReadout ε a (fun z => Complex.exp (-principalSqrt z)) =
      fun (h : Height) w => diamond.stableHalfCoefficient ε a w h := by
    funext h w
    exact diamond.stable_scalar_kernel_readout ε ha h w
  have H := diamond.stable_half_positive_mass_kernel_bounds ε ha hm
  rw [← hK] at H
  simpa only [stable_side_value_at_mass _ _ hm.le] using
    diamond.massive_scalar_line_pairing_limit ε _ a hm H hf hs

/-- Explicit side for the running real test of the manuscript's massive
jump. The oriented numerator gives the full complex shell phase. -/
theorem Plane.massive_stable_running_side (diamond : Plane E) (ε : Evolution)
    {a m : ℝ} (ha : 0 ≤ a) (hm : 0 < m)
    {f : MassiveMomentum → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hs : HasCompactSupport f) :
    let η := diamond.eta ε
    let phase := Complex.exp (Complex.I * (η : ℂ) * (a : ℂ) * (m : ℂ))
    Tendsto (diamond.massiveStableRunningPairing ε a m f) (𝓝[>] (0 : ℝ))
      (𝓝 ((Complex.I * (η : ℂ)) * (phase * (massiveSignedPV m f : ℂ) +
        ∫ q, runningKernelRemainder m (stableSideValue η a) (fun q => (f q : ℂ)) q) +
        (Real.pi : ℂ) * phase * (massiveSignedShellTest m f : ℂ))) := by
  dsimp only
  have H := diamond.stable_half_positive_mass_kernel_bounds ε ha hm
  have hfc : Continuous (fun q => (f q : ℂ)) := Complex.continuous_ofReal.comp hf.continuous
  have hfs : HasCompactSupport (fun q => (f q : ℂ)) := hs.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have h := (diamond.running_kernel_limit ε m H hfc hfs (diamond.massive_signed_pole_limit ε hm hf hs)).const_mul
    (Complex.I * (diamond.eta ε : ℂ))
  rw [stable_side_value_at_mass _ _ hm.le] at h
  have he : (diamond.eta ε : ℂ) ^ 2 = 1 := by exact_mod_cast diamond.eta_sq ε
  have hside := h.congr (f₂ := fun h : Height => diamond.massiveStableRunningPairing ε a m f h) (fun h => by
    dsimp only
    rw [Plane.runningKernelPair, ← integral_const_mul]
    apply integral_congr_ae
    refine Eventually.of_forall fun q => ?_
    simp only [Plane.massiveStableRunningIntegrand, Plane.massiveStableFactor, dif_pos h.property,
      runningAxialTest, massiveD, Complex.ofReal_mul]
    ring)
  have hrange : range (fun h : Height => (h : ℝ)) ∈ 𝓝[>] (0 : ℝ) := by
    simpa [Subtype.range_coe] using (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))
  change map (diamond.massiveStableRunningPairing ε a m f ∘ (fun h : Height => (h : ℝ))) poleBoundaryHeights ≤ _ at hside
  rw [← map_map, poleBoundaryHeights, map_comap_of_mem hrange] at hside
  convert hside using 2
  unfold massiveSignedPoleBoundary
  push_cast
  ring_nf
  simp [he, Complex.I_sq, add_assoc]

end UV.SectorPlane
