import UV.SectorPlaneBoundaryFunctional
import UV.ScalarLineSide
import UV.VerifyRunningLines

/-! Continuous boundary functionals for the actual single-line sector-plane
pairings. The height in the kernel and in each pole is the same. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped UV.SectorPlane Topology

private theorem running_pair_functional (K : TopologicalSpace.Compacts MassiveMomentum)
    (A : Height → MassiveMomentum → ℂ) (hA : ∀ h, Continuous (A h))
    (P : Height → (MassiveMomentum → ℂ) → ℂ)
    (hP : ∀ (h : Height) (f : CompactMomentumTest K), P h f.value =
      ∫ q, f.value q * ((axialSign q.1 : ℂ) * A h q))
    (hlim : ∀ f : CompactMomentumTest K, ∃ z, Tendsto (fun h => P h f.value) poleBoundaryHeights (𝓝 z)) :
    ∃ T : CompactMomentumTest K →L[ℂ] ℂ, ∀ f : CompactMomentumTest K,
      Tendsto (fun h => P h f.value) poleBoundaryHeights (𝓝 (T f)) := by
  have hi (h : Height) : IntegrableOn (fun q : MassiveMomentum => (axialSign q.1 : ℂ) * A h q)
      (K : Set MassiveMomentum) :=
    integrable_runningAxialSign_mul measurable_fst ((hA h).continuousOn.integrableOn_compact K.isCompact)
  obtain ⟨T, hT⟩ := compact_momentum_boundary_functional K _ hi (fun f => by
    obtain ⟨z, hz⟩ := hlim f
    exact ⟨z, hz.congr fun h => hP h f⟩)
  exact ⟨T, fun f => (hT f).congr fun h => (hP h f).symm⟩

variable {E : Type*} [NormedAddCommGroup E]

private theorem Plane.scalar_line_functional_of_limits (diamond : Plane E) (ε : Evolution)
    (K : TopologicalSpace.Compacts MassiveMomentum) (φ : ℂ → ℂ) (a m : ℝ)
    (hφ : ∀ h, Continuous (diamond.scalarKernelReadout ε a φ h))
    (hlim : ∀ f : CompactMomentumTest K, ∃ z, Tendsto (fun h =>
      diamond.runningKernelPair ε h m (diamond.scalarKernelReadout ε a φ) f.value) poleBoundaryHeights (𝓝 z)) :
    ∃ T : CompactMomentumTest K →L[ℂ] ℂ, ∀ f : CompactMomentumTest K,
      Tendsto (fun h => diamond.scalarLinePairing ε h φ a m f.value) poleBoundaryHeights (𝓝 (directed (T f))) := by
  let A (h : Height) (q : MassiveMomentum) := (Complex.I * (diamond.eta ε : ℂ)) *
    (diamond.scalarKernelReadout ε a φ h (shellSquare q.1 q.2) * diamond.poleCoefficient ε h (massiveD m q))
  have hc (h : Height) : Continuous (A h) := continuous_const.mul (((hφ h).comp shellSquare_continuous).mul
    ((diamond.pole_coefficient_continuous ε h).comp (massiveD_continuous m)))
  let P (h : Height) (g : MassiveMomentum → ℂ) := (Complex.I * (diamond.eta ε : ℂ)) *
    diamond.runningKernelPair ε h m (diamond.scalarKernelReadout ε a φ) g
  obtain ⟨T, hT⟩ := running_pair_functional K A hc P (fun h f => by
    unfold P Plane.runningKernelPair
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun q => by dsimp only [A, runningAxialTest]; ring) (fun f => by
      obtain ⟨z, hz⟩ := hlim f
      exact ⟨_, hz.const_mul _⟩)
  exact ⟨T, fun f => (directed_shell_readout_continuous.continuousAt.tendsto.comp (hT f)).congr fun h =>
    (diamond.scalar_line_pairing_eq ε h φ a m (hφ h) f.val.1.continuous f.compact_support).symm⟩

/-- A local coefficient estimate yields an order-at-most-two scalar boundary on every
compact test space, also when the support contains the massless cone tip. -/
theorem Plane.shell_bounded_scalar_distribution (diamond : Plane E) (ε : Evolution)
    (K : TopologicalSpace.Compacts MassiveMomentum) (φ : ℂ → ℂ) (a : ℝ) {m : ℝ} (hm : 0 ≤ m)
    {F : ℝ → ℂ} (H : diamond.ShellKernelBounds ε (m ^ 2) (diamond.scalarKernelReadout ε a φ) F) :
    ∃ T : CompactMomentumTest K →L[ℂ] ℂ, ∀ f : CompactMomentumTest K,
      Tendsto (fun h => diamond.scalarLinePairing ε h φ a m f.value) poleBoundaryHeights (𝓝 (directed (T f))) := by
  apply diamond.scalar_line_functional_of_limits ε K φ a m H.continuous_heights
  intro f
  rcases hm.eq_or_lt with he | hm
  · subst m
    have H₀ : diamond.ShellKernelBounds ε 0 (diamond.scalarKernelReadout ε a φ) F := by simpa using H
    obtain ⟨_, _, hz⟩ := diamond.massless_running_kernel_limit ε H₀ f.contDiff f.compact_support
    exact ⟨_, hz⟩
  · obtain ⟨_, hf⟩ := ContDiff.lipschitzWith_of_hasCompactSupport f.compact_support f.contDiff (by norm_num)
    exact ⟨_, diamond.massive_running_kernel_limit ε hm H hf f.compact_support⟩

theorem Plane.smooth_scalar_distribution (diamond : Plane E) (ε : Evolution)
    (K : TopologicalSpace.Compacts MassiveMomentum) {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) (a : ℝ) {m : ℝ}
    (hm : 0 ≤ m) : ∃ T : CompactMomentumTest K →L[ℂ] ℂ, ∀ f : CompactMomentumTest K,
      Tendsto (fun h => diamond.scalarLinePairing ε h φ a m f.value) poleBoundaryHeights (𝓝 (directed (T f))) :=
  diamond.shell_bounded_scalar_distribution ε K φ a hm (diamond.scalar_kernel_bounds_of_contDiff ε a _ hφ)

theorem Plane.stable_scalar_distribution (diamond : Plane E) (ε : Evolution)
    (K : TopologicalSpace.Compacts MassiveMomentum) {a m : ℝ} (ha : 0 ≤ a) (hm : 0 ≤ m) :
    ∃ T : CompactMomentumTest K →L[ℂ] ℂ, ∀ f : CompactMomentumTest K,
      Tendsto (fun h => diamond.scalarLinePairing ε h (fun z => Complex.exp (-principalSqrt z)) a m f.value)
        poleBoundaryHeights (𝓝 (directed (T f))) := by
  let φ := fun z => Complex.exp (-principalSqrt z)
  have heq : diamond.scalarKernelReadout ε a φ = fun (h : Height) w => diamond.stableHalfCoefficient ε a w h :=
    funext fun h => funext fun w => diamond.stable_scalar_kernel_readout ε ha h w
  rcases hm.eq_or_lt with h₀ | hm
  · subst m
    apply diamond.scalar_line_functional_of_limits ε K φ a 0 (fun h => by rw [heq]; exact diamond.stable_half_coefficient_continuous ε a h)
    intro f
    obtain ⟨_, _, hz⟩ := diamond.massless_running_stable_single_limit ε ha f.contDiff f.compact_support
    rw [heq]
    simpa only [Plane.runningKernelPair, Plane.masslessRunningStableSinglePair, massiveD,
      zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] using (show ∃ z, Tendsto (fun h =>
        diamond.masslessRunningStableSinglePair ε h a f.value) poleBoundaryHeights (𝓝 z) from ⟨_, hz⟩)
  · apply diamond.shell_bounded_scalar_distribution ε K φ a hm.le
    rw [heq]
    exact diamond.stable_half_positive_mass_kernel_bounds ε ha hm

/-- The massless ghost coefficient acts continuously on C² tests, including tests
which meet the vertex of the light cone. -/
theorem Plane.stable_ghost_distribution (diamond : Plane E) (ε : Evolution)
    (K : TopologicalSpace.Compacts MassiveMomentum) {a : ℝ} (ha : 0 ≤ a) :
    ∃ T : CompactMomentumTest K →L[ℂ] ℂ, ∀ f : CompactMomentumTest K,
      Tendsto (fun h => directed (diamond.runningStableGhostPair ε h a f.value)) poleBoundaryHeights (𝓝 (directed (T f))) := by
  let A (h : Height) (q : MassiveMomentum) := (Complex.I * (diamond.eta ε : ℂ)) *
    (diamond.stableHalfCoefficient ε a (shellSquare q.1 q.2) h * diamond.poleCoefficient ε h (shellSquare q.1 q.2))
  have hc (h : Height) : Continuous (A h) := continuous_const.mul
    (((diamond.stable_half_coefficient_continuous ε a h).comp shellSquare_continuous).mul
      ((diamond.pole_coefficient_continuous ε h).comp shellSquare_continuous))
  obtain ⟨T, hT⟩ := running_pair_functional K A hc (fun h => diamond.runningStableGhostPair ε h a) (fun h f => by
    dsimp only
    rw [diamond.massless_running_stable_ghost_pair_integral]
    apply integral_congr_ae
    exact Eventually.of_forall fun q => by dsimp only [A]; push_cast; ring) (fun f => by
      obtain ⟨z, hz, _⟩ := diamond.massless_running_stable_ghost_limit ε ha f.contDiff f.compact_support
      exact ⟨z, hz⟩)
  exact ⟨T, fun f => directed_shell_readout_continuous.continuousAt.tendsto.comp (hT f)⟩

/-- The resolved Maxwell expression acts continuously in the same test norm for every
real gauge parameter and every pair of the original intrinsic unit directions. -/
theorem Plane.stable_maxwell_distribution (diamond : Plane E) (ε : Evolution)
    (K : TopologicalSpace.Compacts MassiveMomentum) {a : ℝ} (ha : 0 ≤ a) (ζ : ℝ) (u v : ConeUnitDirection) :
    ∃ T : CompactMomentumTest K →L[ℂ] ℂ, ∀ f : CompactMomentumTest K,
      Tendsto (fun h => directed (diamond.runningStableGaugePair ε h a ζ u v f.value)) poleBoundaryHeights (𝓝 (directed (T f))) := by
  let G := (coneCovector (WithLp.ofLp u.val) (WithLp.ofLp v.val) : ℂ)
  let B (q : MassiveMomentum) := (1 - (ζ : ℂ)) * (coneCovector (WithLp.ofLp u.val) q : ℂ) *
    (coneCovector (WithLp.ofLp v.val) q : ℂ)
  let A (h : Height) (q : MassiveMomentum) :=
    let w := shellSquare q.1 q.2
    let F := diamond.stableHalfCoefficient ε a w h
    let P := diamond.poleCoefficient ε h w
    show ℂ from -(Complex.I * (diamond.eta ε : ℂ)) * (G * (F * P) - B q * (F * P ^ 2))
  have hB : Continuous B := (continuous_const.mul
    (Complex.continuous_ofReal.comp (coneCovector (WithLp.ofLp u.val)).continuous)).mul
    (Complex.continuous_ofReal.comp (coneCovector (WithLp.ofLp v.val)).continuous)
  have hc (h : Height) : Continuous (A h) := by
    have hF := (diamond.stable_half_coefficient_continuous ε a h).comp shellSquare_continuous
    have hP := (diamond.pole_coefficient_continuous ε h).comp shellSquare_continuous
    exact continuous_const.mul ((continuous_const.mul (hF.mul hP)).sub (hB.mul (hF.mul (hP.pow 2))))
  obtain ⟨T, hT⟩ := running_pair_functional K A hc (fun h => diamond.runningStableGaugePair ε h a ζ u v) (fun h f => by
    dsimp only
    rw [diamond.massless_running_stable_gauge_pair_integral ε h a ζ u v (g := f.value) f.contDiff.continuous f.compact_support]
    apply integral_congr_ae
    exact Eventually.of_forall fun q => by dsimp only [A, B, G]; push_cast; ring) (fun f => by
      obtain ⟨z, hz, _⟩ := diamond.massless_running_stable_gauge_limit ε ha ζ u v f.contDiff f.compact_support
      exact ⟨z, hz⟩)
  exact ⟨T, fun f => directed_shell_readout_continuous.continuousAt.tendsto.comp (hT f)⟩

end UV.SectorPlane
