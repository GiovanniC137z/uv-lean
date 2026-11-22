import UV.SectorPlaneMovingTests
import UV.SectorPlaneLineDistributions

/-! Regular common-height multipliers for the resolved Maxwell and ghost
lines on the fixed plane. No multiplication of two singular boundary values. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped UV.SectorPlane Topology

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-- The boundary is obtained by applying the bare functional to the test
multiplied by the zero-height profile. Both multiplications are performed
on the same compact C² test space. -/
theorem compact_momentum_multiplier_limit (K : TopologicalSpace.Compacts MassiveMomentum)
    (W : Height → MassiveMomentum → ℂ) (hi : ∀ h, IntegrableOn (W h) (K : Set MassiveMomentum))
    (T : CompactMomentumTest K →L[ℂ] ℂ) (hT : ∀ f : CompactMomentumTest K,
      Tendsto (fun h => ∫ q, f.value q * W h q) poleBoundaryHeights (𝓝 (T f)))
    (U : ℝ → MassiveMomentum → ℂ) (hU : ContDiff ℝ 2 (Function.uncurry U)) (f : CompactMomentumTest K) :
    let g (t : ℝ) := CompactMomentumTest.ofFunction K (fun q => f.value q * U t q)
      (f.contDiff.mul (hU.comp (contDiff_const.prodMk contDiff_id))) (fun q hq => by
        change f.val.1 q * U t q = 0; rw [f.property.1 q hq, zero_mul])
    Tendsto (fun h : Height => ∫ q, f.value q * (U (h : ℝ) q * W h q)) poleBoundaryHeights (𝓝 (T (g 0))) := by
  intro g
  let F (t : ℝ) (q : MassiveMomentum) := f.value q * U t q
  have hc : ContDiff ℝ 2 (Function.uncurry F) := (f.contDiff.comp contDiff_snd).mul hU
  have hs t q (hq : q ∉ K) : F t q = 0 := by
    change f.val.1 q * U t q = 0
    rw [f.property.1 q hq, zero_mul]
  have hg : Tendsto g (𝓝 0) (𝓝 (g 0)) := compact_momentum_slices_tendsto K F hc hs 0
  choose L hL using fun h => compact_momentum_integral_exists K (W h) (hi h)
  have hv := compact_momentum_moving_test_limit K L T (fun x => (hT x).congr fun h => (hL h x).symm)
    (hg.comp pole_height_tendsto_zero)
  refine hv.congr fun h => ?_
  dsimp only [Function.comp_apply]
  rw [hL]
  simp only [g, CompactMomentumTest.ofFunction_value, mul_assoc]

/-- Regularizing a compact test with the actual shifted scalar profile preserves
continuity of the resulting boundary functional on every compact set. -/
theorem compact_momentum_multiplier_distribution (K : TopologicalSpace.Compacts MassiveMomentum)
    (W : Height → MassiveMomentum → ℂ) (hi : ∀ h, IntegrableOn (W h) (K : Set MassiveMomentum))
    (hlim : ∀ f : CompactMomentumTest K, ∃ z, Tendsto (fun h => ∫ q, f.value q * W h q) poleBoundaryHeights (𝓝 z))
    (U : ℝ → MassiveMomentum → ℂ) (hU : ContDiff ℝ 2 (Function.uncurry U)) :
    ∃ T : CompactMomentumTest K →L[ℂ] ℂ, ∀ f : CompactMomentumTest K,
      Tendsto (fun h : Height => ∫ q, f.value q * (U (h : ℝ) q * W h q)) poleBoundaryHeights (𝓝 (T f)) := by
  obtain ⟨T, hT⟩ := compact_momentum_boundary_functional K W hi hlim
  apply compact_momentum_boundary_functional
  · intro h
    have hc : Continuous (U (h : ℝ)) := hU.continuous.comp (continuous_const.prodMk continuous_id)
    obtain ⟨B, hB⟩ := K.isCompact.exists_bound_of_continuousOn hc.continuousOn
    exact (hi h).bdd_mul' hc.aestronglyMeasurable ((ae_restrict_mem K.isCompact.measurableSet).mono hB)
  · exact fun f => ⟨_, compact_momentum_multiplier_limit K W hi T hT U hU f⟩

variable {E : Type*} [NormedAddCommGroup E]

/-- The undamped gauge coefficient before the real axial sign is restored. -/
def Plane.maxwellCoefficient (diamond : Plane E) (ε : Evolution) (h : Height)
    (ζ : ℝ) (u v : ConeUnitDirection) (q : MassiveMomentum) : ℂ :=
  let P := diamond.poleCoefficient ε h (shellSquare q.1 q.2)
  let G := (coneCovector (WithLp.ofLp u.val) (WithLp.ofLp v.val) : ℂ)
  let B := (1 - (ζ : ℂ)) * (coneCovector (WithLp.ofLp u.val) q : ℂ) * (coneCovector (WithLp.ofLp v.val) q : ℂ)
  show ℂ from -(Complex.I * (diamond.eta ε : ℂ)) * (G * P - B * P ^ 2)

private theorem Plane.maxwell_coefficient_continuous (diamond : Plane E) (ε : Evolution) (h : Height)
    (ζ : ℝ) (u v : ConeUnitDirection) : Continuous (diamond.maxwellCoefficient ε h ζ u v) := by
  have hP := (diamond.pole_coefficient_continuous ε h).comp shellSquare_continuous
  have hB := (continuous_const (y := 1 - (ζ : ℂ))).mul
    (Complex.continuous_ofReal.comp (coneCovector (WithLp.ofLp u.val)).continuous)
  exact continuous_const.mul ((continuous_const.mul hP).sub ((hB.mul
    (Complex.continuous_ofReal.comp (coneCovector (WithLp.ofLp v.val)).continuous)).mul (hP.pow 2)))

/-- The positive-height line has the original two covariant slots, fixed pole
unit and normalized running sign. Its value on the axial hyperplane is a totalization. -/
def Plane.maxwellLinePairing (diamond : Plane E) (ε : Evolution) (h : Height) (φ : ℂ → ℂ)
    (a ζ : ℝ) (u v : ConeUnitDirection) (f : MassiveMomentum → ℂ) : QuotientCarrier :=
  ∫ q, directed (f q) * directed (diamond.scalarKernelReadout ε a φ h (shellSquare q.1 q.2)) *
    directed ((axialSign q.1 : ℂ) * diamond.maxwellCoefficient ε h ζ u v q)

theorem Plane.maxwell_kernel_vectorial (diamond : Plane E) (ε : Evolution) (h : Height) (φ : ℂ → ℂ)
    (a ζ : ℝ) (u v : ConeUnitDirection) (q : MassiveMomentum) :
    let w := shellSquare q.1 q.2
    let N := Complex.I * ((diamond.eta ε * axialSign q.1 : ℝ) : ℂ)
    let G := (coneCovector (WithLp.ofLp u.val) (WithLp.ofLp v.val) : ℂ)
    let B := (1 - (ζ : ℂ)) * (coneCovector (WithLp.ofLp u.val) q : ℂ) * (coneCovector (WithLp.ofLp v.val) q : ℂ)
    directed (diamond.scalarKernelReadout ε a φ h w) * directed ((axialSign q.1 : ℂ) * diamond.maxwellCoefficient ε h ζ u v q) =
      -directed N * directed (φ (-(a : ℂ) ^ 2 * diamond.shiftedShellCoefficient ε h w)) *
        (directed G * diamond.poleInverse ε h w - directed B * (diamond.poleInverse ε h w) ^ 2) := by
  dsimp only [Plane.maxwellCoefficient, Plane.scalarKernelReadout]
  have hp : directed (diamond.poleCoefficient ε h (shellSquare q.1 q.2)) = diamond.poleInverse ε h (shellSquare q.1 q.2) := by
    simp [diamond.pole_coefficient_eq_inv, diamond.pole_inverse_complex, Plane.shiftedShellCoefficient]
  rw [← hp]
  apply quotientCharacterEquiv.injective
  ext <;> simp [directed, Complex.ofReal_mul] <;> ring

theorem Plane.smooth_maxwell_distribution (diamond : Plane E) (ε : Evolution)
    (K : TopologicalSpace.Compacts MassiveMomentum) {φ : ℂ → ℂ} (hφ : ContDiff ℝ 2 φ)
    (a ζ : ℝ) (u v : ConeUnitDirection) : ∃ T : CompactMomentumTest K →L[ℂ] ℂ, ∀ f : CompactMomentumTest K,
    Tendsto (fun h => diamond.maxwellLinePairing ε h φ a ζ u v f.value) poleBoundaryHeights (𝓝 (directed (T f))) := by
  let W (h : Height) (q : MassiveMomentum) := (axialSign q.1 : ℂ) * diamond.maxwellCoefficient ε h ζ u v q
  have hi (h : Height) : IntegrableOn (W h) (K : Set MassiveMomentum) := integrable_runningAxialSign_mul measurable_fst
    ((diamond.maxwell_coefficient_continuous ε h ζ u v).continuousOn.integrableOn_compact K.isCompact)
  let U (t : ℝ) (q : MassiveMomentum) := φ (-(a : ℂ) ^ 2 * ((shellSquare q.1 q.2 : ℂ) + Complex.I * ((diamond.eta ε * t : ℝ) : ℂ)))
  have hw : ContDiff ℝ 2 (fun q : MassiveMomentum => shellSquare q.1 q.2) := (contDiff_fst.pow 2).sub (contDiff_snd.norm_sq ℝ)
  have hU : ContDiff ℝ 2 (Function.uncurry U) := hφ.comp (contDiff_const.mul
    ((Complex.ofRealCLM.contDiff.comp (hw.comp contDiff_snd)).add (contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst)))))
  have hlim (f : CompactMomentumTest K) : ∃ z, Tendsto (fun h => ∫ q, f.value q * W h q) poleBoundaryHeights (𝓝 z) := by
    obtain ⟨z, hz, _⟩ := diamond.massless_running_stable_gauge_limit ε (a := 0) le_rfl ζ u v f.contDiff f.compact_support
    refine ⟨z, hz.congr fun h => ?_⟩
    rw [diamond.massless_running_stable_gauge_pair_integral ε h 0 ζ u v f.contDiff.continuous f.compact_support]
    apply integral_congr_ae
    exact Eventually.of_forall fun q => by
      simp only [W, Plane.maxwellCoefficient, Plane.stableHalfCoefficient, dif_pos h.property,
        Plane.stableHalfNumerator, Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, directed,
        AlgEquiv.apply_symm_apply, one_mul, Complex.ofReal_mul]; ring
  obtain ⟨T, hT⟩ := compact_momentum_multiplier_distribution K W hi hlim U hU
  refine ⟨T, fun f => (directed_shell_readout_continuous.continuousAt.tendsto.comp (hT f)).congr fun h => ?_⟩
  have hc : Continuous (U (h : ℝ)) := hU.continuous.comp (continuous_const.prodMk continuous_id)
  have hi' := integrable_runningAxialSign_mul measurable_fst
    (((f.val.1.continuous.mul hc).mul (diamond.maxwell_coefficient_continuous ε h ζ u v)).integrable_of_hasCompactSupport
      (μ := volume) (f.compact_support.mul_right.mul_right))
  have hprod : Integrable (fun q => f.value q * (U (h : ℝ) q * W h q)) :=
    hi'.congr (Eventually.of_forall fun q => by dsimp only [W, CompactMomentumTest.value]; ring)
  dsimp only [Function.comp_apply]
  rw [← directed_integral hprod]
  apply integral_congr_ae
  exact Eventually.of_forall fun q => by
    simp only [← directed_mul]; congr 1; dsimp only [U, W, Plane.scalarKernelReadout, Plane.shiftedShellCoefficient]; ring

end UV.SectorPlane
