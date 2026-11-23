import UV.SectorPlaneStableProductBounds

/-! For stable-half lines with distinct masses the two simple-pole boundary
values exist even at the massless end of the branch cut. Both numerators
are evaluated at the same positive height as the two vectorial poles. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory UV.Carrier
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

def Plane.stablePairWeight (diamond : Plane E) (ε₁ ε₂ : Evolution) (a b : ℝ) (h : Height) (w : ℝ) : ℂ :=
  diamond.stableHalfCoefficient ε₁ a w h * diamond.stableHalfCoefficient ε₂ b w h

def stablePairSide (η₁ η₂ a b w : ℝ) : ℂ :=
  stableSideValue η₁ a w * stableSideValue η₂ b w

theorem Plane.stable_pair_weight_continuous (diamond : Plane E) (ε₁ ε₂ : Evolution) (a b : ℝ) (h : Height) :
    Continuous (diamond.stablePairWeight ε₁ ε₂ a b h) :=
  (diamond.stable_half_coefficient_continuous ε₁ a h).mul (diamond.stable_half_coefficient_continuous ε₂ b h)

theorem Plane.stable_pair_side_limit (diamond : Plane E) (ε₁ ε₂ : Evolution) (a b w : ℝ) :
    Tendsto (fun h => diamond.stablePairWeight ε₁ ε₂ a b h w) poleBoundaryHeights
      (𝓝 (stablePairSide (diamond.eta ε₁) (diamond.eta ε₂) a b w)) := by
  have hside (ε : Evolution) (a : ℝ) : Tendsto (fun h : Height => diamond.stableHalfCoefficient ε a w h)
      poleBoundaryHeights (𝓝 (stableSideValue (diamond.eta ε) a w)) := by
    have h := Complex.continuous_exp.continuousAt.tendsto.comp
      ((diamond.stable_shell_root_tendsto ε w).const_mul (-(a:ℂ)))
    refine h.congr fun h => ?_
    rw [Plane.stableHalfCoefficient,dif_pos h.property,diamond.stable_half_numerator_characters]
    rfl
  exact (hside ε₁ a).mul (hside ε₂ b)

def stableWeightedShellBoundary (η m : ℝ) (F : ℝ → ℂ) (f : MassiveMomentum → ℂ) : ℂ :=
  F (m^2) * bareComplexShellBoundary η m f +
    ∫ q, f q * ((F (shellSquare q.1 q.2) - F (m^2)) * (massiveD m q : ℂ)⁻¹)

/-- A simple pole with both moving stable numerators. At zero mass the
majorant has an integrable inverse-square-root singularity on the cone. -/
theorem Plane.stable_weighted_simple_pole (diamond : Plane E) (ε₁ ε₂ κ : Evolution) {a b m : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hm : 0 ≤ m) {f : MassiveMomentum → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    Tendsto (fun h : Height => ∫ q, (f q * diamond.stablePairWeight ε₁ ε₂ a b h (shellSquare q.1 q.2)) *
      diamond.poleCoefficient κ h (massiveD m q)) poleBoundaryHeights
      (𝓝 (stableWeightedShellBoundary (diamond.eta κ) m (stablePairSide (diamond.eta ε₁) (diamond.eta ε₂) a b) f)) := by
  let K := diamond.stablePairWeight ε₁ ε₂ a b
  let F := stablePairSide (diamond.eta ε₁) (diamond.eta ε₂) a b
  let c (h : Height) := diamond.stableShellSubtraction ε₁ a m h * diamond.stableShellSubtraction ε₂ b m h
  let P (h : Height) (q : MassiveMomentum) := diamond.poleCoefficient κ h (massiveD m q)
  let R (h : Height) (q : MassiveMomentum) := f q * ((K h (shellSquare q.1 q.2) - c h) * P h q)
  let R₀ (q : MassiveMomentum) := f q * ((F (shellSquare q.1 q.2) - F (m^2)) * (massiveD m q : ℂ)⁻¹)
  let B (q : MassiveMomentum) := ‖f q‖ * stableSubtractionBound a m (shellSquare q.1 q.2) +
    ‖f q‖ * stableSubtractionBound b m (shellSquare q.1 q.2)
  have hP (h : Height) : Continuous (P h) := (diamond.pole_coefficient_continuous κ h).comp (massiveD_continuous m)
  have hi (h : Height) : Integrable (R h) :=
    (hf.continuous.mul ((((diamond.stable_pair_weight_continuous ε₁ ε₂ a b h).comp shellSquare_continuous).sub
      continuous_const).mul (hP h))).integrable_of_hasCompactSupport hs.mul_right
  have hB : Integrable B := (stable_subtraction_test_integrable a m hf.continuous hs).add
    (stable_subtraction_test_integrable b m hf.continuous hs)
  have hc : Tendsto c poleBoundaryHeights (𝓝 (F (m^2))) :=
    (diamond.stable_subtraction_limit ε₁ a m).mul (diamond.stable_subtraction_limit ε₂ b m)
  have hR : Tendsto (fun h => ∫ q, R h q) poleBoundaryHeights (𝓝 (∫ q, R₀ q)) := by
    apply tendsto_integral_filter_of_dominated_convergence B (Eventually.of_forall fun h => (hi h).aestronglyMeasurable) _ hB
    · exact (massiveD_nonzero_ae m).mono fun q hq =>
        (((diamond.stable_pair_side_limit ε₁ ε₂ a b _).sub hc).mul
          (diamond.pole_coefficient_off_shell_limit κ hq)).const_mul (f q)
    · refine Eventually.of_forall fun h => (massiveD_nonzero_ae m).mono fun q hq => ?_
      dsimp only [R,B]
      rw [norm_mul,← mul_add]
      exact mul_le_mul_of_nonneg_left (diamond.stable_product_subtraction_bound ε₁ ε₂ κ ha hb hm h _ hq) (norm_nonneg _)
  apply ((hc.mul (diamond.bare_complex_shell_boundary κ hm hf hs)).add hR).congr
  intro h
  have hi₀ := ((hf.continuous.mul (hP h)).integrable_of_hasCompactSupport (μ := volume) hs.mul_right).const_mul (c h)
  change c h * (∫ q, f q * P h q) + (∫ q, R h q) = _
  rw [← integral_const_mul,← integral_add hi₀ (hi h)]
  apply integral_congr_ae
  exact Eventually.of_forall fun q => by dsimp only [R,P,K]; ring

theorem Plane.distinct_stable_product_limit (diamond : Plane E) (ε₁ ε₂ : Evolution) {a b m₁ m₂ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h₁ : 0 ≤ m₁) (h₂ : 0 ≤ m₂) (hne : m₁^2 ≠ m₂^2)
    {f : MassiveMomentum → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    let F := stablePairSide (diamond.eta ε₁) (diamond.eta ε₂) a b
    Tendsto (fun h : Height => ∫ q, (f q * diamond.stablePairWeight ε₁ ε₂ a b h (shellSquare q.1 q.2)) *
      (diamond.poleCoefficient ε₁ h (massiveD m₁ q) * diamond.poleCoefficient ε₂ h (massiveD m₂ q)))
      poleBoundaryHeights (𝓝 ((stableWeightedShellBoundary (diamond.eta ε₁) m₁ F f -
        stableWeightedShellBoundary (diamond.eta ε₂) m₂ F f) / ((m₁^2-m₂^2 : ℝ) : ℂ))) := by
  intro F
  exact diamond.weighted_pole_product_limit ε₁ ε₂ hne
    (fun h q => f q * diamond.stablePairWeight ε₁ ε₂ a b h (shellSquare q.1 q.2))
    (fun h ε m => ((hf.continuous.mul ((diamond.stable_pair_weight_continuous ε₁ ε₂ a b h).comp
      shellSquare_continuous)).mul ((diamond.pole_coefficient_continuous ε h).comp
      (massiveD_continuous m))).integrable_of_hasCompactSupport hs.mul_right.mul_right)
    (diamond.stable_weighted_simple_pole ε₁ ε₂ ε₁ ha hb h₁ hf hs) (diamond.stable_weighted_simple_pole ε₁ ε₂ ε₂ ha hb h₂ hf hs)

theorem stable_pair_numerator (diamond : Plane E) (ε₁ ε₂ : Evolution) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : Height) :
    let φ := fun z => Complex.exp (-principalSqrt z)
    diamond.twoLineNumerator ε₁ ε₂ φ φ a b h =
      fun q => -(diamond.eta ε₁:ℂ) * (diamond.eta ε₂:ℂ) * diamond.stablePairWeight ε₁ ε₂ a b h (shellSquare q.1 q.2) := by
  intro φ
  funext q
  change _ * (diamond.scalarKernelReadout ε₁ a φ h _ * diamond.scalarKernelReadout ε₂ b φ h _) = _
  rw [diamond.stable_scalar_kernel_readout ε₁ ha h,diamond.stable_scalar_kernel_readout ε₂ hb h]
  rfl

/-- Recover both original running-unit numerators from the common-height
stable-weighted pairing on the fixed support. -/
theorem Plane.stable_scalar_distribution_of_weighted (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (K : TopologicalSpace.Compacts MassiveMomentum) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (m₁ m₂ : ℝ)
    (hv : ∀ f : CompactMomentumTest K, ∃ z, Tendsto (fun h : Height => ∫ q,
      (f.value q * diamond.stablePairWeight ε₁ ε₂ a b h (shellSquare q.1 q.2)) *
        (diamond.poleCoefficient ε₁ h (massiveD m₁ q) * diamond.poleCoefficient ε₂ h (massiveD m₂ q)))
      poleBoundaryHeights (𝓝 z)) :
    let φ := fun z => Complex.exp (-principalSqrt z)
    ∃ T : CompactMomentumTest K →L[ℂ] ℂ, ∀ f : CompactMomentumTest K,
      Tendsto (fun h => diamond.twoLinePairing ε₁ ε₂ h φ φ a b m₁ m₂ f.value)
        poleBoundaryHeights (𝓝 (directed (T f))) := by
  intro φ
  let d := -(diamond.eta ε₁ : ℂ) * (diamond.eta ε₂ : ℂ)
  let N (h : Height) (q : MassiveMomentum) := d * diamond.stablePairWeight ε₁ ε₂ a b h (shellSquare q.1 q.2)
  let W (h : Height) (q : MassiveMomentum) := N h q * (diamond.poleCoefficient ε₁ h (massiveD m₁ q) *
    diamond.poleCoefficient ε₂ h (massiveD m₂ q))
  have hN (h : Height) : Continuous (N h) :=
    continuous_const.mul ((diamond.stable_pair_weight_continuous ε₁ ε₂ a b h).comp shellSquare_continuous)
  have hn (h : Height) : diamond.twoLineNumerator ε₁ ε₂ φ φ a b h = N h :=
    stable_pair_numerator diamond ε₁ ε₂ ha hb h
  have hW (h : Height) : Continuous (W h) := (hN h).mul
    (((diamond.pole_coefficient_continuous ε₁ h).comp (massiveD_continuous m₁)).mul
      ((diamond.pole_coefficient_continuous ε₂ h).comp (massiveD_continuous m₂)))
  have hlim (f : CompactMomentumTest K) : ∃ z, Tendsto (fun h => ∫ q, f.value q * W h q) poleBoundaryHeights (𝓝 z) := by
    obtain ⟨_,H⟩ := hv f
    refine ⟨_, (H.const_mul d).congr fun h => ?_⟩
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun q => by dsimp only [W,N]; ring
  obtain ⟨T,hT⟩ := compact_momentum_boundary_functional K W (fun h => (hW h).continuousOn.integrableOn_compact K.isCompact) hlim
  refine ⟨T,fun f => (directed_shell_readout_continuous.continuousAt.tendsto.comp (hT f)).congr fun h => ?_⟩
  have h := diamond.two_line_pairing_readout ε₁ ε₂ h φ φ a b m₁ m₂ f.contDiff.continuous f.compact_support
    ((hn h).symm ▸ hN h)
  simpa only [hn] using h.symm

/-- The literal two-line stable-half product, with both running unit
vectors and their prescribed pole sides, defines a continuous functional on
each compact Cartesian C² test space whenever the mass shells are distinct. -/
theorem Plane.distinct_stable_scalar_distribution (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (K : TopologicalSpace.Compacts MassiveMomentum) {a b m₁ m₂ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h₁ : 0 ≤ m₁) (h₂ : 0 ≤ m₂) (hne : m₁^2 ≠ m₂^2) :
    let φ := fun z => Complex.exp (-principalSqrt z)
    ∃ T : CompactMomentumTest K →L[ℂ] ℂ, ∀ f : CompactMomentumTest K,
      Tendsto (fun h => diamond.twoLinePairing ε₁ ε₂ h φ φ a b m₁ m₂ f.value)
        poleBoundaryHeights (𝓝 (directed (T f))) := by
  exact diamond.stable_scalar_distribution_of_weighted ε₁ ε₂ K ha hb m₁ m₂
    (fun f => ⟨_, diamond.distinct_stable_product_limit ε₁ ε₂ ha hb h₁ h₂ hne f.contDiff f.compact_support⟩)

end UV.SectorPlane
