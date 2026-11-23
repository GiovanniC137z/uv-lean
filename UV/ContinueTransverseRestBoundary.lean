import UV.ContinueTransverseRestScalar
import UV.ContinueTransverseChartMoving
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Common-height distributional limit of the two actual stable scalar
lines near the intersecting massive shells of the symmetric rest routing. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Metric Real Set UV.Carrier
open scoped Topology UV.SectorPlane

variable {E : Type*} [NormedAddCommGroup E]

/-- The explicit two-normal boundary for the localized original
directed product. Each pole uses the same positive height before
the limit, and each prescribed side keeps its own η. -/
theorem Plane.rest_stable_transverse_boundary (diamond : Plane E) (ε₁ ε₂ : Evolution)
    {m t a b : ℝ} (ht : 0 < t) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {f : MassiveMomentum → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (K : TopologicalSpace.Compacts (ℝ × ℝ)) (hK : (K : Set (ℝ × ℝ)) ⊆ stableRestNormalRegion m t)
    (hgK : ∀ Y ∉ K, g Y = 0) :
    let φ := fun z => Complex.exp (-principalSqrt z)
    let F := diamond.restStableNormalTest ε₁ ε₂ m t a b f g
    Tendsto (fun h => diamond.shiftedScalarPairing ε₁ ε₂ h φ φ a b m m (axialTransfer (t/2))
      (axialTransfer (-(t/2))) (fun q => f q * g (symmetricRestNormals m t q)))
      poleBoundaryHeights
      (𝓝 (directed ((4 * π) • transverseNormalBoundary (diamond.eta ε₁) (diamond.eta ε₂) (F 0)))) := by
  intro φ F
  have hF : ContDiff ℝ 2 (Function.uncurry F) :=
    diamond.rest_stable_normal_test_contDiff ε₁ ε₂ m t a b hf hg K hK hgK
  have hFs (p : ℝ) (Y : ℝ × ℝ) (hY : Y ∉ K) : F p Y = 0 := by
    simp [F,Plane.restStableNormalTest,hgK Y hY]
  have H := diamond.transverse_normal_product_moving_boundary ε₁ ε₂ K hF hFs
  refine (directed_shell_readout_continuous.continuousAt.tendsto.comp (H.const_smul (4 * π))).congr fun h => ?_
  have hgs (Y : ℝ × ℝ) (hY : g Y ≠ 0) : Y ∈ stableRestNormalRegion m t :=
    hK (by by_contra hn; exact hY (hgK Y hn))
  rw [diamond.rest_stable_pairing_normal_integral ε₁ ε₂ ht ha hb h hf.continuous hs hg.continuous hgs]
  dsimp only [Function.comp_apply]
  congr 2
  apply integral_congr_ae
  exact Eventually.of_forall fun Y => mul_comm _ _

/-- After localization to the simultaneous normal chart, the limits
give a continuous linear functional on each fixed compact Cartesian
C² test space, with values represented in the original directed line. -/
theorem Plane.rest_stable_transverse_distribution (diamond : Plane E) (ε₁ ε₂ : Evolution)
    {m t a b : ℝ} (ht : 0 < t) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (K : TopologicalSpace.Compacts (ℝ × ℝ)) (hK : (K : Set (ℝ × ℝ)) ⊆ stableRestNormalRegion m t)
    (hgK : ∀ Y ∉ K, g Y = 0) (J : TopologicalSpace.Compacts MassiveMomentum) :
    let φ := fun z => Complex.exp (-principalSqrt z)
    ∃ L : CompactMomentumTest J →L[ℂ] ℂ, ∀ f : CompactMomentumTest J,
      Tendsto (fun h => diamond.shiftedScalarPairing ε₁ ε₂ h φ φ a b m m
        (axialTransfer (t/2)) (axialTransfer (-(t/2)))
        (fun q => f.value q * g (symmetricRestNormals m t q))) poleBoundaryHeights
        (𝓝 (directed (L f))) := by
  intro φ
  let N := symmetricRestNormals m t
  let U (h : Height) := diamond.restStableNormalNumerator ε₁ ε₂ m a b h
  let P (h : Height) (Y : ℝ × ℝ) := diamond.poleCoefficient ε₁ h Y.1 * diamond.poleCoefficient ε₂ h Y.2
  let W (h : Height) (q : MassiveMomentum) := g (N q) * (U h (N q) * P h (N q))
  have hN : Continuous N :=
    (shiftedD_contDiff (n := 1) _ _).continuous.prodMk (shiftedD_contDiff (n := 1) _ _).continuous
  have hU (h : Height) : Continuous (U h) := diamond.rest_stable_normal_numerator_continuous ε₁ ε₂ m a b h
  have hP (h : Height) : Continuous (P h) :=
    ((diamond.pole_coefficient_continuous ε₁ h).comp continuous_fst).mul
      ((diamond.pole_coefficient_continuous ε₂ h).comp continuous_snd)
  have hW (h : Height) : Continuous (W h) :=
    (hg.continuous.comp hN).mul (((hU h).mul (hP h)).comp hN)
  have hread (f : CompactMomentumTest J) (h : Height) :
      diamond.shiftedScalarPairing ε₁ ε₂ h φ φ a b m m (axialTransfer (t/2)) (axialTransfer (-(t/2)))
        (fun q => f.value q * g (N q)) = directed (∫ q, f.value q * W h q) := by
    have hci : Continuous (fun q => (f.value q * g (N q)) * (U h (N q) * P h (N q))) :=
      (f.contDiff.continuous.mul (hg.continuous.comp hN)).mul (((hU h).mul (hP h)).comp hN)
    have hi := hci.integrable_of_hasCompactSupport (μ := volume) f.compact_support.mul_right.mul_right
    rw [diamond.shifted_scalar_pairing_eq_of_numerator ε₁ ε₂ h φ φ a b m m _ _ hi (fun q hq _ _ => by
      apply diamond.rest_stable_normal_numerator_eq ε₁ ε₂ ht ha hb h q
      apply hK
      by_contra hn
      exact hq (by rw [hgK _ hn,mul_zero]))]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun q => mul_assoc _ _ _
  have hlim (f : CompactMomentumTest J) : ∃ z, Tendsto (fun h => ∫ q, f.value q * W h q)
      poleBoundaryHeights (𝓝 z) := by
    have hc : Continuous (fun z : QuotientCarrier => (quotientCharacterEquiv z).1) :=
      continuous_fst.comp quotientCharacterIsometry.continuous
    have H := hc.continuousAt.tendsto.comp (diamond.rest_stable_transverse_boundary ε₁ ε₂
      ht ha hb f.contDiff f.compact_support hg K hK hgK)
    refine ⟨_,H.congr fun h => ?_⟩
    change (quotientCharacterEquiv (diamond.shiftedScalarPairing ε₁ ε₂ h φ φ a b m m
      (axialTransfer (t/2)) (axialTransfer (-(t/2)))
      (fun q => f.value q * g (N q)))).1 = _
    rw [hread f h]
    simp only [directed,AlgEquiv.apply_symm_apply]
  obtain ⟨L,hL⟩ := compact_momentum_boundary_functional J W
    (fun h => (hW h).continuousOn.integrableOn_compact J.isCompact) hlim
  exact ⟨L,fun f => (directed_shell_readout_continuous.continuousAt.tendsto.comp (hL f)).congr
    (fun h => (hread f h).symm)⟩

/-- At the simultaneous shell, the η factors from the two scalar
numerators cancel the η factors in the double delta. The remaining
amplitude retains the spatial unit-sphere average and the exact phase. -/
theorem Plane.rest_stable_double_delta_term (diamond : Plane E) (ε₁ ε₂ : Evolution)
    {m t : ℝ} (hm : 0 ≤ m) (ht : 0 < t) (a b : ℝ)
    (f : MassiveMomentum → ℂ) (g : ℝ × ℝ → ℂ) :
    let r := Real.sqrt ((t/2)^2-m^2)
    (4 * π : ℝ) • (-(π : ℂ)^2 * (diamond.eta ε₁ : ℂ) * (diamond.eta ε₂ : ℂ) *
      diamond.restStableNormalTest ε₁ ε₂ m t a b f g 0 0) =
      (-(π^3 * r/t) : ℝ) • (coneSpatialMean f (0,r) * g 0 *
        Complex.exp (Complex.I * (((diamond.eta ε₁ * a + diamond.eta ε₂ * b) * m : ℝ) : ℂ))) := by
  intro r
  rw [diamond.rest_stable_normal_test_at_intersection ε₁ ε₂ hm t a b f g]
  have e₁ : (diamond.eta ε₁ : ℂ)^2 = 1 := by exact_mod_cast diamond.eta_sq ε₁
  have e₂ : (diamond.eta ε₂ : ℂ)^2 = 1 := by exact_mod_cast diamond.eta_sq ε₂
  rw [abs_of_pos ht]
  simp only [Complex.real_smul]
  let R := Real.sqrt ((t/2)^2-m^2)
  let U := coneSpatialMean f (0,R) * g 0 *
    Complex.exp (Complex.I * (((diamond.eta ε₁ * a + diamond.eta ε₂ * b) * m : ℝ) : ℂ))
  calc
    _ = (-(π^3 * r/t) : ℝ) * ((diamond.eta ε₁ : ℂ)^2 * (diamond.eta ε₂ : ℂ)^2 * U) := by
      have hn : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
      dsimp only [U,R,r]
      push_cast
      field_simp [hn]
    _ = _ := by simp [e₁,e₂,U,R,r]

/-- Above twice the mass, all compact Cartesian C² tests supported in a
neighborhood of the common shell have a limit for the actual product.
The radius is a cutoff in the two normal coordinates. The support may
contain every spatial direction on the common shell. -/
theorem Plane.rest_stable_transverse_local_limit (diamond : Plane E) (ε₁ ε₂ : Evolution)
    {m t a b : ℝ} (hm : 0 < m) (ht : 2*m < t) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ ρ > (0:ℝ), ∀ f : MassiveMomentum → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      (∀ q ∈ tsupport f, symmetricRestNormals m t q ∈ closedBall (0 : ℝ × ℝ) ρ) →
      let φ := fun z => Complex.exp (-principalSqrt z)
      ∃ L : QuotientCarrier, Tendsto (fun h =>
        diamond.shiftedScalarPairing ε₁ ε₂ h φ φ a b m m (axialTransfer (t/2))
          (axialTransfer (-(t/2))) f) poleBoundaryHeights (𝓝 L) := by
  have ht' : 0 < t := by linarith
  obtain ⟨δ,hδ,hs⟩ := Metric.isOpen_iff.mp (stable_rest_normal_region_open m t) (0 : ℝ × ℝ)
    (zero_mem_stable_rest_normal_region hm ht)
  let B : ContDiffBump (0 : ℝ) := ⟨δ/4,δ/2,by positivity,by linarith⟩
  let K : TopologicalSpace.Compacts (ℝ × ℝ) := ⟨closedBall 0 B.rOut,isCompact_closedBall _ _⟩
  have hK : (K : Set (ℝ × ℝ)) ⊆ stableRestNormalRegion m t :=
    (closedBall_subset_ball (show B.rOut < δ by dsimp [B]; linarith)).trans hs
  let g (Y : ℝ × ℝ) : ℂ := ((B Y.1 * B Y.2 : ℝ) : ℂ)
  have hg : ContDiff ℝ 2 g := Complex.ofRealCLM.contDiff.comp
    (((B.contDiff : ContDiff ℝ 2 (B : ℝ → ℝ)).comp contDiff_fst).mul
      ((B.contDiff : ContDiff ℝ 2 (B : ℝ → ℝ)).comp contDiff_snd))
  have hBzero (x : ℝ) (hx : B.rOut < ‖x‖) : B x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    rw [B.tsupport_eq]
    simpa only [mem_closedBall,dist_zero_right] using hx.not_ge
  have hgK (Y : ℝ × ℝ) (hY : Y ∉ K) : g Y = 0 := by
    have H : B.rOut < max ‖Y.1‖ ‖Y.2‖ := by
      apply lt_of_not_ge
      change Y ∉ closedBall (0 : ℝ × ℝ) B.rOut at hY
      simpa only [mem_closedBall,dist_zero_right,Prod.norm_def] using hY
    rcases lt_max_iff.mp H with h | h
    · simp [g,hBzero _ h]
    · simp [g,hBzero _ h]
  refine ⟨B.rIn,B.rIn_pos,fun f hf hfs hfN => ?_⟩
  intro φ
  have he : (fun q => f q * g (symmetricRestNormals m t q)) = f := by
    funext q
    by_cases hn : f q = 0
    · simp [hn]
    · have H : ‖symmetricRestNormals m t q‖ ≤ B.rIn := by
        simpa only [mem_closedBall,dist_zero_right] using hfN q (subset_tsupport f hn)
      let Y := symmetricRestNormals m t q
      have H₁ : B Y.1 = 1 := B.one_of_mem_closedBall (by
        rw [mem_closedBall,dist_zero_right]
        exact (le_max_left _ _).trans H)
      have H₂ : B Y.2 = 1 := B.one_of_mem_closedBall (by
        rw [mem_closedBall,dist_zero_right]
        exact (le_max_right _ _).trans H)
      simp only [g,← show Y = symmetricRestNormals m t q from rfl,H₁,H₂,mul_one,Complex.ofReal_one]
  exact ⟨_, by
    simpa only [he] using (diamond.rest_stable_transverse_boundary ε₁ ε₂ ht' ha hb hf hfs hg K hK hgK)⟩

end UV.SectorPlane
