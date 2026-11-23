import UV.ContinueTransverseChartFamily

/-! Both pole normals and the chart's full numerator use one common
height. Joint C² data account for the mixed cancellation in the limit. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E]

private theorem interval_compact_of_vanishes {g : ℝ → ℂ} {R : ℝ}
    (h : ∀ x, R < |x| → g x = 0) : HasCompactSupport g := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R))
  intro x hx
  exact h x (lt_of_not_ge (fun hh => hx (abs_le.mp hh)))

/-- Moving one-dimensional boundary tests share a compact support and
a Lipschitz constant near the positive-height limit. -/
theorem Plane.transverse_normal_single_moving_test (diamond : Plane E) (ε : Evolution)
    (g : Height → ℝ → ℂ) (g₀ : ℝ → ℂ) {L L₀ : ℝ≥0} {R : ℝ} (hR : 1 ≤ R)
    (hgc : ∀ h, Continuous (g h)) (hgL : ∀ᶠ h in poleBoundaryHeights, LipschitzWith L (g h))
    (hg₀ : LipschitzWith L₀ g₀)
    (hgs : ∀ h x, R < |x| → g h x = 0) (hg₀s : ∀ x, R < |x| → g₀ x = 0)
    (hg : ∀ x, Tendsto (fun h => g h x) poleBoundaryHeights (𝓝 (g₀ x))) :
    Tendsto (fun h => ∫ x, diamond.poleCoefficient ε h x * g h x)
      poleBoundaryHeights
      (𝓝 (complexShellPV g₀ - Complex.I * (Real.pi : ℂ) * (diamond.eta ε : ℂ) * g₀ 0)) := by
  let u (h : Height) (x : ℝ) := g h x - g₀ x
  let U (h : Height) (x : ℝ) := u h x - transverseNormalCutoff x * u h 0
  let P := diamond.poleCoefficient ε
  let C := (L : ℝ) + (L₀ : ℝ) + 1
  let M := (Icc (-R) R).indicator (fun _ : ℝ => C)
  have hM : Integrable M :=
    (integrableOn_const (C := C) isCompact_Icc.measure_lt_top.ne).integrable_indicator measurableSet_Icc
  have hu (x : ℝ) : Tendsto (fun h => u h x) poleBoundaryHeights (𝓝 0) := by
    simpa only [u,sub_self] using (hg x).sub_const (g₀ x)
  have hu₀ : ∀ᶠ h in poleBoundaryHeights, ‖u h 0‖ ≤ 1 := by
    have H := (hu 0).norm
    rw [norm_zero] at H
    exact H (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hUc (h : Height) : Continuous (U h) :=
    ((hgc h).sub hg₀.continuous).sub (transverse_normal_cutoff_lipschitz.continuous.mul continuous_const)
  have hUs (h : Height) (x : ℝ) (hx : R < |x|) : U h x = 0 := by
    have hcut : transverseNormalCutoff x = 0 := by
      unfold transverseNormalCutoff
      rw [massive_normal_cutoff_zero zero_lt_one (hR.trans hx.le),Complex.ofReal_zero]
    simp [U,u,hgs h x hx,hg₀s x hx,hcut]
  have hUlim : Tendsto (fun h : Height => ∫ x, P h x * U h x) poleBoundaryHeights (𝓝 0) := by
    rw [← integral_zero (μ := (volume : Measure ℝ)) (G := ℂ)]
    refine tendsto_integral_filter_of_dominated_convergence M ?_ ?_ hM ?_
    · exact Eventually.of_forall fun h =>
        ((diamond.pole_coefficient_continuous ε h).mul (hUc h)).aestronglyMeasurable
    · filter_upwards [hu₀,hgL] with h hh hl
      have hnon : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
      filter_upwards [hnon] with x hx
      by_cases hb : x ∈ Icc (-R) R
      · have he : U h x = (u h x - u h 0) + (1-transverseNormalCutoff x)*u h 0 := by
          dsimp only [U]
          ring
        have h₁ : ‖u h x - u h 0‖ ≤ (L : ℝ)*|x| + (L₀ : ℝ)*|x| := by
          have H := (hl.sub hg₀).norm_sub_le x 0
          simpa only [u, Real.norm_eq_abs, sub_zero, NNReal.coe_add, add_mul] using H
        have h₂ : ‖(1-transverseNormalCutoff x)*u h 0‖ ≤ |x| := by
          rw [norm_mul]
          exact (mul_le_mul (transverse_cutoff_defect_bound x) hh (norm_nonneg _) (abs_nonneg _)).trans_eq
            (mul_one _)
        have hB : ‖U h x‖ ≤ C * |x| := by
          rw [he]
          exact ((norm_add_le _ _).trans (add_le_add h₁ h₂)).trans_eq (by dsimp only [C]; ring)
        dsimp only [M]
        rw [indicator_of_mem hb, norm_mul]
        calc
          _ ≤ |x|⁻¹ * (C*|x|) := mul_le_mul
            (diamond.pole_coefficient_off_shell_bound ε h hx) hB (norm_nonneg _) (by positivity)
          _ = C := by field_simp [abs_ne_zero.mpr hx]
      · simp [M, indicator_of_notMem hb, hUs h x (lt_of_not_ge (fun H => hb (abs_le.mp H)))]
    · have hnon : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
      filter_upwards [hnon] with x hx
      have H := (diamond.pole_coefficient_off_shell_limit ε hx).mul
        ((hu x).sub ((hu 0).const_mul (transverseNormalCutoff x)))
      simpa only [P, U, mul_zero, sub_zero] using H
  have hzero : Tendsto (fun h => ∫ x, P h x * u h x) poleBoundaryHeights (𝓝 0) := by
    have H := hUlim.add ((hu 0).mul (diamond.transverse_normal_cutoff_limit ε))
    simp only [zero_mul,add_zero] at H
    refine H.congr fun h => ?_
    have hi : Integrable (fun x => P h x * U h x) :=
      ((diamond.pole_coefficient_continuous ε h).mul (hUc h)).integrable_of_hasCompactSupport
        (interval_compact_of_vanishes (hUs h)).mul_left
    have hj : Integrable (fun x => P h x * transverseNormalCutoff x) :=
      ((diamond.pole_coefficient_continuous ε h).mul transverse_normal_cutoff_lipschitz.continuous).integrable_of_hasCompactSupport
        transverse_normal_cutoff_compact.mul_left
    change (∫ x, P h x * U h x) + u h 0 * (∫ x, P h x * transverseNormalCutoff x) = _
    rw [← integral_const_mul, ← integral_add hi (hj.const_mul _)]
    apply integral_congr_ae
    refine Eventually.of_forall fun x => ?_
    dsimp only [U]
    ring
  have H := (diamond.transverse_normal_single_test ε hg₀ (interval_compact_of_vanishes hg₀s)).add hzero
  simp only [add_zero] at H
  refine H.congr fun h => ?_
  have hi₀ : Integrable (fun x => P h x * g₀ x) :=
    ((diamond.pole_coefficient_continuous ε h).mul hg₀.continuous).integrable_of_hasCompactSupport
      (interval_compact_of_vanishes hg₀s).mul_left
  have hi : Integrable (fun x => P h x * u h x) :=
    ((diamond.pole_coefficient_continuous ε h).mul ((hgc h).sub hg₀.continuous)).integrable_of_hasCompactSupport
      ((interval_compact_of_vanishes (hgs h)).sub (interval_compact_of_vanishes hg₀s)).mul_left
  change (∫ x, P h x * g₀ x) + (∫ x, P h x * u h x) = _
  rw [← integral_add hi₀ hi]
  apply integral_congr_ae
  refine Eventually.of_forall fun x => ?_
  dsimp only [u]
  ring

/-- The two-normal boundary remains valid when the actual chart numerator
and density depend jointly C² on the shared height and both normals. -/
theorem Plane.transverse_normal_product_moving_boundary (diamond : Plane E) (ε₁ ε₂ : Evolution)
    (K : TopologicalSpace.Compacts (ℝ × ℝ)) {F : ℝ → (ℝ × ℝ) → ℂ}
    (hF : ContDiff ℝ 2 (Function.uncurry F)) (hFs : ∀ t p, p ∉ K → F t p = 0) :
    Tendsto (fun h : Height => ∫ p, diamond.poleCoefficient ε₁ h p.1 *
      diamond.poleCoefficient ε₂ h p.2 * F h p ∂transverseNormalVolume) poleBoundaryHeights
      (𝓝 (transverseNormalBoundary (diamond.eta ε₁) (diamond.eta ε₂) (F 0))) := by
  have hS (t : ℝ) : ContDiff ℝ 2 (F t) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hs (t : ℝ) : HasCompactSupport (F t) := HasCompactSupport.intro K.isCompact (hFs t)
  obtain ⟨L₀,L,B,_,hU⟩ := transverse_normal_family_uniform_lipschitz K hF hFs
  obtain ⟨R,hR,hfar,hrest⟩ := transverse_normal_family_box K hFs
  let C := (L : ℝ) + 2*(L₀ : ℝ) + B
  let J : TopologicalSpace.Compacts (ℝ × ℝ) :=
    ⟨Icc (-R) R ×ˢ Icc (-R) R,isCompact_Icc.prod isCompact_Icc⟩
  have hpoint (p : ℝ × ℝ) : Tendsto (fun h : Height => F h p) poleBoundaryHeights (𝓝 (F 0 p)) :=
    (hF.continuous.comp (continuous_id.prodMk continuous_const)).continuousAt.tendsto.comp pole_height_tendsto_zero
  have hRpoint (p : ℝ × ℝ) : Tendsto (fun h : Height => transverseNormalRemainder (F h) p)
      poleBoundaryHeights (𝓝 (transverseNormalRemainder (F 0) p)) :=
    (((hpoint p).sub ((hpoint (0,p.2)).const_mul (transverseNormalCutoff p.1))).sub
      ((hpoint (p.1,0)).const_mul (transverseNormalCutoff p.2))).add
        ((hpoint (0,0)).const_mul (transverseNormalCutoff p.1 * transverseNormalCutoff p.2))
  have hb : ∀ᶠ h : Height in poleBoundaryHeights, ∀ p,
      ‖transverseNormalRemainder (F h) p‖ ≤ C * |p.1| * |p.2| := by
    filter_upwards [hU] with h H
    exact transverse_normal_remainder_bound_of_lipschitz H.1
      (transverse_normal_mixed_difference_of_lipschitz ((hS h).differentiable (by norm_num)) H.2.1) H.2.2
  have Hr := transverse_normal_remainder_moving_limit
    (fun h => transverseNormalRemainder (F h)) (transverseNormalRemainder (F 0)) J (C := C)
    (Eventually.of_forall fun h => transverse_normal_remainder_continuous (hS h).continuous)
    (Eventually.of_forall fun h => hrest h) hb hRpoint
    (diamond.poleCoefficient ε₁) (diamond.poleCoefficient ε₂)
    (diamond.pole_coefficient_continuous ε₁) (diamond.pole_coefficient_continuous ε₂)
    (fun h _ hx => diamond.pole_coefficient_off_shell_bound ε₁ h hx)
    (fun h _ hx => diamond.pole_coefficient_off_shell_bound ε₂ h hx)
    (fun _ hx => diamond.pole_coefficient_off_shell_limit ε₁ hx)
    (fun _ hx => diamond.pole_coefficient_off_shell_limit ε₂ hx)
  have hx (t : ℝ) : ContDiff ℝ 2 (fun x => F t (x,0)) :=
    (hS t).comp (contDiff_id.prodMk contDiff_const)
  have hy (t : ℝ) : ContDiff ℝ 2 (fun y => F t (0,y)) :=
    (hS t).comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨hsx,hsy⟩ := transverse_normal_slice_compact (hs 0)
  obtain ⟨Lx,hLx⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsx (hx 0) (by norm_num)
  obtain ⟨Ly,hLy⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsy (hy 0) (by norm_num)
  have hxl : ∀ᶠ h : Height in poleBoundaryHeights, LipschitzWith L₀ (fun x => F h (x,0)) := by
    filter_upwards [hU] with h H
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simpa [Prod.dist_eq] using H.1.dist_le_mul (x,0) (y,0)
  have hyl : ∀ᶠ h : Height in poleBoundaryHeights, LipschitzWith L₀ (fun y => F h (0,y)) := by
    filter_upwards [hU] with h H
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simpa [Prod.dist_eq] using H.1.dist_le_mul (0,x) (0,y)
  have Hx := diamond.transverse_normal_single_moving_test ε₁ (fun h x => F h (x,0)) (fun x => F 0 (x,0))
    hR (fun h => (hx h).continuous) hxl hLx (fun h x H => hfar h (x,0) (Or.inl H))
    (fun x H => hfar 0 (x,0) (Or.inl H)) (fun x => hpoint (x,0))
  have Hy := diamond.transverse_normal_single_moving_test ε₂ (fun h y => F h (0,y)) (fun y => F 0 (0,y))
    hR (fun h => (hy h).continuous) hyl hLy (fun h y H => hfar h (0,y) (Or.inr H))
    (fun y H => hfar 0 (0,y) (Or.inr H)) (fun y => hpoint (0,y))
  have Hc₁ := diamond.transverse_normal_cutoff_limit ε₁
  have Hc₂ := diamond.transverse_normal_cutoff_limit ε₂
  have H := ((Hr.add (Hc₁.mul Hy)).add (Hx.mul Hc₂)).sub ((hpoint (0,0)).mul (Hc₁.mul Hc₂))
  let c (ε : Evolution) := Complex.I * (Real.pi : ℂ) * (diamond.eta ε : ℂ)
  have he : transverseNormalPV₂ (F 0) +
      (-c ε₁) * (complexShellPV (fun y => F 0 (0,y)) - c ε₂ * F 0 (0,0)) +
      (complexShellPV (fun x => F 0 (x,0)) - c ε₁ * F 0 (0,0)) * (-c ε₂) -
      F 0 (0,0) * ((-c ε₁) * (-c ε₂)) =
        transverseNormalBoundary (diamond.eta ε₁) (diamond.eta ε₂) (F 0) := by
    simp only [transverseNormalBoundary, c]
    ring_nf
    rw [Complex.I_sq]
    ring
  change Tendsto _ _ (𝓝 (transverseNormalPV₂ (F 0) +
      (-c ε₁) * (complexShellPV (fun y => F 0 (0,y)) - c ε₂ * F 0 (0,0)) +
      (complexShellPV (fun x => F 0 (x,0)) - c ε₁ * F 0 (0,0)) * (-c ε₂) -
      F 0 (0,0) * ((-c ε₁) * (-c ε₂)))) at H
  rw [he] at H
  exact H.congr (fun h => by
    rw [transverse_normal_product_split _ _ (diamond.pole_coefficient_continuous ε₁ h)
      (diamond.pole_coefficient_continuous ε₂ h) (hS h).continuous (hs h)])

end UV.SectorPlane
