import UV.ContinueTransverseChartProduct
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Joint C² regularity controls all mixed divided differences uniformly
as the common positive height tends to zero. -/

noncomputable section

namespace UV.SectorPlane

open Filter Set MeasureTheory Metric
open scoped Topology NNReal

private def transverseHeightBump : ContDiffBump (0 : ℝ) :=
  ⟨1,2,by norm_num,by norm_num⟩

/-- The compact support in the normal chart stays fixed. Compactification
in height is used only to furnish uniform derivative bounds. -/
theorem transverse_normal_family_uniform_lipschitz (K : TopologicalSpace.Compacts (ℝ × ℝ))
    {F : ℝ → (ℝ × ℝ) → ℂ} (hF : ContDiff ℝ 2 (Function.uncurry F))
    (hFs : ∀ t p, p ∉ K → F t p = 0) :
    ∃ L₀ L : ℝ≥0, ∃ B ≥ 0, ∀ᶠ h : Height in poleBoundaryHeights,
      LipschitzWith L₀ (F h) ∧ LipschitzWith L (fderiv ℝ (F h)) ∧ ‖F h (0,0)‖ ≤ B := by
  let G (t : ℝ) (p : ℝ × ℝ) := (transverseHeightBump t : ℂ) * F t p
  let G' := Function.uncurry G
  have hG : ContDiff ℝ 2 G' := by
    exact (Complex.ofRealCLM.contDiff.comp (transverseHeightBump.contDiff.comp contDiff_fst)).mul hF
  have hGs : HasCompactSupport G' := by
    let T := Icc (-2 : ℝ) 2 ×ˢ (K : Set (ℝ × ℝ))
    apply HasCompactSupport.intro (isCompact_Icc.prod K.isCompact : IsCompact T)
    intro p hp
    by_cases ht : p.1 ∈ Icc (-2 : ℝ) 2
    · have hq : p.2 ∉ K := fun hq => hp ⟨ht,hq⟩
      simp [G',G,Function.uncurry,hFs p.1 p.2 hq]
    · have hzero : transverseHeightBump p.1 = 0 := by
        apply transverseHeightBump.zero_of_le_dist
        change (2 : ℝ) ≤ dist p.1 0
        rw [Real.dist_eq, sub_zero]
        exact (lt_of_not_ge (fun h => ht (abs_le.mp h))).le
      simp [G',G,Function.uncurry,hzero]
  obtain ⟨L₀,hL₀⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hGs hG (by norm_num)
  have hDG : ContDiff ℝ 1 (fderiv ℝ G') :=
    hG.fderiv_right (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hGs.fderiv ℝ) hDG le_rfl
  obtain ⟨B,hB⟩ := hG.continuous.bounded_above_of_compact_support hGs
  let i : (ℝ × ℝ) →L[ℝ] (ℝ × (ℝ × ℝ)) := ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)
  have hi : ‖i‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro p
    simp [i, Prod.norm_def]
  have hD (t : ℝ) (p : ℝ × ℝ) :
      fderiv ℝ (G t) p = (fderiv ℝ G' (t,p)).comp i := by
    have hp : HasFDerivAt (fun q : ℝ × ℝ => (t,q)) i p := by
      simpa [i] using (i.hasFDerivAt (x := p)).const_add (t,0)
    exact ((hG.differentiable (by norm_num) (t,p)).hasFDerivAt.comp p hp).fderiv
  have hnear : ∀ᶠ h : Height in poleBoundaryHeights, (h : ℝ) ≤ 1 :=
    pole_height_tendsto_zero (eventually_le_nhds zero_lt_one)
  refine ⟨L₀,L,B,(norm_nonneg _).trans (hB (0,(0,0))),?_⟩
  filter_upwards [hnear] with h hh
  have hχ : transverseHeightBump (h : ℝ) = 1 := by
    apply transverseHeightBump.one_of_mem_closedBall
    change dist (h : ℝ) 0 ≤ (1 : ℝ)
    simpa only [Real.dist_eq, sub_zero, abs_of_pos h.property] using hh
  have he : G (h : ℝ) = F h := by
    funext p
    simp [G,hχ]
  rw [← he]
  refine ⟨LipschitzWith.of_dist_le_mul (fun p q => ?_), LipschitzWith.of_dist_le_mul (fun p q => ?_),
    hB ((h : ℝ),(0,0))⟩
  · simpa [G', Prod.dist_eq] using hL₀.dist_le_mul ((h : ℝ),p) ((h : ℝ),q)
  · rw [dist_eq_norm, hD, hD, ← ContinuousLinearMap.sub_comp]
    calc
      _ ≤ ‖fderiv ℝ G' ((h : ℝ),p) - fderiv ℝ G' ((h : ℝ),q)‖ * ‖i‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (L : ℝ) * dist p q := by
        have H := hL.norm_sub_le ((h : ℝ),p) ((h : ℝ),q)
        exact (mul_le_of_le_one_right (norm_nonneg _) hi).trans (by
          simpa [Prod.norm_def, dist_eq_norm] using H)

theorem transverse_normal_family_box (K : TopologicalSpace.Compacts (ℝ × ℝ))
    {F : ℝ → (ℝ × ℝ) → ℂ} (hFs : ∀ t p, p ∉ K → F t p = 0) :
    ∃ R ≥ 1, (∀ t p, R < |p.1| ∨ R < |p.2| → F t p = 0) ∧
      (∀ t p, p ∉ Icc (-R) R ×ˢ Icc (-R) R → transverseNormalRemainder (F t) p = 0) := by
  obtain ⟨C,hC⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ × ℝ)).mp K.isCompact.isBounded
  let R := max 1 C
  have hs (t : ℝ) (p : ℝ × ℝ) (hp : R < |p.1| ∨ R < |p.2|) : F t p = 0 := by
    apply hFs
    intro H
    have hn : ‖p‖ ≤ R := (by simpa using hC H : ‖p‖ ≤ C).trans (le_max_right _ _)
    change max ‖p.1‖ ‖p.2‖ ≤ R at hn
    rcases hp with hp | hp
    · exact hp.not_ge (by simpa [Real.norm_eq_abs] using (le_max_left ‖p.1‖ ‖p.2‖).trans hn)
    · exact hp.not_ge (by simpa [Real.norm_eq_abs] using (le_max_right ‖p.1‖ ‖p.2‖).trans hn)
  have hc (x : ℝ) (hx : R < |x|) : transverseNormalCutoff x = 0 := by
    unfold transverseNormalCutoff
    rw [massive_normal_cutoff_zero zero_lt_one ((le_max_left _ _).trans hx.le), Complex.ofReal_zero]
  refine ⟨R,le_max_left _ _,hs,?_⟩
  intro t p hp
  by_cases hx : R < |p.1|
  · simp [transverseNormalRemainder, hs t p (Or.inl hx), hs t (p.1,0) (Or.inl hx), hc _ hx]
  · have hy : R < |p.2| := by
      by_contra! h
      exact hp ⟨abs_le.mp (le_of_not_gt hx),abs_le.mp h⟩
    simp [transverseNormalRemainder, hs t p (Or.inr hy), hs t (0,p.2) (Or.inr hy), hc _ hy]

end UV.SectorPlane
