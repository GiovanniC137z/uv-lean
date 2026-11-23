import UV.ContinueCutBoundary

/-! A compact regular chart test times an arbitrary continued numerator.
Uniform C¹ convergence on the support of the fixed test suffices for the
individual directed coefficient extraction. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory UV.Carrier
open scoped Topology NNReal

private def cutChartNormalDerivative (f : ℝ × Spatial → ℂ) (x : ℝ × Spatial) : ℂ :=
  fderiv ℝ f x (1, 0)

private theorem cut_chart_normal_hasDerivAt {f : ℝ × Spatial → ℂ}
    (hf : ContDiff ℝ 1 f) (D : ℝ) (p : Spatial) :
    HasDerivAt (fun y => f (y, p)) (cutChartNormalDerivative f (D, p)) D := by
  exact ((hf.differentiable le_rfl).differentiableAt.hasFDerivAt).comp_hasDerivAt D
    ((hasDerivAt_id D).prodMk (hasDerivAt_const D p))

private theorem cut_chart_normal_continuous {f : ℝ × Spatial → ℂ} (hf : ContDiff ℝ 1 f) :
    Continuous (cutChartNormalDerivative f) :=
  (hf.continuous_fderiv le_rfl).clm_apply continuous_const

/-- Multiplying the numerator by a fixed compact chart test, including the
coarea density, produces the uniform normal estimates used in the boundary
theorem. Both error controls are required only on the test's support. -/
theorem shell_chart_numerator_of_compact_c1_multiplier
    {test F : ℝ × Spatial → ℂ} (ht : ContDiff ℝ 1 test) (hs : HasCompactSupport test)
    (hF : ContDiff ℝ 1 F) (g : ℝ → ℝ × Spatial → ℂ)
    (hg : ∀ h > 0, ContDiff ℝ 1 (g h)) (A B : ℝ → ℝ≥0)
    (hA : ∀ h > 0, ∀ x ∈ tsupport test, ‖g h x - F x‖ ≤ (A h : ℝ))
    (hB : ∀ h > 0, ∀ x ∈ tsupport test,
      ‖fderiv ℝ (g h) x - fderiv ℝ F x‖ ≤ (B h : ℝ))
    (hA₀ : Tendsto (fun h => (A h : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hB₀ : Tendsto (fun h => (B h : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∃ n : ShellChartNumerator, n.base = (fun x => test x * F x) ∧
      ∀ h x, n.error h x = test x * (g h x - F x) := by
  let N := cutChartNormalDerivative
  let base (x : ℝ × Spatial) := test x * F x
  have hbase : ContDiff ℝ 1 base := ht.mul hF
  have hbs : HasCompactSupport base := hs.mul_right
  obtain ⟨radius, hr, hsupp⟩ := exists_normal_support_bound hs
  obtain ⟨Cbase, hCbase⟩ := hbs.exists_bound_of_continuous hbase.continuous
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hbs hbase le_rfl
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous ht.continuous
  obtain ⟨C', hC'⟩ := (hs.fderiv ℝ).exists_bound_of_continuous (ht.continuous_fderiv le_rfl)
  let c : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  let c' : ℝ≥0 := ⟨max C' 0, le_max_right _ _⟩
  have hcb (x : ℝ × Spatial) : ‖test x‖ ≤ (c : ℝ) := (hC x).trans (le_max_left _ _)
  have hn : ‖((1 : ℝ), (0 : Spatial))‖ = 1 := by simp [Prod.norm_def]
  have hc'b (x : ℝ × Spatial) : ‖N test x‖ ≤ (c' : ℝ) := by
    have hb := (fderiv ℝ test x).le_opNorm ((1 : ℝ), (0 : Spatial))
    rw [hn, mul_one] at hb
    exact hb.trans ((hC' x).trans (le_max_left _ _))
  have hNb {h : ℝ} (hh : 0 < h) {x : ℝ × Spatial} (hx : x ∈ tsupport test) :
      ‖N (g h) x - N F x‖ ≤ (B h : ℝ) := by
    have hb := (fderiv ℝ (g h) x - fderiv ℝ F x).le_opNorm ((1 : ℝ), (0 : Spatial))
    rw [hn, mul_one, ContinuousLinearMap.sub_apply] at hb
    exact hb.trans (hB h hh x hx)
  have hC₀ : Tendsto (fun h => (c : ℝ) * (A h : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using hA₀.const_mul (c : ℝ)
  have hD₀ : Tendsto (fun h => ((c' * A h + c * B h : ℝ≥0) : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [NNReal.coe_add, NNReal.coe_mul, mul_zero, zero_add] using
      (hA₀.const_mul (c' : ℝ)).add (hB₀.const_mul (c : ℝ))
  refine ⟨{
    radius := radius
    radius_pos := hr
    base := base
    base_continuous := hbase.continuous
    baseBound := Cbase
    base_norm := hCbase
    baseLip := L
    base_lipschitz := ?_
    base_support := ?_
    error := fun h x => test x * (g h x - F x)
    errorDeriv := fun h x => N test x * (g h x - F x) + test x * (N (g h) x - N F x)
    error_continuous := fun h hh => ht.continuous.mul ((hg h hh).continuous.sub hF.continuous)
    errorDeriv_continuous := fun h hh =>
      ((cut_chart_normal_continuous ht).mul ((hg h hh).continuous.sub hF.continuous)).add
        (ht.continuous.mul ((cut_chart_normal_continuous (hg h hh)).sub
          (cut_chart_normal_continuous hF)))
    error_hasDerivAt := ?_
    errorBound := fun h => (c : ℝ) * (A h : ℝ)
    errorDerivBound := fun h => c' * A h + c * B h
    error_norm := ?_
    errorDeriv_norm := ?_
    error_support := ?_
    error_bound_zero := hC₀
    errorDeriv_bound_zero := hD₀
  }, rfl, fun _ _ => rfl⟩
  · intro p
    have hslice : LipschitzWith 1 (fun y : ℝ => (y, p)) := by
      apply LipschitzWith.of_dist_le_mul
      intro y z
      simp [Prod.dist_eq]
    simpa only [mul_one] using hL.comp hslice
  · intro D p hD
    simp [base, hsupp D p hD]
  · intro h hh D p
    convert (cut_chart_normal_hasDerivAt ht D p).mul
      ((cut_chart_normal_hasDerivAt (hg h hh) D p).sub (cut_chart_normal_hasDerivAt hF D p)) using 1
  · intro h hh x
    by_cases hx : x ∈ tsupport test
    · rw [norm_mul]
      exact mul_le_mul (hcb x) (hA h hh x hx) (norm_nonneg _) c.coe_nonneg
    · simp [image_eq_zero_of_notMem_tsupport hx, mul_nonneg]
  · intro h hh x
    by_cases hx : x ∈ tsupport test
    · refine (norm_add_le _ _).trans ?_
      simp only [NNReal.coe_add, NNReal.coe_mul, norm_mul]
      exact add_le_add
        (mul_le_mul (hc'b x) (hA h hh x hx) (norm_nonneg _) c'.coe_nonneg)
        (mul_le_mul (hcb x) (hNb hh hx) (norm_nonneg _) c.coe_nonneg)
    · have hzero : N test x = 0 := by simp [N, cutChartNormalDerivative,
        fderiv_of_notMem_tsupport ℝ hx]
      simp only [hzero, image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_add, norm_zero]
      exact (c' * A h + c * B h).coe_nonneg
  · intro h _ D p hD
    simp [hsupp D p hD]

variable {E : Type*} [NormedAddCommGroup E]

/-- The coefficient limit for an unabsorbed C¹ numerator and compact chart
test. The directed algebra product is integrated before its first character
is extracted, and it uses the positive norm of the vectorial displacement. -/
theorem Plane.cut_directed_compact_c1_coefficient_limit (diamond : Plane E) (ε : Evolution)
    (ν : Measure Spatial) [IsFiniteMeasure ν]
    {test F : ℝ × Spatial → ℂ} (ht : ContDiff ℝ 1 test) (hs : HasCompactSupport test)
    (hF : ContDiff ℝ 1 F) (g : ℝ → ℝ × Spatial → ℂ)
    (hg : ∀ h > 0, ContDiff ℝ 1 (g h)) (A B : ℝ → ℝ≥0)
    (hA : ∀ h > 0, ∀ x ∈ tsupport test, ‖g h x - F x‖ ≤ (A h : ℝ))
    (hB : ∀ h > 0, ∀ x ∈ tsupport test,
      ‖fderiv ℝ (g h) x - fderiv ℝ F x‖ ≤ (B h : ℝ))
    (hA₀ : Tendsto (fun h => (A h : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hB₀ : Tendsto (fun h => (B h : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun h : Height => (quotientCharacterEquiv
      (∫ x : ℝ × Spatial, directed (test x * g h x) * diamond.poleInverse ε h x.1
        ∂(volume.prod ν))).1) poleBoundaryHeights
      (𝓝 (complexShellPV (transverseTest ν (fun x => test x * F x)) -
        Complex.I * (diamond.eta ε : ℂ) * ((Real.pi : ℂ) *
          transverseTest ν (fun x => test x * F x) 0))) := by
  obtain ⟨n, hn, he⟩ := shell_chart_numerator_of_compact_c1_multiplier ht hs hF g hg A B hA hB hA₀ hB₀
  rw [← hn]
  apply (diamond.cut_directed_coefficient_extraction ε ν n).congr
  intro h
  rw [Plane.cutDirectedChartPairing]
  congr 2
  apply integral_congr_ae
  refine Eventually.of_forall fun x => ?_
  dsimp only
  rw [hn, he]
  congr 2
  ring

end UV.SectorPlane
