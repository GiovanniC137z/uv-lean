import UV.AdvanceConeAngularBoundary

/-! Quantitative normal Taylor estimates for smooth test families on the
actual cone angular chart. Only a closed interior strip is differentiated. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Real Set Filter
open scoped Topology

abbrev ConeNormalVariables := ℝ × (ℝ × Spatial)

def coneNormalStrip : Set ConeNormalVariables :=
  (fun p : ConeNormalVariables => p.2.1) ⁻¹' Ioo (-1 : ℝ) 1

theorem cone_normal_strip_isOpen : IsOpen coneNormalStrip :=
  isOpen_Ioo.preimage (continuous_fst.comp continuous_snd)

def coneNormalDerivative (F : ConeNormalVariables → ℂ) (p : ConeNormalVariables) : ℂ :=
  fderiv ℝ F p (0, (1, 0))

private theorem cone_normal_derivative_hasDerivAt {F : ConeNormalVariables → ℂ}
    {r u : ℝ} {ω : Spatial} (hF : DifferentiableAt ℝ F (r, (u, ω))) :
    HasDerivAt (fun v : ℝ => F (r, (v, ω))) (coneNormalDerivative F (r, (u, ω))) u := by
  have he : HasDerivAt (fun v : ℝ => (r, (v, ω))) (0, (1, 0)) u :=
    (hasDerivAt_const u r).prodMk ((hasDerivAt_id u).prodMk (hasDerivAt_const u ω))
  exact hF.hasFDerivAt.comp_hasDerivAt u he

private theorem cone_segment_abs_le {u v : ℝ} (hv : v ∈ uIcc (0 : ℝ) u) :
    |v| ≤ |u| := by
  rcases le_or_gt 0 u with hu | hu
  · rw [uIcc_of_le hu] at hv
    simpa [abs_of_nonneg hv.1, abs_of_nonneg hu] using hv.2
  · rw [uIcc_of_ge hu.le] at hv
    simp only [abs_of_nonpos hv.2, abs_of_neg hu, neg_le_neg_iff]
    exact hv.1

set_option maxHeartbeats 400000 in
/-- A continuous family that is C² on the regular angular strip has
uniform value, first-normal-jet and quadratic remainder bounds on every
compact radial slab with norm-one spatial directions. Endpoint continuity
suffices outside the differentiable strip used to estimate the remainder. -/
theorem cone_uniform_normal_jet
    {F : ConeNormalVariables → ℂ} (hc : Continuous F) (hF : ContDiffOn ℝ 2 F coneNormalStrip)
    (R : ℝ) :
    ∃ C ≥ (0 : ℝ), ∀ r ∈ Icc (0 : ℝ) R, ∀ ω : ConeSpatialSphere,
      ‖F (r, (0, (ω : Spatial)))‖ ≤ C ∧
      ‖coneNormalDerivative F (r, (0, (ω : Spatial)))‖ ≤ C ∧
      ∀ u ∈ Icc (-1 : ℝ) 1,
        ‖F (r, (u, (ω : Spatial))) - F (r, (0, (ω : Spatial))) -
          (u : ℂ) * coneNormalDerivative F (r, (0, (ω : Spatial)))‖ ≤ C * |u| ^ 2 := by
  let D := coneNormalDerivative F
  let DD := coneNormalDerivative D
  have hDbase : ContDiffOn ℝ 1 (fderiv ℝ F) coneNormalStrip :=
    hF.fderiv_of_isOpen cone_normal_strip_isOpen (by norm_num)
  have hD : ContDiffOn ℝ 1 D coneNormalStrip :=
    hDbase.clm_apply (contDiffOn_const : ContDiffOn ℝ 1
      (fun _ : ConeNormalVariables => ((0, (1, 0)) : ConeNormalVariables)) coneNormalStrip)
  have hDDbase : ContinuousOn (fderiv ℝ D) coneNormalStrip :=
    hD.continuousOn_fderiv_of_isOpen cone_normal_strip_isOpen (by norm_num)
  have hDD : ContinuousOn DD coneNormalStrip :=
    hDDbase.clm_apply (continuousOn_const : ContinuousOn
      (fun _ : ConeNormalVariables => ((0, (1, 0)) : ConeNormalVariables)) coneNormalStrip)
  let K := Icc 0 R ×ˢ (Icc (-1 : ℝ) 1 ×ˢ Metric.sphere (0 : Spatial) 1)
  let S := Icc 0 R ×ˢ (Icc (-(1 / 2) : ℝ) (1 / 2) ×ˢ Metric.sphere (0 : Spatial) 1)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod (isCompact_sphere _ _))
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_Icc.prod (isCompact_sphere _ _))
  have hSub : S ⊆ coneNormalStrip := by
    intro q hq
    have hl : -(1 / 2) ≤ q.2.1 := hq.2.1.1
    have hu : q.2.1 ≤ 1 / 2 := hq.2.1.2
    exact ⟨by linarith, by linarith⟩
  obtain ⟨b₀, hb₀⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨b₁, hb₁⟩ := hS.exists_bound_of_continuousOn (hD.continuousOn.mono hSub)
  obtain ⟨b₂, hb₂⟩ := hS.exists_bound_of_continuousOn (hDD.mono hSub)
  let m := max 0 (max b₀ (max b₁ b₂))
  have hm : 0 ≤ m := le_max_left _ _
  have hm₀ : b₀ ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hm₁ : b₁ ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hm₂ : b₂ ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hsmall : m ≤ 12 * m := by linarith
  refine ⟨12 * m, mul_nonneg (by norm_num) hm, ?_⟩
  intro r hr ω
  let f (u : ℝ) := F (r, (u, (ω : Spatial)))
  let d (u : ℝ) := D (r, (u, (ω : Spatial)))
  let d₂ (u : ℝ) := DD (r, (u, (ω : Spatial)))
  have hfB (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) : ‖f u‖ ≤ m :=
    (hb₀ (r, (u, ω.val)) ⟨hr, hu, ω.property⟩).trans hm₀
  have hdB (u : ℝ) (hu : u ∈ Icc (-(1 / 2) : ℝ) (1 / 2)) : ‖d u‖ ≤ m :=
    (hb₁ (r, (u, ω.val)) ⟨hr, hu, ω.property⟩).trans hm₁
  have hD2B (u : ℝ) (hu : u ∈ Icc (-(1 / 2) : ℝ) (1 / 2)) : ‖d₂ u‖ ≤ m :=
    (hb₂ (r, (u, ω.val)) ⟨hr, hu, ω.property⟩).trans hm₂
  have h0 : (0 : ℝ) ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := by norm_num
  have hd0 : ‖d 0‖ ≤ m := hdB 0 h0
  have hf0 : ‖f 0‖ ≤ m := hfB 0 (by norm_num)
  refine ⟨hf0.trans hsmall, hd0.trans hsmall, ?_⟩
  intro u hu
  change ‖f u - f 0 - (u : ℂ) * d 0‖ ≤ 12 * m * |u| ^ 2
  by_cases hu₁ : |u| ≤ 1 / 2
  · let I := Icc (-(1 / 2) : ℝ) (1 / 2)
    have hstrip (v : ℝ) (hv : v ∈ I) : (r, (v, (ω : Spatial))) ∈ coneNormalStrip :=
      hSub ⟨hr, hv, ω.property⟩
    have hder (v : ℝ) (hv : v ∈ I) : HasDerivAt f (d v) v :=
      cone_normal_derivative_hasDerivAt
        ((hF.differentiableOn (by norm_num) _ (hstrip v hv)).differentiableAt
          (cone_normal_strip_isOpen.mem_nhds (hstrip v hv)))
    have hder₂ (v : ℝ) (hv : v ∈ I) : HasDerivAt d (d₂ v) v :=
      cone_normal_derivative_hasDerivAt
        ((hD.differentiableOn (by norm_num) _ (hstrip v hv)).differentiableAt
          (cone_normal_strip_isOpen.mem_nhds (hstrip v hv)))
    have hDnorm (v : ℝ) (hv : v ∈ uIcc 0 u) : ‖d v - d 0‖ ≤ m * |u| := by
      have hvAbs := cone_segment_abs_le hv
      have hi : v ∈ I := abs_le.mp (hvAbs.trans hu₁)
      have h := (convex_Icc _ _).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun v hv => (hder₂ v hv).hasDerivWithinAt) hD2B h0 hi
      have hh : ‖d v - d 0‖ ≤ m * |v| := by
        simpa only [sub_zero, Real.norm_eq_abs] using h
      exact hh.trans (mul_le_mul_of_nonneg_left hvAbs hm)
    have hderR (v : ℝ) (hv : v ∈ uIcc 0 u) :
        HasDerivWithinAt (fun x : ℝ => f x - (x : ℂ) * d 0) (d v - d 0) (uIcc 0 u) v := by
      have hi : v ∈ I := abs_le.mp ((cone_segment_abs_le hv).trans hu₁)
      exact ((hder v hi).sub (by simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using
        (Complex.ofRealCLM.hasDerivAt (x := v)).mul_const (d 0))).hasDerivWithinAt
    have h := (convex_uIcc (0 : ℝ) u).norm_image_sub_le_of_norm_hasDerivWithin_le
      hderR hDnorm left_mem_uIcc right_mem_uIcc
    simp only [Complex.ofReal_zero, zero_mul, sub_zero, Real.norm_eq_abs] at h
    have ht : f u - (u : ℂ) * d 0 - f 0 = f u - f 0 - (u : ℂ) * d 0 := by ring
    rw [ht] at h
    refine h.trans ?_
    have hp := mul_le_mul_of_nonneg_right hsmall (sq_nonneg |u|)
    nlinarith only [hp]
  · have huAbs : |u| ≤ 1 := abs_le.mpr hu
    have hb : ‖(u : ℂ) * d 0‖ ≤ m := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul huAbs hd0 (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    have hSum : ‖f u - f 0 - (u : ℂ) * d 0‖ ≤ 3 * m :=
      (norm_sub_le _ _).trans (by linarith only [norm_sub_le (f u) (f 0), hfB u hu, hf0, hb])
    refine hSum.trans ?_
    have hsquare : (1 / 2 : ℝ) ^ 2 ≤ |u| ^ 2 :=
      (sq_le_sq₀ (by norm_num) (abs_nonneg _)).mpr (le_of_not_ge hu₁)
    nlinarith only [mul_le_mul_of_nonneg_left hsquare hm]

end UV.SectorPlane
