import UV.ExtendRunningAngularReflection

/-! Uniform jets of the signed normal profile. The derivatives act on the
original smooth test evaluated on each unit direction of the cone chart. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Real Set
open scoped Topology

private def coneRunningPoint (p : ConeNormalVariables) : ℝ × Spatial :=
  (coneAxialCoordinate p.2.1, coneSpatialCoordinate p.2.1 • p.2.2)

private theorem cone_running_point_continuous : Continuous coneRunningPoint := by
  unfold coneRunningPoint coneAxialCoordinate coneSpatialCoordinate
  fun_prop

private theorem cone_running_point_contDiffOn :
    ContDiffOn ℝ 2 coneRunningPoint coneNormalStrip := by
  have hu : ContDiffOn ℝ 2 (fun p : ConeNormalVariables => p.2.1) coneNormalStrip :=
    (contDiff_fst.comp contDiff_snd).contDiffOn
  have hx : ContDiffOn ℝ 2 (fun p : ConeNormalVariables => coneAxialCoordinate p.2.1)
      coneNormalStrip := by
    unfold coneAxialCoordinate
    refine ((contDiffOn_const.add hu).div_const 2).sqrt fun p hp => ?_
    have hp' : -1 < p.2.1 := hp.1
    linarith
  have hp : ContDiffOn ℝ 2 (fun p : ConeNormalVariables => coneSpatialCoordinate p.2.1)
      coneNormalStrip := by
    unfold coneSpatialCoordinate
    refine ((contDiffOn_const.sub hu).div_const 2).sqrt fun p hp => ?_
    have hp' : p.2.1 < 1 := hp.2
    linarith
  exact hx.prodMk (hp.smul (contDiff_snd.comp contDiff_snd).contDiffOn)

private def coneRunningBranchField (F : ConeNormalVariables → ℂ) (p : ConeNormalVariables) : ℂ :=
  (F (p.1, coneRunningPoint p) - F (p.1, coneAxialReflection (coneRunningPoint p))) / 2

private theorem cone_running_branch_field_continuous {F : ConeNormalVariables → ℂ}
    (hf : Continuous F) : Continuous (coneRunningBranchField F) := by
  exact ((hf.comp (continuous_fst.prodMk cone_running_point_continuous)).sub
    (hf.comp (continuous_fst.prodMk
      (cone_axial_reflection_continuous.comp cone_running_point_continuous)))).div_const 2

private theorem cone_running_branch_field_contDiffOn {F : ConeNormalVariables → ℂ}
    (hf : ContDiff ℝ 2 F) : ContDiffOn ℝ 2 (coneRunningBranchField F) coneNormalStrip := by
  exact ((hf.comp_contDiffOn (contDiffOn_fst.prodMk cone_running_point_contDiffOn)).sub
    (hf.comp_contDiffOn (contDiffOn_fst.prodMk
      (cone_axial_reflection_contDiff.comp_contDiffOn cone_running_point_contDiffOn)))).div_const 2

private def coneRunningMean (F : ConeNormalVariables → ℂ) (r u : ℝ) : ℂ :=
  (4 * π)⁻¹ • ∫ ω : ConeSpatialSphere, F (r, (u, ω.val)) ∂coneSpatialSphereMeasure

private theorem cone_running_sphere_integrable {f : ConeSpatialSphere → ℂ} (hf : Continuous f) :
    Integrable f coneSpatialSphereMeasure := by
  letI : CompactSpace ConeSpatialSphere := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem cone_running_mean_norm_le {F : ConeNormalVariables → ℂ} {r u C : ℝ}
    (h : ∀ ω : ConeSpatialSphere, ‖F (r, (u, ω.val))‖ ≤ C) :
    ‖coneRunningMean F r u‖ ≤ C := by
  unfold coneRunningMean
  rw [norm_smul, norm_inv, Real.norm_of_nonneg (by positivity : 0 ≤ 4 * π)]
  calc
    _ ≤ (4 * π)⁻¹ * (C * coneSpatialSphereMeasure.real univ) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le_const (Eventually.of_forall h))
        (by positivity)
    _ = _ := by rw [cone_spatial_sphere_area]; field_simp [pi_ne_zero]

private theorem cone_running_mean_jet {F : ConeNormalVariables → ℂ}
    (hC : Continuous F) (hD : ContDiffOn ℝ 2 F coneNormalStrip) (R : ℝ) :
    ∃ d : ℝ → ℂ, ∃ C ≥ 0, ∀ r ∈ Icc (0 : ℝ) R,
      ‖coneRunningMean F r 0‖ ≤ C ∧ ‖d r‖ ≤ C ∧
      ∀ u ∈ Icc (-1 : ℝ) 1,
        ‖coneRunningMean F r u - coneRunningMean F r 0 - (u : ℂ) * d r‖ ≤ C * |u| ^ 2 := by
  let D := coneNormalDerivative F
  let d (r : ℝ) := coneRunningMean D r 0
  obtain ⟨C, hC₀, h⟩ := cone_uniform_normal_jet hC hD R
  refine ⟨d, C, hC₀, fun r hr => ⟨?_, ?_, ?_⟩⟩
  · exact cone_running_mean_norm_le (fun ω => (h r hr ω).1)
  · exact cone_running_mean_norm_le (fun ω => (h r hr ω).2.1)
  · intro u hu
    let J (q : ConeNormalVariables) :=
      F q - F (q.1, (0, q.2.2)) - (q.2.1 : ℂ) * D (q.1, (0, q.2.2))
    have hiF (v : ℝ) : Integrable (fun ω : ConeSpatialSphere => F (r, (v, ω.val)))
        coneSpatialSphereMeasure :=
      cone_running_sphere_integrable (hC.comp (by fun_prop))
    have hiD : Integrable (fun ω : ConeSpatialSphere => D (r, (0, ω.val)))
        coneSpatialSphereMeasure := by
      have hd : ContinuousOn D coneNormalStrip :=
        (hD.continuousOn_fderiv_of_isOpen cone_normal_strip_isOpen (by norm_num)).clm_apply
          continuousOn_const
      apply cone_running_sphere_integrable
      apply hd.comp_continuous (by fun_prop)
      intro ω
      change (0 : ℝ) ∈ Ioo (-1) 1
      norm_num
    have hEq : coneRunningMean J r u =
        coneRunningMean F r u - coneRunningMean F r 0 - (u : ℂ) * d r := by
      have hSub : Integrable (fun ω : ConeSpatialSphere => F (r, (u, ω.val)) - F (r, (0, ω.val)))
          coneSpatialSphereMeasure := (hiF u).sub (hiF 0)
      have hMul : Integrable (fun ω : ConeSpatialSphere => (u : ℂ) * D (r, (0, ω.val)))
          coneSpatialSphereMeasure := hiD.const_mul _
      unfold d coneRunningMean J
      dsimp only
      rw [integral_sub hSub hMul, integral_sub (hiF u) (hiF 0), integral_const_mul]
      simp only [Complex.real_smul]
      ring
    rw [← hEq]
    exact cone_running_mean_norm_le (fun ω => (h r hr ω).2.2 u hu)

private def coneRunningScaledTest (f : ℝ × Spatial → ℂ) (q : ConeNormalVariables) : ℂ :=
  f (q.1 • q.2)

private def coneRunningScaledQuadratic (L M : (ℝ × Spatial) →L[ℝ] ℝ)
    (f : ℝ × Spatial → ℂ) (q : ConeNormalVariables) : ℂ :=
  (L q.2 * M q.2) • coneRunningScaledTest f q

private theorem cone_running_scaled_test_contDiff {f : ℝ × Spatial → ℂ}
    (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 (coneRunningScaledTest f) :=
  hf.comp (contDiff_fst.smul contDiff_snd)

private theorem cone_running_scaled_quadratic_contDiff {f : ℝ × Spatial → ℂ}
    (hf : ContDiff ℝ 2 f) (L M : (ℝ × Spatial) →L[ℝ] ℝ) :
    ContDiff ℝ 2 (coneRunningScaledQuadratic L M f) :=
  (((L.contDiff.comp contDiff_snd).mul (M.contDiff.comp contDiff_snd)).smul
    (cone_running_scaled_test_contDiff hf))

private theorem cone_running_mean_eq_profile {f : ℝ × Spatial → ℂ} (hf : Continuous f)
    (r u : ℝ) :
    coneRunningMean (coneRunningBranchField (coneRunningScaledTest f)) r u =
      coneRunningAngularAmplitude f r u := by
  let Fplus (ω : ConeSpatialSphere) := f (r * coneAxialCoordinate u,
    (r * coneSpatialCoordinate u) • ω.val)
  let Fminus (ω : ConeSpatialSphere) := f (-(r * coneAxialCoordinate u),
    (r * coneSpatialCoordinate u) • ω.val)
  have hFplus : Continuous Fplus := by unfold Fplus; fun_prop
  have hFminus : Continuous Fminus := by unfold Fminus; fun_prop
  have he (ω : ConeSpatialSphere) :
      coneRunningBranchField (coneRunningScaledTest f) (r, (u, ω.val)) =
        (Fplus ω - Fminus ω) / 2 := by
    simp [coneRunningBranchField, coneRunningScaledTest, coneRunningPoint,
      coneAxialReflection, Fplus, Fminus, Prod.smul_mk, smul_smul]
  unfold coneRunningMean coneRunningAngularAmplitude coneSpatialMean
  simp_rw [he, integral_div, integral_sub (cone_running_sphere_integrable hFplus)
    (cone_running_sphere_integrable hFminus)]
  simp only [Complex.real_smul, Fplus, Fminus]
  ring

/-- The running quadratic amplitude keeps the two numerator powers as
a separate radius factor. -/
def coneRunningQuadraticAngularAmplitude (f : ℝ × Spatial → ℂ) (r u : ℝ) : ℂ :=
  ((r ^ 2)⁻¹ : ℝ) • coneRunningAngularAmplitude f r u

private theorem cone_running_mean_eq_quadratic_profile {f : ℝ × Spatial → ℂ} (hf : Continuous f)
    (L M : (ℝ × Spatial) →L[ℝ] ℝ) {r : ℝ} (hr : 0 < r) (u : ℝ) :
    coneRunningMean (coneRunningBranchField (coneRunningScaledQuadratic L M f)) r u =
      coneRunningQuadraticAngularAmplitude (fun q => (L q * M q) • f q) r u := by
  have hc : Continuous (fun q => (L q * M q) • f q) :=
    (L.continuous.mul M.continuous).smul hf
  unfold coneRunningQuadraticAngularAmplitude
  rw [← cone_running_mean_eq_profile hc]
  have hpoint (ω : ConeSpatialSphere) :
      coneRunningBranchField (coneRunningScaledTest (fun q => (L q * M q) • f q))
        (r, (u, ω.val)) =
        r ^ 2 • coneRunningBranchField (coneRunningScaledQuadratic L M f)
          (r, (u, ω.val)) := by
    unfold coneRunningBranchField coneRunningScaledTest coneRunningScaledQuadratic
    simp only [map_smul, smul_eq_mul, Complex.real_smul, coneRunningScaledTest]
    push_cast
    ring
  unfold coneRunningMean
  simp_rw [hpoint, integral_smul, smul_smul]
  congr 1
  field_simp [hr.ne']

/-- Ordinary compact Cartesian C² tests supply the normal remainder for
the running sign on the simple pole by taking the true axial difference. -/
theorem cone_running_smooth_single_normal_jet {f : ℝ × Spatial → ℂ}
    (hf : ContDiff ℝ 2 f) (R : ℝ) :
    ∃ C ≥ 0, ∀ r ∈ Ioc (0 : ℝ) R,
      ‖coneRunningAngularAmplitude f r 0‖ ≤ C ∧ ∀ u ∈ Icc (-1 : ℝ) 1,
        ‖coneRunningAngularAmplitude f r u - coneRunningAngularAmplitude f r 0‖ ≤ C * |u| := by
  have hs := cone_running_scaled_test_contDiff hf
  obtain ⟨d, C, hC, h⟩ := cone_running_mean_jet
    (cone_running_branch_field_continuous hs.continuous)
    (cone_running_branch_field_contDiffOn hs) R
  simp_rw [cone_running_mean_eq_profile hf.continuous] at h
  refine ⟨2 * C, by positivity, ?_⟩
  intro r hr
  obtain ⟨hv, hd, hR⟩ := h r ⟨hr.1.le, hr.2⟩
  refine ⟨hv.trans (by linarith), fun u hu => ?_⟩
  have hEq : coneRunningAngularAmplitude f r u - coneRunningAngularAmplitude f r 0 =
      (coneRunningAngularAmplitude f r u - coneRunningAngularAmplitude f r 0 -
        (u : ℂ) * d r) + (u : ℂ) * d r := by ring
  rw [hEq]
  apply (norm_add_le _ _).trans
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hu₁ : |u| ≤ 1 := abs_le.mpr hu
  have hsq : |u| ^ 2 ≤ |u| := by nlinarith [mul_le_mul_of_nonneg_right hu₁ (abs_nonneg u)]
  have h1 := mul_le_mul_of_nonneg_left hsq hC
  have h2 := mul_le_mul_of_nonneg_left hd (abs_nonneg u)
  linarith only [hR u hu, h1, h2]

/-- The signed quadratic amplitude of the actual product of linear slots
has uniform normal value, slope and Taylor remainder bounds. -/
theorem cone_running_smooth_quadratic_normal_jet {f : ℝ × Spatial → ℂ}
    (hf : ContDiff ℝ 2 f) (L M : (ℝ × Spatial) →L[ℝ] ℝ) (R : ℝ) :
    let F := fun q => (L q * M q) • f q
    ∃ d : ℝ → ℂ, ∃ C ≥ 0, ∀ r ∈ Ioc (0 : ℝ) R,
      ‖coneRunningQuadraticAngularAmplitude F r 0‖ ≤ C ∧ ‖d r‖ ≤ C ∧
      ∀ u ∈ Icc (-1 : ℝ) 1,
        ‖coneRunningQuadraticAngularAmplitude F r u -
          coneRunningQuadraticAngularAmplitude F r 0 - (u : ℂ) * d r‖ ≤ C * |u| ^ 2 := by
  have hs := cone_running_scaled_quadratic_contDiff hf L M
  obtain ⟨d, C, hC, h⟩ := cone_running_mean_jet
    (cone_running_branch_field_continuous hs.continuous)
    (cone_running_branch_field_contDiffOn hs) R
  refine ⟨d, C, hC, fun r hr => ?_⟩
  simpa only [cone_running_mean_eq_quadratic_profile hf.continuous L M hr.1]
    using h r ⟨hr.1.le, hr.2⟩

end UV.SectorPlane
