import UV.AdvanceConeAngularJet

/-! The normal Taylor bounds follow from ordinary Cartesian C² tests.
The axial and spatial square roots are differentiated only in the regular
interior chart, and the angular averages retain their exact measures. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Real Set Filter
open scoped Topology

private def coneNormalPoint (a : ℝ) (p : ConeNormalVariables) : ℝ × Spatial :=
  (a * coneAxialCoordinate p.2.1, coneSpatialCoordinate p.2.1 • p.2.2)

private theorem cone_normal_point_continuous (a : ℝ) : Continuous (coneNormalPoint a) := by
  unfold coneNormalPoint coneAxialCoordinate coneSpatialCoordinate
  fun_prop

private theorem cone_normal_point_contDiffOn (a : ℝ) :
    ContDiffOn ℝ 2 (coneNormalPoint a) coneNormalStrip := by
  have hU : ContDiffOn ℝ 2 (fun p : ConeNormalVariables => p.2.1) coneNormalStrip :=
    (contDiff_fst.comp contDiff_snd).contDiffOn
  have hx : ContDiffOn ℝ 2 (fun p : ConeNormalVariables => coneAxialCoordinate p.2.1)
      coneNormalStrip := by
    unfold coneAxialCoordinate
    refine ((contDiffOn_const.add hU).div_const 2).sqrt fun p hp => ?_
    have hp' : -1 < p.2.1 := hp.1
    linarith
  have hz : ContDiffOn ℝ 2 (fun p : ConeNormalVariables => coneSpatialCoordinate p.2.1)
      coneNormalStrip := by
    unfold coneSpatialCoordinate
    refine ((contDiffOn_const.sub hU).div_const 2).sqrt fun p hp => ?_
    have hp' : p.2.1 < 1 := hp.2
    linarith
  exact (contDiffOn_const.mul hx).prodMk (hz.smul (contDiff_snd.comp contDiff_snd).contDiffOn)

private def coneScaledTest (f : ℝ × Spatial → ℂ) (a : ℝ) (p : ConeNormalVariables) : ℂ :=
  f (p.1 • coneNormalPoint a p)

private theorem cone_scaled_test_continuous {f : ℝ × Spatial → ℂ} (hf : Continuous f) (a : ℝ) :
    Continuous (coneScaledTest f a) :=
  hf.comp (continuous_fst.smul (cone_normal_point_continuous a))

private theorem cone_scaled_test_contDiffOn {f : ℝ × Spatial → ℂ} (hf : ContDiff ℝ 2 f) (a : ℝ) :
    ContDiffOn ℝ 2 (coneScaledTest f a) coneNormalStrip :=
  hf.comp_contDiffOn (contDiffOn_fst.smul (cone_normal_point_contDiffOn a))

private def coneScaledQuadraticTest (L M : (ℝ × Spatial) →L[ℝ] ℝ)
    (f : ℝ × Spatial → ℂ) (a : ℝ) (p : ConeNormalVariables) : ℂ :=
  (L (coneNormalPoint a p) * M (coneNormalPoint a p)) • coneScaledTest f a p

private theorem cone_scaled_quadratic_continuous {f : ℝ × Spatial → ℂ}
    (hf : Continuous f) (L M : (ℝ × Spatial) →L[ℝ] ℝ) (a : ℝ) :
    Continuous (coneScaledQuadraticTest L M f a) := by
  have hp := cone_normal_point_continuous a
  exact ((L.continuous.comp hp).mul (M.continuous.comp hp)).smul
    (cone_scaled_test_continuous hf a)

private theorem cone_scaled_quadratic_contDiffOn {f : ℝ × Spatial → ℂ}
    (hf : ContDiff ℝ 2 f) (L M : (ℝ × Spatial) →L[ℝ] ℝ) (a : ℝ) :
    ContDiffOn ℝ 2 (coneScaledQuadraticTest L M f a) coneNormalStrip := by
  have hp := cone_normal_point_contDiffOn a
  exact ((L.contDiff.comp_contDiffOn hp).mul (M.contDiff.comp_contDiffOn hp)).smul
    (cone_scaled_test_contDiffOn hf a)

private def coneNormalAverage (F : ℝ → ConeNormalVariables → ℂ) (r u : ℝ) : ℂ :=
  (4 * π)⁻¹ • ∫ ω : ConeSpatialSphere,
    (F 1 (r, (u, (ω : Spatial))) + F (-1) (r, (u, (ω : Spatial)))) / 2
    ∂coneSpatialSphereMeasure

private theorem cone_sphere_integrable {f : ConeSpatialSphere → ℂ} (hf : Continuous f) :
    Integrable f coneSpatialSphereMeasure := by
  letI : CompactSpace ConeSpatialSphere := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem cone_normal_average_eq_amplitude {f : ℝ × Spatial → ℂ}
    (hf : Continuous f) (r u : ℝ) :
    coneNormalAverage (coneScaledTest f) r u = coneAngularAmplitude f r u := by
  let B₁ (ω : ConeSpatialSphere) := f (r * coneAxialCoordinate u, (r * coneSpatialCoordinate u) • ω.val)
  let B₂ (ω : ConeSpatialSphere) := f (-(r * coneAxialCoordinate u), (r * coneSpatialCoordinate u) • ω.val)
  have h₁ : Continuous B₁ := by
    unfold B₁
    fun_prop
  have h₂ : Continuous B₂ := by
    unfold B₂
    fun_prop
  have hplus (ω : ConeSpatialSphere) : coneScaledTest f 1 (r, (u, ω.val)) = B₁ ω := by
    simp [coneScaledTest, coneNormalPoint, B₁, Prod.smul_mk, smul_smul]
  have hminus (ω : ConeSpatialSphere) : coneScaledTest f (-1) (r, (u, ω.val)) = B₂ ω := by
    simp [coneScaledTest, coneNormalPoint, B₂, Prod.smul_mk, smul_smul]
  unfold coneNormalAverage
  simp_rw [hplus, hminus, integral_div, integral_add (cone_sphere_integrable h₁)
    (cone_sphere_integrable h₂)]
  unfold coneAngularAmplitude coneAxialMean coneSpatialMean
  simp only [Complex.real_smul, B₁, B₂]
  ring

private theorem cone_normal_average_eq_quadratic_amplitude {f : ℝ × Spatial → ℂ}
    (hf : Continuous f) (L M : (ℝ × Spatial) →L[ℝ] ℝ) {r : ℝ} (hr : 0 < r) (u : ℝ) :
    coneNormalAverage (coneScaledQuadraticTest L M f) r u =
      coneQuadraticAngularAmplitude (fun q => (L q * M q) • f q) r u := by
  have h := cone_normal_average_eq_amplitude
    ((L.continuous.mul M.continuous).smul hf : Continuous (fun q => (L q * M q) • f q)) r u
  unfold coneQuadraticAngularAmplitude
  rw [← h, coneNormalAverage, coneNormalAverage, smul_smul]
  have hscale (a : ℝ) (ω : ConeSpatialSphere) :
      coneScaledTest (fun q => (L q * M q) • f q) a (r, (u, ω.val)) =
        r ^ 2 • coneScaledQuadraticTest L M f a (r, (u, ω.val)) := by
    simp only [coneScaledTest, coneScaledQuadraticTest, map_smul, smul_eq_mul,
      smul_smul]
    congr 1
    ring
  simp_rw [hscale, ← smul_add]
  have hdiv (x : ℂ) : (r ^ 2 • x) / 2 = r ^ 2 • (x / 2) := by
    simp only [Complex.real_smul]
    ring
  simp_rw [hdiv, integral_smul, smul_smul]
  congr 1
  field_simp [hr.ne']

private theorem cone_normal_average_norm_bound
    {F : ℝ → ConeNormalVariables → ℂ} {r u C : ℝ}
    (h₁ : ∀ ω : ConeSpatialSphere, ‖F 1 (r, (u, ω.val))‖ ≤ C)
    (h₂ : ∀ ω : ConeSpatialSphere, ‖F (-1) (r, (u, ω.val))‖ ≤ C) :
    ‖coneNormalAverage F r u‖ ≤ C := by
  unfold coneNormalAverage
  rw [norm_smul, norm_inv, Real.norm_of_nonneg (by positivity : 0 ≤ 4 * π)]
  have hI : ‖∫ ω : ConeSpatialSphere,
        (F 1 (r, (u, ω.val)) + F (-1) (r, (u, ω.val))) / 2 ∂coneSpatialSphereMeasure‖ ≤
      C * (4 * π) := by
    rw [← cone_spatial_sphere_area]
    apply norm_integral_le_of_norm_le_const
    refine Eventually.of_forall fun ω => ?_
    rw [norm_div, Complex.norm_ofNat, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact (norm_add_le _ _).trans (by linarith only [h₁ ω, h₂ ω])
  calc
    _ ≤ (4 * π)⁻¹ * (C * (4 * π)) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by field_simp [pi_ne_zero]

private theorem cone_normal_average_jet {F : ℝ → ConeNormalVariables → ℂ}
    (hC : ∀ a, Continuous (F a)) (hD : ∀ a, ContDiffOn ℝ 2 (F a) coneNormalStrip)
    (R : ℝ) :
    ∃ d : ℝ → ℂ, ∃ C ≥ 0, ∀ r ∈ Icc (0 : ℝ) R,
      ‖coneNormalAverage F r 0‖ ≤ C ∧ ‖d r‖ ≤ C ∧
      ∀ u ∈ Icc (-1 : ℝ) 1,
        ‖coneNormalAverage F r u - coneNormalAverage F r 0 - (u : ℂ) * d r‖ ≤ C * |u| ^ 2 := by
  let D (a : ℝ) := coneNormalDerivative (F a)
  let d (r : ℝ) := coneNormalAverage D r 0
  obtain ⟨m₁, hm₁, h₁⟩ := cone_uniform_normal_jet (hC 1) (hD 1) R
  obtain ⟨m₂, hm₂, h₂⟩ := cone_uniform_normal_jet (hC (-1)) (hD (-1)) R
  let C := max m₁ m₂
  have hC₀ : 0 ≤ C := hm₁.trans (le_max_left _ _)
  refine ⟨d, C, hC₀, ?_⟩
  intro r hr
  constructor
  · exact cone_normal_average_norm_bound
      (fun ω => (h₁ r hr ω).1.trans (le_max_left _ _))
      (fun ω => (h₂ r hr ω).1.trans (le_max_right _ _))
  constructor
  · exact cone_normal_average_norm_bound
      (fun ω => (h₁ r hr ω).2.1.trans (le_max_left _ _))
      (fun ω => (h₂ r hr ω).2.1.trans (le_max_right _ _))
  intro u hu
  let J (a : ℝ) (q : ConeNormalVariables) :=
    F a q - F a (q.1, (0, q.2.2)) - (q.2.1 : ℂ) * D a (q.1, (0, q.2.2))
  have hEq : coneNormalAverage J r u =
      coneNormalAverage F r u - coneNormalAverage F r 0 - (u : ℂ) * d r := by
    let Avg (v : ℝ) (ω : ConeSpatialSphere) :=
      (F 1 (r, (v, ω.val)) + F (-1) (r, (v, ω.val))) / 2
    let Jet (ω : ConeSpatialSphere) :=
      (D 1 (r, (0, ω.val)) + D (-1) (r, (0, ω.val))) / 2
    have hA (v : ℝ) : Continuous (Avg v) := by
      have hmap : Continuous (fun ω : ConeSpatialSphere => (r, (v, ω.val))) := by fun_prop
      exact (((hC 1).comp hmap).add ((hC (-1)).comp hmap)).div_const 2
    have hJ (a : ℝ) : Continuous (fun ω : ConeSpatialSphere => D a (r, (0, ω.val))) := by
      have hd : ContinuousOn (D a) coneNormalStrip :=
        ((hD a).continuousOn_fderiv_of_isOpen cone_normal_strip_isOpen (by norm_num)).clm_apply
          continuousOn_const
      apply hd.comp_continuous (by fun_prop)
      intro ω
      change (0 : ℝ) ∈ Ioo (-1) 1
      norm_num
    have hJi : Integrable Jet coneSpatialSphereMeasure :=
      cone_sphere_integrable (((hJ 1).add (hJ (-1))).div_const 2)
    have hin (ω : ConeSpatialSphere) :
        (J 1 (r, (u, ω.val)) + J (-1) (r, (u, ω.val))) / 2 =
          Avg u ω - Avg 0 ω - (u : ℂ) * Jet ω := by
      unfold J Avg Jet
      dsimp only
      ring
    unfold coneNormalAverage
    simp_rw [hin]
    have hSub : Integrable (fun ω => Avg u ω - Avg 0 ω) coneSpatialSphereMeasure :=
      (cone_sphere_integrable (hA u)).sub (cone_sphere_integrable (hA 0))
    have hMul : Integrable (fun ω => (u : ℂ) * Jet ω) coneSpatialSphereMeasure :=
      hJi.const_mul _
    rw [integral_sub hSub hMul,
      integral_sub (cone_sphere_integrable (hA u)) (cone_sphere_integrable (hA 0)),
      integral_const_mul]
    unfold d coneNormalAverage
    simp only [Complex.real_smul, Avg, Jet]
    ring
  rw [← hEq]
  exact cone_normal_average_norm_bound
    (fun ω => ((h₁ r hr ω).2.2 u hu).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)))
    (fun ω => ((h₂ r hr ω).2.2 u hu).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)))

/-- Ordinary Cartesian C² tests automatically supply the uniform normal
jets for the square with the literal product of two linear coordinates. -/
theorem cone_smooth_quadratic_normal_jet {f : ℝ × Spatial → ℂ}
    (hf : ContDiff ℝ 2 f) (L M : (ℝ × Spatial) →L[ℝ] ℝ) (R : ℝ) :
    ∃ d : ℝ → ℂ, ∃ C ≥ 0, ∀ r ∈ Ioc (0 : ℝ) R,
      ‖coneQuadraticAngularAmplitude (fun q => (L q * M q) • f q) r 0‖ ≤ C ∧ ‖d r‖ ≤ C ∧
      ∀ u ∈ Icc (-1 : ℝ) 1,
        ‖coneQuadraticAngularAmplitude (fun q => (L q * M q) • f q) r u -
          coneQuadraticAngularAmplitude (fun q => (L q * M q) • f q) r 0 -
          (u : ℂ) * d r‖ ≤ C * |u| ^ 2 := by
  obtain ⟨d, C, hC, h⟩ := cone_normal_average_jet
    (cone_scaled_quadratic_continuous hf.continuous L M)
    (cone_scaled_quadratic_contDiffOn hf L M) R
  refine ⟨d, C, hC, fun r hr => ?_⟩
  simpa only [cone_normal_average_eq_quadratic_amplitude hf.continuous L M hr.1]
    using h r ⟨hr.1.le, hr.2⟩

/-- A Cartesian C² single-line test supplies the first normal remainder and
uniform value bounds needed by the full nonradial single-pole limit. -/
theorem cone_smooth_single_normal_jet {f : ℝ × Spatial → ℂ}
    (hf : ContDiff ℝ 2 f) (R : ℝ) :
    ∃ C ≥ 0, ∀ r ∈ Ioc (0 : ℝ) R,
      ‖coneAngularAmplitude f r 0‖ ≤ C ∧ ∀ u ∈ Icc (-1 : ℝ) 1,
        ‖coneAngularAmplitude f r u - coneAngularAmplitude f r 0‖ ≤ C * |u| := by
  obtain ⟨d, C, hC, h⟩ := cone_normal_average_jet
    (cone_scaled_test_continuous hf.continuous)
    (cone_scaled_test_contDiffOn hf) R
  simp_rw [cone_normal_average_eq_amplitude hf.continuous] at h
  refine ⟨2 * C, by positivity, ?_⟩
  intro r hr
  obtain ⟨hv, hd, hR⟩ := h r ⟨hr.1.le, hr.2⟩
  refine ⟨hv.trans (by linarith), fun u hu => ?_⟩
  have hEq : coneAngularAmplitude f r u - coneAngularAmplitude f r 0 =
      (coneAngularAmplitude f r u - coneAngularAmplitude f r 0 - (u : ℂ) * d r) +
        (u : ℂ) * d r := by ring
  rw [hEq]
  apply (norm_add_le _ _).trans
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have ha : |u| ≤ 1 := abs_le.mpr hu
  have hsq : |u| ^ 2 ≤ |u| := by nlinarith [mul_le_mul_of_nonneg_right ha (abs_nonneg u)]
  have h1 := mul_le_mul_of_nonneg_left hsq hC
  have h2 := mul_le_mul_of_nonneg_left hd (abs_nonneg u)
  linarith only [hR u hu, h1, h2]


theorem cone_radial_cutoff_of_compact {f : ℝ × Spatial → ℂ} (hs : HasCompactSupport f) :
    ∃ R > (0 : ℝ), ∀ q, R < coneEuclideanRadius q → f q = 0 := by
  have hC : Continuous coneEuclideanRadius :=
    continuous_sqrt.comp ((continuous_fst.pow 2).add ((continuous_norm.comp continuous_snd).pow 2))
  have hS : IsCompact (tsupport f) := hs
  obtain ⟨R, hR⟩ := hS.exists_bound_of_continuousOn hC.continuousOn
  refine ⟨max 1 R, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro q hq
  by_contra hn
  have h := hR q (subset_tsupport f hn)
  have hq₀ : 0 ≤ coneEuclideanRadius q := sqrt_nonneg _
  rw [Real.norm_of_nonneg hq₀] at h
  exact (not_le_of_gt hq) (h.trans (le_max_right _ _))

variable {E : Type*} [NormedAddCommGroup E]

/-- The scalar first pole has a finite boundary pairing on any compact
Cartesian C² test, with neither angular sheet omitted. -/
theorem Plane.cone_nonradial_smooth_single_limit (diamond : Plane E) (ε : Evolution)
    {f : ℝ × Spatial → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    ∃ z : ℂ, Tendsto (fun h : Height => ∫ q : ℝ × Spatial,
      f q * diamond.poleCoefficient ε h (shellSquare q.1 q.2))
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))) (𝓝 z) := by
  obtain ⟨R, hR, hcut⟩ := cone_radial_cutoff_of_compact hs
  obtain ⟨C, hC, hjet⟩ := cone_smooth_single_normal_jet hf R
  exact ⟨_, diamond.cone_nonradial_single_limit ε hf.continuous hs hR hcut hC hjet⟩

/-- The unweighted longitudinal square, with the actual Cartesian
quadratic numerator, has a finite pairing on every compact C² test. -/
theorem Plane.cone_nonradial_smooth_longitudinal_limit (diamond : Plane E) (ε : Evolution)
    {f : ℝ × Spatial → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)
    (L M : (ℝ × Spatial) →L[ℝ] ℝ) :
    ∃ z : ℂ, Tendsto (fun h : Height => ∫ q : ℝ × Spatial,
      ((L q * M q) • f q) * diamond.poleCoefficient ε h (shellSquare q.1 q.2) ^ 2)
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))) (𝓝 z) := by
  have hct : Continuous (fun q => (L q * M q) • f q) :=
    (L.continuous.mul M.continuous).smul hf.continuous
  have hst : HasCompactSupport (fun q => (L q * M q) • f q) := hs.smul_left
  obtain ⟨R, hR, hcut⟩ := cone_radial_cutoff_of_compact hst
  obtain ⟨d, C, hC, hjet⟩ := cone_smooth_quadratic_normal_jet hf L M R
  exact ⟨_, diamond.cone_nonradial_quadratic_limit ε hct hst hR hcut d hC hjet⟩

end UV.SectorPlane
