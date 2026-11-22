import UV.AdvanceConeAngularCartesian

/-! The radial boundary limit for the actual Cartesian pairing, under
uniform normal estimates of its spatially and axially averaged test. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Real Set
open scoped Interval Topology

def coneAngularSingleBoundary (η : ℝ) (g : ℝ → ℂ) : ℂ :=
  g 0 * (-1 - Complex.I * (η : ℂ)) +
    ∫ θ in (0 : ℝ)..π, coneAngularWeight θ •
      ((g (cos θ) - g 0) * (cos θ : ℂ)⁻¹)

def coneAngularSquareBoundary (η : ℝ) (g : ℝ → ℂ) (d : ℂ) : ℂ :=
  g 0 * (Complex.I * (η : ℂ)) + d * (-1 - Complex.I * (η : ℂ)) +
    ∫ θ in (0 : ℝ)..π, coneAngularWeight θ •
      ((g (cos θ) - g 0 - (cos θ : ℂ) * d) * ((cos θ : ℂ)⁻¹) ^ 2)

private theorem cone_radial_pairing_measurable {g : ℝ → ℝ → ℂ}
    (hg : Measurable (Function.uncurry g)) (η h : ℝ) (n : ℕ) :
    Measurable fun r => coneAngularPairing η (h / r ^ 2) n (g r) := by
  have hcos : Measurable (fun q : ℝ × ℝ => (cos q.2 : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (continuous_cos.measurable.comp measurable_snd)
  have hHt : Measurable (fun q : ℝ × ℝ => ((η * (h / q.1 ^ 2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      (measurable_const.mul (measurable_const.div (measurable_fst.pow_const 2)))
  have hp : Measurable (fun q : ℝ × ℝ => coneAngularPole η (h / q.1 ^ 2) q.2 ^ n) :=
    ((hcos.add (measurable_const.mul hHt)).inv).pow_const _
  have hw : Measurable (fun q : ℝ × ℝ => coneAngularWeight q.2) :=
    ((continuous_const.sub continuous_cos).div_const π).measurable.comp measurable_snd
  have hg' : Measurable (fun q : ℝ × ℝ => g q.1 (cos q.2)) :=
    hg.comp (measurable_fst.prodMk (continuous_cos.measurable.comp measurable_snd))
  simp_rw [coneAngularPairing, intervalIntegral.integral_of_le pi_pos.le]
  exact ((hw.smul (hg'.mul hp)).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc 0 π))).measurable

private theorem cone_radial_angular_pairing_limit {g : ℝ → ℝ → ℂ} {L : ℝ → ℂ}
    (hg : Measurable (Function.uncurry g)) {η R : ℝ} {n : ℕ}
    (hR : 0 < R) {M : ℝ}
    (hbound : ∀ r ∈ Ioc (0 : ℝ) R, ∀ t > 0, ‖coneAngularPairing η t n (g r)‖ ≤ M)
    (hlim : ∀ r ∈ Ioc (0 : ℝ) R,
      Tendsto (fun t => coneAngularPairing η t n (g r)) (𝓝[>] (0 : ℝ)) (𝓝 (L r)))
    (hoff : ∀ r > R, ∀ u ∈ Icc (-1 : ℝ) 1, g r u = 0) :
    Tendsto (fun h : Height => ∫ r in Ioi (0 : ℝ), r •
        coneAngularPairing η ((h : ℝ) / r ^ 2) n (g r))
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 (∫ r in Ioc (0 : ℝ) R, r • L r)) := by
  let H := (𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))
  let μ := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) R)
  let F (h : Height) (r : ℝ) := r • coneAngularPairing η ((h : ℝ) / r ^ 2) n (g r)
  have hU : Ioc 0 R ∪ Ioi R = Ioi (0 : ℝ) := by
    ext r
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (hr | hr)
      · exact hr.1
      · exact hR.trans hr
    · intro hr
      rcases le_or_gt r R with ht | ht
      · exact Or.inl ⟨hr, ht⟩
      · exact Or.inr ht
  have hzero (h : Height) (r : ℝ) (hr : r ∈ Ioi R) : F h r = 0 := by
    unfold F coneAngularPairing
    simp [hoff r hr (cos _) ⟨neg_one_le_cos _, cos_le_one _⟩]
  have hCut (h : Height) : (∫ r, F h r ∂μ) = ∫ r in Ioi (0 : ℝ), F h r := by
    rw [← hU, integral_union_eq_left_of_forall measurableSet_Ioi (hzero h)]
  have hi : Integrable (fun r => r * M) μ :=
    ((continuous_id.mul continuous_const).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hHeight : Tendsto (fun h : Height => (h : ℝ)) H (𝓝 (0 : ℝ)) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  have hLim := tendsto_integral_filter_of_dominated_convergence
    (l := H) (μ := μ) (F := F) (f := fun r => r • L r) _ ?_ ?_ hi ?_
  · exact hLim.congr' (Eventually.of_forall hCut)
  · exact Eventually.of_forall fun h =>
      (measurable_id.smul (cone_radial_pairing_measurable hg η (h : ℝ) n)).aestronglyMeasurable
  · refine Eventually.of_forall fun h => ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    dsimp only [F]
    rw [norm_smul, Real.norm_of_nonneg hr.1.le]
    exact mul_le_mul_of_nonneg_left
      (hbound r hr _ (div_pos h.property (sq_pos_of_pos hr.1))) hr.1.le
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hT : Tendsto (fun h : Height => (h : ℝ) / r ^ 2) H (𝓝[>] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, Eventually.of_forall fun h => div_pos h.property (sq_pos_of_pos hr.1)⟩
      simpa only [zero_div] using hHeight.div_const (r ^ 2)
    exact ((hlim r hr).comp hT).const_smul r

variable {E : Type*} [NormedAddCommGroup E]

/-- Full single pole on a nonradial Cartesian test with uniformly Lipschitz
normal amplitude at the angular shell. No angular direction is selected. -/
theorem Plane.cone_nonradial_single_limit (diamond : Plane E) (ε : Evolution)
    {f : ℝ × Spatial → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
    {R : ℝ} (hR : 0 < R) (hoff : ∀ q, R < coneEuclideanRadius q → f q = 0)
    {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ r ∈ Ioc (0 : ℝ) R, ‖coneAngularAmplitude f r 0‖ ≤ M ∧
      ∀ u ∈ Icc (-1 : ℝ) 1,
        ‖coneAngularAmplitude f r u - coneAngularAmplitude f r 0‖ ≤ M * |u|) :
    Tendsto (fun h : Height => ∫ q : ℝ × Spatial,
      f q * diamond.poleCoefficient ε h (shellSquare q.1 q.2))
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 ((2 * π ^ 2 : ℝ) • ∫ r in Ioc (0 : ℝ) R, r •
        coneAngularSingleBoundary (diamond.eta ε) (coneAngularAmplitude f r))) := by
  have hC := cone_angular_amplitude_continuous hf hs
  have hB (r : ℝ) (hr : r ∈ Ioc 0 R) (t : ℝ) (ht : 0 < t) :
      ‖coneAngularPairing (diamond.eta ε) t 1 (coneAngularAmplitude f r)‖ ≤ 3 * M :=
    cone_angular_single_pairing_norm_le
      (hC.comp (continuous_const.prodMk continuous_id)) hM (hg r hr).1 (hg r hr).2
      (diamond.eta_sq ε) ht
  have h := (cone_radial_angular_pairing_limit hC.measurable hR
    hB (fun r hr => cone_angular_single_pairing_tendsto
      (hC.comp (continuous_const.prodMk continuous_id)) hM (hg r hr).2 (diamond.eta_sq ε))
    (fun r hr u hu => cone_angular_amplitude_zero_outside hoff (hR.trans hr).le hr hu)).const_smul
      (2 * π ^ 2 : ℝ)
  refine h.congr fun h => ?_
  have hP := diamond.cone_nonradial_polar_pairing ε h 1 hf hs
  simp only [pow_one] at hP
  rw [hP]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  congr 1
  field_simp [(show 0 < r from hr).ne']

/-- Full Cartesian square with two numerator powers, including the cone
tip under uniform quadratic normal control of the normalized angular test. -/
theorem Plane.cone_nonradial_quadratic_limit (diamond : Plane E) (ε : Evolution)
    {f : ℝ × Spatial → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
    {R : ℝ} (hR : 0 < R) (hoff : ∀ q, R < coneEuclideanRadius q → f q = 0)
    (d : ℝ → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ r ∈ Ioc (0 : ℝ) R, ‖coneQuadraticAngularAmplitude f r 0‖ ≤ M ∧ ‖d r‖ ≤ M ∧
      ∀ u ∈ Icc (-1 : ℝ) 1,
        ‖coneQuadraticAngularAmplitude f r u - coneQuadraticAngularAmplitude f r 0 -
          (u : ℂ) * d r‖ ≤ M * |u| ^ 2) :
    Tendsto (fun h : Height => ∫ q : ℝ × Spatial,
      f q * diamond.poleCoefficient ε h (shellSquare q.1 q.2) ^ 2)
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 ((2 * π ^ 2 : ℝ) • ∫ r in Ioc (0 : ℝ) R, r •
        coneAngularSquareBoundary (diamond.eta ε) (coneQuadraticAngularAmplitude f r) (d r))) := by
  have hMeas : Measurable (Function.uncurry (coneQuadraticAngularAmplitude f)) :=
    ((measurable_fst.pow_const 2).inv).smul (cone_angular_amplitude_continuous hf hs).measurable
  have hB (r : ℝ) (hr : r ∈ Ioc 0 R) (t : ℝ) (ht : 0 < t) :
      ‖coneAngularPairing (diamond.eta ε) t 2 (coneQuadraticAngularAmplitude f r)‖ ≤ 5 * M := by
    have h := cone_angular_square_pairing_norm_le
      (cone_quadratic_amplitude_continuous_normal hf hs r) (d r) hM (hg r hr).2.2
      (diamond.eta_sq ε) ht
    linarith [h, (hg r hr).1, (hg r hr).2.1]
  have h := (cone_radial_angular_pairing_limit hMeas hR
    hB (fun r hr => cone_angular_square_pairing_tendsto
      (cone_quadratic_amplitude_continuous_normal hf hs r) (d r) hM (hg r hr).2.2
      (diamond.eta_sq ε))
    (fun r hr u hu => by simp [coneQuadraticAngularAmplitude,
      cone_angular_amplitude_zero_outside hoff (hR.trans hr).le hr hu])).const_smul
      (2 * π ^ 2 : ℝ)
  exact h.congr fun h => (diamond.cone_nonradial_quadratic_pairing ε h hf hs).symm

end UV.SectorPlane
