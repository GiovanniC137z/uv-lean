import UV.AdvanceConeAngularSmooth

/-! The axial running factor acts on tests by reflecting the two intrinsic
axial sheets. Positive height and the oriented scalar inverse stay fixed. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Real Set
open scoped Interval Topology

/-- Reflection of only the real axial momentum slot. -/
def coneAxialReflection (q : ℝ × Spatial) : ℝ × Spatial :=
  (-q.1, q.2)

theorem cone_axial_reflection_continuous : Continuous coneAxialReflection :=
  continuous_fst.neg.prodMk continuous_snd

theorem cone_axial_reflection_contDiff {n : WithTop ℕ∞} :
    ContDiff ℝ n coneAxialReflection :=
  contDiff_fst.neg.prodMk contDiff_snd

private def coneAxialReflectionEquiv : (ℝ × Spatial) ≃ᵐ (ℝ × Spatial) :=
  (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl Spatial)

theorem cone_axial_reflection_measurePreserving :
    MeasurePreserving coneAxialReflection volume volume :=
  (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
    (MeasurePreserving.id (volume : Measure Spatial))

theorem cone_axial_reflection_shell (q : ℝ × Spatial) :
    shellSquare (coneAxialReflection q).1 (coneAxialReflection q).2 = shellSquare q.1 q.2 := by
  simp [coneAxialReflection, shellSquare]

private theorem cone_axial_sign_neg (x : ℝ) : axialSign (-x) = -axialSign x := by
  by_cases hx : x = 0
  · simp [hx, axialSign]
  · exact axialSign_neg hx

private theorem cone_axial_sign_measurable : Measurable axialSign := by
  unfold axialSign
  exact measurable_const.ite (measurableSet_lt measurable_const measurable_id)
    (measurable_const.ite (measurableSet_lt measurable_id measurable_const) measurable_const)

private theorem cone_axial_sign_norm_le (x : ℝ) : ‖axialSign x‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  by_cases hx : x = 0
  · simp [hx, axialSign]
  · rw [axialSign_abs hx]

/-- The odd Cartesian part before folding the real axial variable. -/
def coneAxialOddPart (f : ℝ × Spatial → ℂ) (q : ℝ × Spatial) : ℂ :=
  (f q - f (coneAxialReflection q)) / 2

/-- The running sign on the odd part as a genuinely continuous folded
Cartesian test. This includes the zero axial slot. -/
def coneRunningEvenTest (f : ℝ × Spatial → ℂ) (q : ℝ × Spatial) : ℂ :=
  coneAxialOddPart f (|q.1|, q.2)

theorem cone_running_even_test_continuous {f : ℝ × Spatial → ℂ} (hf : Continuous f) :
    Continuous (coneRunningEvenTest f) := by
  have hOdd : Continuous (coneAxialOddPart f) :=
    (hf.sub (hf.comp cone_axial_reflection_continuous)).div_const 2
  exact hOdd.comp (continuous_fst.abs.prodMk continuous_snd)

theorem cone_running_even_test_eq (f : ℝ × Spatial → ℂ) (q : ℝ × Spatial) :
    coneRunningEvenTest f q = axialSign q.1 • coneAxialOddPart f q := by
  unfold coneRunningEvenTest coneAxialOddPart coneAxialReflection
  rcases lt_trichotomy q.1 0 with hp | hz | hp
  · simp only [abs_of_neg hp, neg_neg, axialSign, if_neg hp.not_gt, if_pos hp,
      neg_smul, one_smul]
    ring
  · simp [hz, axialSign]
  · simp [abs_of_pos hp, axialSign, hp]

theorem cone_running_even_test_zero_outside {f : ℝ × Spatial → ℂ} {R : ℝ}
    (hf : ∀ q, R < coneEuclideanRadius q → f q = 0) (q : ℝ × Spatial)
    (hq : R < coneEuclideanRadius q) : coneRunningEvenTest f q = 0 := by
  unfold coneRunningEvenTest coneAxialOddPart coneAxialReflection
  have hp : coneEuclideanRadius (|q.1|, q.2) = coneEuclideanRadius q := by
    simp [coneEuclideanRadius, sq_abs]
  have hn : coneEuclideanRadius (-|q.1|, q.2) = coneEuclideanRadius q := by
    simp [coneEuclideanRadius, sq_abs]
  simp [hf _ (hp.symm ▸ hq), hf _ (hn.symm ▸ hq)]

theorem cone_running_even_test_compactSupport {f : ℝ × Spatial → ℂ}
    (hs : HasCompactSupport f) : HasCompactSupport (coneRunningEvenTest f) := by
  obtain ⟨R, _, hR⟩ := cone_radial_cutoff_of_compact hs
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × Spatial) R)
  intro q hq
  have hr : R < ‖q‖ := lt_of_not_ge fun h => hq (by simpa [Metric.mem_closedBall] using h)
  exact cone_running_even_test_zero_outside hR q (hr.trans_le (norm_le_coneEuclideanRadius q))

private theorem cone_running_integrable {f : ℝ × Spatial → ℂ} (hf : Integrable f) :
    Integrable (fun q : ℝ × Spatial => axialSign q.1 • f q) := by
  have hm := (cone_axial_sign_measurable.comp measurable_fst).aestronglyMeasurable.smul
    hf.aestronglyMeasurable
  apply hf.norm.mono' hm
  exact Eventually.of_forall fun q => by
    rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (cone_axial_sign_norm_le q.1)

/-- Every even axial multiplier pairs the original running sign with the
continuous folded odd test. The substitution is in the original Cartesian
Lebesgue measure. -/
theorem cone_running_integral_even {f K : ℝ × Spatial → ℂ} (hi : Integrable (f * K))
    (hK : ∀ q, K (coneAxialReflection q) = K q) :
    (∫ q : ℝ × Spatial, axialSign q.1 • (f q * K q)) =
      ∫ q : ℝ × Spatial, coneRunningEvenTest f q * K q := by
  let A (q : ℝ × Spatial) := axialSign q.1 • (f q * K q)
  let B (q : ℝ × Spatial) := axialSign q.1 • (f (coneAxialReflection q) * K q)
  have hA : Integrable A := cone_running_integrable hi
  have hrefl : (A ∘ coneAxialReflection) = -B := by
    funext q
    unfold A B
    simp [Function.comp_apply, coneAxialReflection, ← hK q,
      cone_axial_sign_neg]
  have hB : Integrable B := by
    have h := cone_axial_reflection_measurePreserving.integrable_comp_of_integrable hA
    rw [hrefl] at h
    simpa only [neg_neg] using h.neg
  have hBA : (∫ q : ℝ × Spatial, B q) = - ∫ q : ℝ × Spatial, A q := by
    have h := cone_axial_reflection_measurePreserving.integral_comp
      coneAxialReflectionEquiv.measurableEmbedding A
    change (∫ q : ℝ × Spatial, (A ∘ coneAxialReflection) q) = _ at h
    rw [hrefl] at h
    change (∫ q : ℝ × Spatial, -B q) = _ at h
    rw [integral_neg] at h
    exact neg_eq_iff_eq_neg.mp h
  have hpoint (q : ℝ × Spatial) : coneRunningEvenTest f q * K q = (A q - B q) / 2 := by
    rw [cone_running_even_test_eq]
    simp only [A, B, coneAxialOddPart, Complex.real_smul]
    ring
  change (∫ q : ℝ × Spatial, A q) = _
  simp_rw [hpoint]
  have hDif : Integrable (fun q => A q - B q) := hA.sub hB
  rw [integral_div, integral_sub hA hB, hBA]
  ring

/-- The signed normalized angular profile, evaluated at both intrinsic
norm-one branches before taking their half-difference. -/
def coneRunningAngularAmplitude (f : ℝ × Spatial → ℂ) (r u : ℝ) : ℂ :=
  (coneSpatialMean f (r * coneAxialCoordinate u, r * coneSpatialCoordinate u) -
    coneSpatialMean f (-(r * coneAxialCoordinate u), r * coneSpatialCoordinate u)) / 2

theorem cone_running_angular_amplitude_eq (f : ℝ × Spatial → ℂ) (r u : ℝ)
    (hr : 0 ≤ r) (hf : Continuous f) :
    coneAngularAmplitude (coneRunningEvenTest f) r u = coneRunningAngularAmplitude f r u := by
  have hA : 0 ≤ r * coneAxialCoordinate u := mul_nonneg hr (sqrt_nonneg _)
  unfold coneAngularAmplitude coneRunningAngularAmplitude coneAxialMean coneSpatialMean
  simp only [coneRunningEvenTest, coneAxialOddPart, coneAxialReflection, abs_neg,
    abs_of_nonneg hA]
  let Fplus (ω : ConeSpatialSphere) := f (r * coneAxialCoordinate u,
    (r * coneSpatialCoordinate u) • (ω : Spatial))
  let Fminus (ω : ConeSpatialSphere) := f (-(r * coneAxialCoordinate u),
    (r * coneSpatialCoordinate u) • (ω : Spatial))
  have hFplus : Continuous Fplus := by unfold Fplus; fun_prop
  have hFminus : Continuous Fminus := by unfold Fminus; fun_prop
  letI : CompactSpace ConeSpatialSphere := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  have hiplus : Integrable Fplus coneSpatialSphereMeasure :=
    hFplus.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have himinus : Integrable Fminus coneSpatialSphereMeasure :=
    hFminus.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change ((4 * π)⁻¹ • (∫ ω, (Fplus ω - Fminus ω) / 2 ∂coneSpatialSphereMeasure) +
      (4 * π)⁻¹ • (∫ ω, (Fplus ω - Fminus ω) / 2 ∂coneSpatialSphereMeasure)) / 2 =
    ((4 * π)⁻¹ • (∫ ω, Fplus ω ∂coneSpatialSphereMeasure) -
      (4 * π)⁻¹ • (∫ ω, Fminus ω ∂coneSpatialSphereMeasure)) / 2
  rw [integral_div, integral_sub hiplus himinus]
  simp only [Complex.real_smul]
  ring

end UV.SectorPlane
