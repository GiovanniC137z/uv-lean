import UV.ExtendShellMeasureBounds

/-! Weak limits on the full intrinsic four-momentum space. The selector
uses the signed coordinate on a fixed sector plane. The cut-arrow
version transports all components, including the three transverse ones. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Filter Set
open scoped ENNReal Topology

theorem norm_le_shell_frequency (m : ℝ) (p : Spatial) :
    ‖p‖ ≤ shellFrequency m p := by
  have hκ : 0 ≤ shellFrequency m p := Real.sqrt_nonneg _
  apply (sq_le_sq₀ (norm_nonneg _) hκ).mp
  rw [shell_frequency_square]
  exact le_add_of_nonneg_right (sq_nonneg m)

theorem shell_frequency_pos_of_ne_zero (m : ℝ) {p : Spatial} (hp : p ≠ 0) :
    0 < shellFrequency m p :=
  (norm_pos_iff.mpr hp).trans_le (norm_le_shell_frequency m p)

/-- The normalized density of the shell mollifier, before selecting an
axial sign. Its factor (2/(2π)^4) is the prescribed four-dimensional
Fourier measure times (2π), with the normalized Poisson delta. -/
def shellMollifierDensity (h m : ℝ) (q : ℝ × Spatial) : ℝ :=
  2 * polePoisson h (shellSquare q.1 q.2 - m ^ 2) / (2 * Real.pi) ^ 4

/-- Test the scalar shell selector on the full intrinsic momentum space.
The axial and transverse coordinates use the same product Lebesgue
measure at every positive height. -/
def selectedShellTest (σ h m : ℝ) (f : ℝ × Spatial → ℝ) : ℝ :=
  ∫ q in {q : ℝ × Spatial | 0 < σ * q.1}, shellMollifierDensity h m q * f q

private theorem abs_of_shell_sign {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : |σ| = 1 := by
  rcases hσ with rfl | rfl <;> norm_num

private theorem mul_shell_frequency_norm {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (r : ℝ) :
    ‖σ * r‖ = ‖r‖ := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_shell_sign hσ, one_mul, Real.norm_eq_abs]

private theorem shell_mollifier_continuous {h m : ℝ} (hh : 0 < h) :
    Continuous (shellMollifierDensity h m) := by
  have hf : Continuous (fun q : ℝ × Spatial => shellSquare q.1 q.2 - m ^ 2) := by
    unfold shellSquare
    fun_prop
  exact ((continuous_const.mul (continuous_const.div ((hf.pow 2).add continuous_const)
    (fun _ => by positivity))).div_const _)

private theorem shell_mollifier_density_on_signed_ray {σ h m : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (r : ℝ) (p : Spatial) :
    shellMollifierDensity h m (σ * r, p) =
      (2 / (2 * Real.pi) ^ 4) * polePoisson h (r ^ 2 - shellFrequency m p ^ 2) := by
  have hsq : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  unfold shellMollifierDensity shellSquare
  rw [Prod.fst, Prod.snd, mul_pow, hsq, one_mul, shell_frequency_square,
    sub_sub, div_mul_eq_mul_div]

/-- Exact Fubini identity for the finite-height test. The negative
selected ray is reflected as a real change of coordinates. -/
theorem selected_shell_test_eq_axial_transverse {σ h m : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hh : 0 < h) {f : ℝ × Spatial → ℝ}
    (hf : Continuous f) (hs : HasCompactSupport f) :
    selectedShellTest σ h m f =
      (2 / (2 * Real.pi) ^ 4) * ∫ p : Spatial, ∫ r in Ioi (0 : ℝ),
        polePoisson h (r ^ 2 - shellFrequency m p ^ 2) * f (σ * r, p) := by
  let S := {q : ℝ × Spatial | 0 < σ * q.1}
  let G := fun q : ℝ × Spatial => shellMollifierDensity h m q * f q
  have hS : MeasurableSet S := measurableSet_lt measurable_const
    (measurable_const.mul measurable_fst)
  have hg : Integrable G :=
    ((shell_mollifier_continuous hh).mul hf).integrable_of_hasCompactSupport
      (hs.mul_left (f := shellMollifierDensity h m))
  change (∫ q in S, G q) = _
  rw [← integral_indicator hS]
  have hprod : Integrable (S.indicator G)
      ((volume : Measure ℝ).prod (volume : Measure Spatial)) := hg.indicator hS
  change (∫ q, S.indicator G q ∂(volume : Measure ℝ).prod (volume : Measure Spatial)) = _
  rw [integral_prod_symm _ hprod, ← integral_const_mul]
  apply integral_congr_ae
  refine Eventually.of_forall fun p => ?_
  have hEq (r : ℝ) : S.indicator G (r, p) =
      {r : ℝ | 0 < σ * r}.indicator (fun r : ℝ => G (r, p)) r := by
    by_cases hr : 0 < σ * r <;> simp [S, hr]
  simp_rw [hEq]
  have hAxisSet : MeasurableSet {r : ℝ | 0 < σ * r} :=
    measurableSet_lt measurable_const (measurable_const.mul measurable_id)
  rw [integral_indicator hAxisSet]
  have hAxis : (∫ r in {r : ℝ | 0 < σ * r}, G (r, p)) =
      ∫ r in Ioi (0 : ℝ), G (σ * r, p) := by
    rcases hσ with rfl | rfl
    · simp [one_mul, Ioi]
    · simp only [neg_one_mul, neg_pos]
      change (∫ r in Iio (0 : ℝ), G (r, p)) = ∫ r in Ioi (0 : ℝ), G (-r, p)
      rw [← integral_Iic_eq_integral_Iio]
      simpa only [neg_zero] using (integral_comp_neg_Ioi (f := fun r => G (r, p)) 0).symm
  rw [hAxis, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  dsimp only [G]
  rw [shell_mollifier_density_on_signed_ray hσ]
  ring

private theorem compact_pair_test_radius {f : ℝ × Spatial → ℝ} (hs : HasCompactSupport f) :
    ∃ R : ℝ, ∀ q : ℝ × Spatial, R < ‖q‖ → f q = 0 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ × Spatial)).mp hs.isBounded
  refine ⟨R, fun q hq => ?_⟩
  by_contra hn
  have hp := hR (subset_tsupport f (show q ∈ Function.support f from hn))
  exact not_lt_of_ge (by simpa using hp) hq

private theorem compact_axial_test {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {f : ℝ × Spatial → ℝ}
    {R : ℝ} (hR : ∀ q : ℝ × Spatial, R < ‖q‖ → f q = 0) (p : Spatial) :
    HasCompactSupport (fun r : ℝ => f (σ * r, p)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : ℝ) R)
  intro r hr
  rw [Metric.mem_closedBall, dist_zero_right]
  apply le_of_not_gt
  intro h
  apply hr
  apply hR
  change R < max ‖σ * r‖ ‖p‖
  rw [mul_shell_frequency_norm hσ]
  exact h.trans_le (le_max_left _ _)

private theorem transverse_test_vanishes_off_ball {f : ℝ × Spatial → ℝ}
    {R : ℝ} (hR : ∀ q : ℝ × Spatial, R < ‖q‖ → f q = 0)
    {p : Spatial} (hp : p ∉ Metric.closedBall 0 R) (r : ℝ) : f (r, p) = 0 := by
  apply hR
  change R < max ‖r‖ ‖p‖
  have hp' : R < ‖p‖ := lt_of_not_ge (by simpa using hp)
  exact hp'.trans_le (le_max_right _ _)

/-- The normalized shell limit with transverse momenta integrated.
The exceptional spatial zero has measure zero. The same estimate treats
massive and massless regular sheets for every compact continuous test. -/
theorem selected_shell_test_limit {σ m : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {f : ℝ × Spatial → ℝ} (hf : Continuous f) (hs : HasCompactSupport f) :
    Tendsto (fun h : ℝ => selectedShellTest σ h m f) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ p : Spatial, f (σ * shellFrequency m p, p) *
        (((2 * Real.pi) ^ 3 * (2 * shellFrequency m p))⁻¹))) := by
  obtain ⟨R, hR⟩ := compact_pair_test_radius hs
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hs
  have hC₀ : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  let F (h : ℝ) (p : Spatial) := ∫ r in Ioi (0 : ℝ),
    polePoisson h (r ^ 2 - shellFrequency m p ^ 2) * f (σ * r, p)
  let b (p : Spatial) := (Metric.closedBall (0 : Spatial) R).indicator (fun p : Spatial =>
    ((Real.pi + 1 / 3) * C) * ‖p‖⁻¹) p
  have hBi : IntegrableOn (fun p : Spatial =>
      ((Real.pi + 1 / 3) * C) * ‖p‖⁻¹) (Metric.closedBall 0 R) :=
    (integrableOn_inv_norm_closedBall_spatial R).const_mul _
  have hb : Integrable b :=
    hBi.integrable_indicator Metric.isClosed_closedBall.measurableSet
  have hcv (p : Spatial) : Continuous (fun r : ℝ => f (σ * r, p)) :=
    hf.comp ((continuous_const.mul continuous_id).prodMk continuous_const)
  have hsup (p : Spatial) : HasCompactSupport (fun r : ℝ => f (σ * r, p)) :=
    compact_axial_test hσ hR p
  have hp0 : ∀ᵐ p : Spatial ∂(volume : Measure Spatial), p ≠ 0 := by
    rw [ae_iff]
    simp
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ)) (μ := volume)
    (F := F) (f := fun p => Real.pi * (f (σ * shellFrequency m p, p) / (2 * shellFrequency m p)))
    b ?_ ?_ hb ?_
  · have hscaled := hlim.const_mul (2 / (2 * Real.pi) ^ 4)
    have eq_at_height : (fun h => (2 / (2 * Real.pi) ^ 4) * ∫ p, F h p) =ᶠ[𝓝[>] 0]
        (fun h => selectedShellTest σ h m f) := by
      filter_upwards [self_mem_nhdsWithin] with h hh
      exact (selected_shell_test_eq_axial_transverse hσ hh hf hs).symm
    have eq_limit : (2 / (2 * Real.pi) ^ 4) *
        (∫ p : Spatial, Real.pi * (f (σ * shellFrequency m p, p) / (2 * shellFrequency m p))) =
        ∫ p : Spatial, f (σ * shellFrequency m p, p) *
          (((2 * Real.pi) ^ 3 * (2 * shellFrequency m p))⁻¹) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hp0] with p hp
      have hk := shell_frequency_pos_of_ne_zero m hp
      field_simp [Real.pi_ne_zero, hk.ne']
    rw [eq_limit] at hscaled
    exact hscaled.congr' eq_at_height
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hpos : 0 < h := hh
    have hc : Continuous (fun z : Spatial × ℝ => polePoisson h
        (z.2 ^ 2 - (‖z.1‖ ^ 2 + m ^ 2)) * f (σ * z.2, z.1)) := by
      have harg : Continuous (fun z : Spatial × ℝ => z.2 ^ 2 - (‖z.1‖ ^ 2 + m ^ 2)) := by
        fun_prop
      exact (continuous_const.div ((harg.pow 2).add continuous_const)
        (fun _ => by positivity)).mul
        (hf.comp ((continuous_const.mul continuous_snd).prodMk continuous_fst))
    have hm := hc.stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure ℝ).restrict (Ioi 0))
    change AEStronglyMeasurable (F h) volume
    simpa only [F, shell_frequency_square] using hm.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hpos : 0 < h := hh
    filter_upwards [hp0] with p hp
    by_cases hpR : p ∈ Metric.closedBall (0 : Spatial) R
    · have hk := shell_frequency_pos_of_ne_zero m hp
      have hnorm := positive_ray_poisson_test_norm_le hk hpos
        ((hcv p).integrable_of_hasCompactSupport (hsup p)).integrableOn C
        (fun r => hC (σ * r, p))
      change ‖F h p‖ ≤ b p
      simp only [b, indicator_of_mem hpR]
      exact hnorm.trans (by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left
          (inv_anti₀ (norm_pos_iff.mpr hp) (norm_le_shell_frequency m p))
          (mul_nonneg (by positivity) hC₀))
    · change ‖F h p‖ ≤ b p
      have hzero : ∀ r, f (σ * r, p) = 0 :=
        fun r => transverse_test_vanishes_off_ball hR hpR (σ * r)
      simp [F, b, hpR, hzero]
  · filter_upwards [hp0] with p hp
    exact positive_ray_shell_poisson_limit (shell_frequency_pos_of_ne_zero m hp) (hcv p)
      C (fun r => hC (σ * r, p))
      ((hcv p).integrable_of_hasCompactSupport (hsup p)).integrableOn

variable {E : Type*} [NormedAddCommGroup E]

/-- The positive shell measure has the stated spatial density also for
ordinary real test integrals. -/
theorem Plane.positive_shell_measure_test (diamond : Plane E) (m : ℝ)
    {f : ℝ × Spatial → ℝ} (hf : Continuous f) :
    (∫ q, f q ∂diamond.positiveShellMeasure m) =
      ∫ p : Spatial, f (diamond.physicalShellPoint m p) *
        (((2 * Real.pi) ^ 3 * (2 * shellFrequency m p))⁻¹) := by
  have hκ : Continuous (shellFrequency m) :=
    Real.continuous_sqrt.comp ((continuous_norm.pow 2).add continuous_const)
  let w (p : Spatial) := (((2 * Real.pi) ^ 3 * (2 * shellFrequency m p))⁻¹)
  have hw : Measurable (fun p : Spatial => ENNReal.ofReal (w p)) :=
    ((measurable_const.mul (measurable_const.mul hκ.measurable)).inv).ennreal_ofReal
  rw [Plane.positiveShellMeasure, integral_map (diamond.physical_shell_point_continuous m).measurable.aemeasurable
    hf.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul hw
    (Eventually.of_forall fun p => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  refine Eventually.of_forall fun p => ?_
  have hw₀ : 0 ≤ w p := by
    dsimp [w]
    have : 0 ≤ shellFrequency m p := Real.sqrt_nonneg _
    positivity
  change (ENNReal.ofReal (w p)).toReal • f (diamond.physicalShellPoint m p) = _
  rw [ENNReal.toReal_ofReal hw₀, smul_eq_mul, mul_comm]

/-- Full scalar state normalization as a compact test limit on the signed
physical sheet. The limit is the positive measure already constructed
on the fixed plane. -/
theorem Plane.physical_shell_test_limit (diamond : Plane E) (m : ℝ)
    {f : ℝ × Spatial → ℝ} (hf : Continuous f) (hs : HasCompactSupport f) :
    Tendsto (fun h : ℝ => selectedShellTest (sectorSign diamond.s) h m f) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ q, f q ∂diamond.positiveShellMeasure m)) := by
  rw [diamond.positive_shell_measure_test m hf]
  exact selected_shell_test_limit (by cases diamond.s <;> simp [sectorSign]) hf hs

theorem cut_arrow_is_identity_or_negation (ε : Evolution) :
    cutArrow ε = id ∨ cutArrow ε = fun q => -q := by
  cases ε
  · left
    funext q
    simp [cutArrow, evolutionSign]
  · right
    funext q
    simp only [cutArrow, evolutionSign, neg_one_mul, neg_one_smul]
    exact Prod.ext rfl rfl

private theorem map_neg_addHaar {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] : Measure.map (fun q : V => -q) μ = μ := by
  have he : (fun q : V => -q) = fun q => (-1 : ℝ) • q :=
    funext fun q => (neg_one_smul ℝ q).symm
  rw [he, Measure.map_addHaar_smul μ (by norm_num : (-1 : ℝ) ≠ 0), abs_inv, abs_pow]
  norm_num

theorem cut_arrow_preserves_volume (ε : Evolution) :
    MeasurePreserving (cutArrow ε) (volume : Measure (ℝ × Spatial)) volume := by
  rcases cut_arrow_is_identity_or_negation ε with h | h
  · rw [h]
    exact MeasurePreserving.id _
  · rw [h]
    refine ⟨measurable_neg, ?_⟩
    change Measure.map (Prod.map (fun x : ℝ => -x) (fun p : Spatial => -p))
      ((volume : Measure ℝ).prod (volume : Measure Spatial)) =
      (volume : Measure ℝ).prod (volume : Measure Spatial)
    rw [← Measure.map_prod_map _ _ measurable_neg measurable_neg,
      map_neg_addHaar (volume : Measure ℝ), map_neg_addHaar (volume : Measure Spatial)]

theorem cut_arrow_measurableEmbedding (ε : Evolution) :
    MeasurableEmbedding (cutArrow ε) := by
  rcases cut_arrow_is_identity_or_negation ε with h | h
  · rw [h]
    exact MeasurableEmbedding.id
  · rw [h]
    exact (MeasurableEquiv.neg (ℝ × Spatial)).measurableEmbedding

theorem Plane.cut_arrow_selector (diamond : Plane E) (ε : Evolution) (q : ℝ × Spatial) :
    diamond.eta ε * (cutArrow ε q).1 = sectorSign diamond.s * q.1 := by
  change (sectorSign diamond.s * evolutionSign ε) * (evolutionSign ε * q.1) = _
  calc
    _ = sectorSign diamond.s * (evolutionSign ε ^ 2) * q.1 := by ring
    _ = _ := by rw [evolutionSign_sq, mul_one]

theorem cut_arrow_shell_mollifier (ε : Evolution) (h m : ℝ) (q : ℝ × Spatial) :
    shellMollifierDensity h m (cutArrow ε q) = shellMollifierDensity h m q := by
  rcases cut_arrow_is_identity_or_negation ε with hε | hε
  · simp [hε]
  · simp only [hε, shellMollifierDensity, Prod.fst_neg, Prod.snd_neg, shellSquare_reverse]

/-- Routing gives the correct branch-selected tested shell at every
finite height. The identity transports the test by the full arrow. -/
theorem Plane.selected_shell_test_cut_arrow (diamond : Plane E) (ε : Evolution)
    (h m : ℝ) (f : ℝ × Spatial → ℝ) :
    selectedShellTest (diamond.eta ε) h m f =
      selectedShellTest (sectorSign diamond.s) h m (f ∘ cutArrow ε) := by
  unfold selectedShellTest
  rw [← integral_indicator (measurableSet_lt measurable_const (measurable_const.mul measurable_fst)),
    ← integral_indicator (measurableSet_lt measurable_const (measurable_const.mul measurable_fst))]
  rw [← (cut_arrow_preserves_volume ε).integral_comp (cut_arrow_measurableEmbedding ε)]
  apply integral_congr_ae
  refine Eventually.of_forall fun q => ?_
  by_cases hq : 0 < sectorSign diamond.s * q.1 <;>
    simp [diamond.cut_arrow_selector ε, cut_arrow_shell_mollifier ε, hq]

private theorem cut_arrow_preserves_compact_test (ε : Evolution)
    {f : ℝ × Spatial → ℝ} (hs : HasCompactSupport f) :
    HasCompactSupport (f ∘ cutArrow ε) := by
  obtain ⟨R, hR⟩ := compact_pair_test_radius hs
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : ℝ × Spatial) R)
  intro q hq
  rw [Metric.mem_closedBall, dist_zero_right]
  apply le_of_not_gt
  intro h
  apply hq
  apply hR
  rcases cut_arrow_is_identity_or_negation ε with he | he
  · exact he ▸ h
  · rw [he, norm_neg]
    exact h

/-- The four-dimensional branch selector converges to the scalar
completeness measure routed by the entire real cut arrow. -/
theorem Plane.routed_shell_test_limit (diamond : Plane E) (ε : Evolution) (m : ℝ)
    {f : ℝ × Spatial → ℝ} (hf : Continuous f) (hs : HasCompactSupport f) :
    Tendsto (fun h : ℝ => selectedShellTest (diamond.eta ε) h m f) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ k, f k ∂Measure.map (cutArrow ε) (diamond.positiveShellMeasure m))) := by
  rw [integral_map (cut_arrow_continuous ε).measurable.aemeasurable hf.aestronglyMeasurable]
  have hlim := diamond.physical_shell_test_limit m (hf.comp (cut_arrow_continuous ε))
    (cut_arrow_preserves_compact_test ε hs)
  simp_rw [diamond.selected_shell_test_cut_arrow ε _ m f]
  exact hlim

end UV.SectorPlane
