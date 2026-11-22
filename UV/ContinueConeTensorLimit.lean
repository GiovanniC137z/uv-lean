import UV.ContinueConeTensorRadial

/-! Boundary limits of the actual radial quadratic channels of the
unweighted pole square, with uniform integrable bounds through the tip. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Set Filter Real
open scoped Topology

private theorem cone_positive_radial_limit {C : ℝ → ℂ} (hC : Continuous C)
    {M : ℝ} (hM : ∀ t ≥ 0, ‖C t‖ ≤ M) {φ : ℝ → ℝ} (hc : Continuous φ)
    {R : ℝ} (hR : 0 < R) (hs : ∀ r > R, φ r = 0) :
    Tendsto (fun h : Height => ∫ r in Ioi (0 : ℝ), (r * φ r) • C ((h : ℝ) / r ^ 2))
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 ((∫ r in Ioi (0 : ℝ), r * φ r) • C 0)) := by
  let H := (𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))
  let μ := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) R)
  let F (h : Height) (r : ℝ) := (r * φ r) • C ((h : ℝ) / r ^ 2)
  let L (r : ℝ) := (r * φ r) • C 0
  have hU : Ioc 0 R ∪ Ioi R = Ioi (0 : ℝ) := by
    ext r
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (hr | hr)
      · exact hr.1
      · exact hR.trans hr
    · intro hr
      rcases le_or_gt r R with h | h
      · exact Or.inl ⟨hr, h⟩
      · exact Or.inr h
  have hCut (f : ℝ → ℂ) (hf : ∀ r > R, f r = 0) :
      (∫ r, f r ∂μ) = ∫ r in Ioi (0 : ℝ), f r := by
    rw [← hU, integral_union_eq_left_of_forall measurableSet_Ioi (fun r hr => hf r hr)]
  have hi : Integrable (fun r => ‖r * φ r‖ * M) μ :=
    ((continuous_id.mul hc).norm.mul continuous_const).continuousOn.integrableOn_compact
      isCompact_Icc |>.mono_set Ioc_subset_Icc_self
  have hHeight : Tendsto (fun h : Height => (h : ℝ)) H (𝓝 (0 : ℝ)) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  have hLim := tendsto_integral_filter_of_dominated_convergence
    (l := H) (μ := μ) (F := F) (f := L) _ ?_ ?_ hi ?_
  · have hL : (∫ r, L r ∂μ) = (∫ r in Ioi (0 : ℝ), r * φ r) • C 0 := by
      rw [hCut L (fun r hr => by simp [L, hs r hr])]
      exact integral_smul_const _ _
    rw [hL] at hLim
    exact hLim.congr' (Eventually.of_forall fun h => hCut (F h) (fun r hr => by simp [F, hs r hr]))
  · exact Eventually.of_forall fun h =>
      ((continuous_id.mul hc).measurable.smul
        (hC.measurable.comp (measurable_const.div (measurable_id.pow_const 2)))).aestronglyMeasurable
  · refine Eventually.of_forall fun h => Eventually.of_forall fun r => ?_
    dsimp only [F]
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hM _ (div_nonneg h.property.le (sq_nonneg r))) (norm_nonneg _)
  · refine Eventually.of_forall fun r => ?_
    have ht : Tendsto (fun h : Height => (h : ℝ) / r ^ 2) H (𝓝 (0 : ℝ)) := by
      simpa only [zero_div] using hHeight.div_const (r ^ 2)
    exact ((hC.continuousAt (x := 0)).tendsto.comp ht).const_smul (r * φ r)

private theorem cone_closed_continuous (η : ℝ) :
    Continuous (coneTemporalClosed η) ∧ Continuous (coneSpatialClosed η) := by
  have hS : Continuous (fun t : ℝ => (sqrt (1 + t ^ 2) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2)))
  have hS₀ (t : ℝ) : (sqrt (1 + t ^ 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sqrt_pos.mpr (by positivity)).ne'
  have h₁ : Continuous (coneFirstClosed η) := by
    unfold coneFirstClosed
    exact ((Complex.continuous_ofReal.sub continuous_const).div hS hS₀).sub continuous_const
  have h₂ : Continuous (coneSecondClosed η) := by
    unfold coneSecondClosed
    exact (continuous_const.sub Complex.continuous_ofReal).div (hS.pow 3)
      (fun t => pow_ne_zero _ (hS₀ t))
  have hZ : Continuous (fun t : ℝ => Complex.I * ((η * t : ℝ) : ℂ)) :=
    continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id))
  exact ⟨(((continuous_const.sub hZ).mul h₂).add h₁).div_const 2,
    (((continuous_const.add hZ).mul h₂).sub h₁).div_const 6⟩

variable {E : Type*} [NormedAddCommGroup E]

theorem Plane.cone_temporal_radial_limit (diamond : Plane E) (ε : Evolution)
    {φ : ℝ → ℝ} (hc : Continuous φ) {R : ℝ} (hR : 0 < R) (hs : ∀ r > R, φ r = 0) :
    Tendsto (fun h : Height => diamond.coneQuadraticPairing ε h 1 0 φ)
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 ((2 * π ^ 2 : ℝ) • ((∫ r in Ioi (0 : ℝ), r * φ r) • (-(1 / 2) : ℂ)))) := by
  let η := diamond.eta ε
  have hL := (cone_positive_radial_limit (cone_closed_continuous η).1
    (fun _ ht => coneTemporalClosed_norm_le ht (diamond.eta_sq ε)) hc hR hs).const_smul
      (2 * π ^ 2 : ℝ)
  have h0 : coneTemporalClosed η 0 = -(1 / 2) := by
    norm_num [coneTemporalClosed, coneFirstClosed, coneSecondClosed]
    ring
  rw [h0] at hL
  refine hL.congr ?_
  intro h
  rw [diamond.cone_temporal_radial_integral ε h hc hs]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [coneTemporalSecond_eq_closed (div_pos h.property (sq_pos_of_pos hr)) (diamond.eta_sq ε)]

theorem Plane.cone_one_third_spatial_radial_limit (diamond : Plane E) (ε : Evolution)
    {φ : ℝ → ℝ} (hc : Continuous φ) {R : ℝ} (hR : 0 < R) (hs : ∀ r > R, φ r = 0) :
    Tendsto (fun h : Height => diamond.coneQuadraticPairing ε h 0 (1 / 3) φ)
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 ((2 * π ^ 2 : ℝ) • ((∫ r in Ioi (0 : ℝ), r * φ r) •
        ((1 + 2 * Complex.I * (diamond.eta ε : ℂ)) / 6)))) := by
  let η := diamond.eta ε
  have hL := (cone_positive_radial_limit (cone_closed_continuous η).2
    (fun _ ht => coneSpatialClosed_norm_le ht (diamond.eta_sq ε)) hc hR hs).const_smul
      (2 * π ^ 2 : ℝ)
  have h0 : coneSpatialClosed η 0 = (1 + 2 * Complex.I * (η : ℂ)) / 6 := by
    norm_num [coneSpatialClosed, coneFirstClosed, coneSecondClosed]
    ring
  rw [h0] at hL
  refine hL.congr ?_
  intro h
  rw [diamond.cone_one_third_spatial_radial_integral ε h hc hs]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [coneSpatialSecond_eq_closed (div_pos h.property (sq_pos_of_pos hr)) (diamond.eta_sq ε)]

end UV.SectorPlane
