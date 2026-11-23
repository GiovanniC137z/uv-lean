import UV.ContinueConePolar
import UV.AdvanceConeAngularLimits

/-! Four-momentum polar disintegration of nonradial tests. The spatial
direction has Euclidean norm one, and the two axial signs remain separately
sampled before taking their average. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Real Set
open scoped Interval Topology

abbrev ConeSpatialSphere := Metric.sphere (0 : Spatial) 1

def coneSpatialSphereMeasure : Measure ConeSpatialSphere :=
  (volume : Measure Spatial).toSphere

instance : IsFiniteMeasure coneSpatialSphereMeasure := by
  unfold coneSpatialSphereMeasure
  infer_instance

theorem cone_spatial_direction_norm (ω : ConeSpatialSphere) : ‖(ω : Spatial)‖ = 1 :=
  mem_sphere_zero_iff_norm.mp ω.property

theorem cone_spatial_sphere_area : coneSpatialSphereMeasure.real univ = 4 * π := by
  simp [coneSpatialSphereMeasure, Spatial, Measure.real,
    ENNReal.toReal_ofReal (show 0 ≤ π * 4 / 3 by positivity)]
  ring

/-- Spherical averaging uses the area of the actual spatial unit sphere. -/
def coneSpatialMean (f : ℝ × Spatial → ℂ) (z : ℝ × ℝ) : ℂ :=
  (4 * π)⁻¹ • ∫ ω : ConeSpatialSphere, f (z.1, z.2 • (ω : Spatial))
    ∂coneSpatialSphereMeasure

private theorem cone_spatial_polar_integral (f : Spatial → ℂ) (hi : Integrable f) :
    (∫ p, f p) = ∫ y in Ioi (0 : ℝ), y ^ 2 •
      ∫ ω : ConeSpatialSphere, f (y • (ω : Spatial)) ∂coneSpatialSphereMeasure := by
  let μ := (volume : Measure Spatial).comap
    (Subtype.val : ({(0 : Spatial)}ᶜ : Set Spatial) → Spatial)
  let e := homeomorphUnitSphereProd Spatial
  let F (z : ConeSpatialSphere × Ioi (0 : ℝ)) : ℂ := f (z.2.val • z.1.val)
  have hp : MeasurePreserving e μ
      (coneSpatialSphereMeasure.prod (Measure.volumeIoiPow 2)) := by
    simpa [μ, e, coneSpatialSphereMeasure, Spatial] using
      (volume : Measure Spatial).measurePreserving_homeomorphUnitSphereProd
  have hemi := (Homeomorph.measurableEmbedding e)
  have hf : Integrable (fun p : ({(0 : Spatial)}ᶜ : Set Spatial) => f p.val) μ :=
    (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mp hi.integrableOn
  have hh : Integrable (F ∘ e) μ := hf.congr (Eventually.of_forall fun p => by
    change f p.val = f ((e p).2.val • (e p).1.val)
    rw [← homeomorphUnitSphereProd_symm_apply_coe]
    change f p.val = f (e.symm (e p)).val
    rw [e.symm_apply_apply])
  have hI := (hp.integrable_comp_emb hemi).mp hh
  calc
    _ = ∫ p : ({(0 : Spatial)}ᶜ : Set Spatial), f p.val ∂μ := by
      dsimp only [μ]
      rw [integral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
    _ = ∫ z, F z ∂(coneSpatialSphereMeasure.prod (Measure.volumeIoiPow 2)) := by
      rw [← hp.integral_comp hemi F]
      apply integral_congr_ae
      refine Eventually.of_forall fun p => ?_
      change f p.val = f ((e p).2.val • (e p).1.val)
      rw [← homeomorphUnitSphereProd_symm_apply_coe]
      change f p.val = f (e.symm (e p)).val
      rw [e.symm_apply_apply]
    _ = ∫ y : Ioi (0 : ℝ), ∫ ω : ConeSpatialSphere, f (y.val • (ω : Spatial))
          ∂coneSpatialSphereMeasure ∂Measure.volumeIoiPow 2 := integral_prod_symm F hI
    _ = _ := by
      simp only [Measure.volumeIoiPow, ENNReal.ofReal]
      rw [integral_withDensity_eq_integral_smul]
      · rw [← integral_subtype_comap measurableSet_Ioi
          (fun y => y ^ 2 • ∫ ω : ConeSpatialSphere, f (y • (ω : Spatial))
            ∂coneSpatialSphereMeasure)]
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by
          dsimp only
          rw [NNReal.smul_def, Real.coe_toNNReal _ (by positivity)]
      · exact (measurable_subtype_coe.pow_const 2).real_toNNReal

theorem cone_spatial_mean_continuous {f : ℝ × Spatial → ℂ} (hf : Continuous f)
    (hs : HasCompactSupport f) : Continuous (coneSpatialMean f) := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hs
  have hφ : Continuous (fun z : (ℝ × ℝ) × ConeSpatialSphere =>
      f (z.1.1, z.1.2 • (z.2 : Spatial))) := by fun_prop
  apply continuous_iff_continuousAt.mpr
  intro x
  unfold ContinuousAt coneSpatialMean
  apply Tendsto.const_smul
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : ConeSpatialSphere => C)
  · exact Eventually.of_forall fun z =>
      (hφ.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Eventually.of_forall fun _ => Eventually.of_forall fun _ => hC _
  · exact integrable_const _
  · refine Eventually.of_forall fun ω => ?_
    exact (hφ.comp (continuous_id.prodMk continuous_const)).continuousAt.tendsto

private theorem cone_spatial_mean_norm_eval {f : ℝ × Spatial → ℂ} (hf : Continuous f)
    (hs : HasCompactSupport f) (x : ℝ) :
    (∫ p : Spatial, f (x, p)) =
      ∫ p : Spatial, coneSpatialMean f (x, ‖p‖) := by
  obtain ⟨R, hR⟩ := hs.isBounded.subset_closedBall (0 : ℝ × Spatial)
  have hF : Integrable (fun p : Spatial => f (x, p)) := by
    apply (hf.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    apply HasCompactSupport.intro (isCompact_closedBall (0 : Spatial) R)
    intro p hp
    by_contra hn
    have h := hR (subset_tsupport f hn)
    apply hp
    simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at h ⊢
    exact (le_max_right _ _).trans h
  rw [cone_spatial_polar_integral _ hF,
    integral_fun_norm_addHaar volume (fun y => coneSpatialMean f (x, y))]
  have harea : (↑(Module.finrank ℝ Spatial) : ℝ) *
      (volume : Measure Spatial).real (Metric.ball 0 1) = 4 * π := by
    simpa only [coneSpatialSphereMeasure, Measure.toSphere_real_apply_univ,
      nsmul_eq_mul] using cone_spatial_sphere_area
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, harea, ← integral_smul]
  have hd : Module.finrank ℝ Spatial - 1 = 2 := by simp [Spatial]
  rw [hd]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  simp only [coneSpatialMean, smul_smul]
  congr 1
  have hne : 4 * π ≠ 0 := by positivity
  field_simp [hne]

private theorem cone_spatial_mean_lift_integrable {f : ℝ × Spatial → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) :
    Integrable (fun q : ℝ × Spatial => coneSpatialMean f (q.1, ‖q.2‖)) := by
  have hG := cone_spatial_mean_continuous hf hs
  obtain ⟨R, hR⟩ := hs.isBounded.subset_closedBall (0 : ℝ × Spatial)
  have H : Continuous (fun q : ℝ × Spatial => coneSpatialMean f (q.1, ‖q.2‖)) :=
    hG.comp (continuous_fst.prodMk (continuous_norm.comp continuous_snd))
  apply H.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × Spatial) R)
  intro q hq
  unfold coneSpatialMean
  have hz (ω : ConeSpatialSphere) : f (q.1, ‖q.2‖ • (ω : Spatial)) = 0 := by
    by_contra hn
    apply hq
    have h := hR (subset_tsupport f hn)
    simpa [Metric.mem_closedBall, dist_zero_right, Prod.norm_def,
      norm_smul, Real.norm_of_nonneg (norm_nonneg q.2), cone_spatial_direction_norm ω]
      using h
  simp [hz]

/-- The spatial angular averaging step on the intrinsic momentum chart.
This keeps the real axial variable independent of the positive spatial radius. -/
theorem cone_axial_spatial_integral {f : ℝ × Spatial → ℂ} (hf : Continuous f)
    (hs : HasCompactSupport f) :
    (∫ q : ℝ × Spatial, f q) =
      (4 * π) • ∫ q in univ ×ˢ Ioi (0 : ℝ), q.2 ^ 2 • coneSpatialMean f q := by
  have hG := cone_spatial_mean_continuous hf hs
  have hi := cone_spatial_mean_lift_integrable hf hs
  calc
    _ = ∫ x : ℝ, ∫ p : Spatial, f (x, p) := integral_prod _ (hf.integrable_of_hasCompactSupport hs)
    _ = ∫ x : ℝ, ∫ p : Spatial, coneSpatialMean f (x, ‖p‖) := by
      apply integral_congr_ae
      exact Eventually.of_forall (cone_spatial_mean_norm_eval hf hs)
    _ = ∫ q : ℝ × Spatial, coneSpatialMean f (q.1, ‖q.2‖) := (integral_prod _ hi).symm
    _ = _ := axial_spatial_radial_integral _ hG.aestronglyMeasurable hi

/-- The Cartesian four-momentum integral disintegrates into radial, polar
and spatial unit-sphere variables, retaining every angular dependence. -/
theorem cone_full_nonradial_polar_integral {f : ℝ × Spatial → ℂ} (hf : Continuous f)
    (hs : HasCompactSupport f) :
    (∫ q : ℝ × Spatial, f q) =
      (4 * π) • ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (0 : ℝ) π,
        (r ^ 3 * sin θ ^ 2) • coneSpatialMean f (r * cos θ, r * sin θ) := by
  have hG := cone_spatial_mean_continuous hf hs
  have hi := cone_spatial_mean_lift_integrable hf hs
  rw [cone_axial_spatial_integral hf hs, ← axial_spatial_radial_integral _ hG.aestronglyMeasurable hi]
  exact cone_polar_integral _ hG.aestronglyMeasurable hi

end UV.SectorPlane
