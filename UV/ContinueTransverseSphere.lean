import UV.AdvanceConeAngularGeometry
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Smooth spatial sphere averages for the two independent real normals
of a transverse pair of mass shells. The angular measure is the actual
unit-sphere measure on the locked momentum chart. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Metric Set
open scoped Topology

private theorem compact_parameter_integrable {S V : Type*} [TopologicalSpace S] [CompactSpace S]
    [MeasurableSpace S] [OpensMeasurableSpace S] {μ : Measure S} [IsFiniteMeasure μ]
    [NormedAddCommGroup V] {f : S → V} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem compact_parameter_average_continuous {H S V : Type*}
    [NormedAddCommGroup H] [ProperSpace H] [TopologicalSpace S] [CompactSpace S]
    [MeasurableSpace S] [OpensMeasurableSpace S] {μ : Measure S} [IsFiniteMeasure μ]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {F : H × S → V} (hf : Continuous F) : Continuous (fun x => ∫ ω, F (x,ω) ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let K := closedBall x (1:ℝ) ×ˢ (univ : Set S)
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_univ
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : S => M)
  · exact Eventually.of_forall fun y =>
      (compact_parameter_integrable (μ := μ) (hf.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  · filter_upwards [closedBall_mem_nhds x zero_lt_one] with y hy
    exact Eventually.of_forall fun ω => hM (y,ω) ⟨hy,mem_univ ω⟩
  · exact integrable_const _
  · exact Eventually.of_forall fun ω =>
      (hf.comp (continuous_id.prodMk continuous_const)).continuousAt.tendsto

private theorem compact_parameter_average_hasFDerivAt {H S V : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [TopologicalSpace S] [CompactSpace S] [MeasurableSpace S] [OpensMeasurableSpace S]
    {μ : Measure S} [IsFiniteMeasure μ] [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {F : H × S → V} {D : H × S → H →L[ℝ] V} (hf : Continuous F) (hd : Continuous D)
    (hD : ∀ x ω, HasFDerivAt (fun y => F (y,ω)) (D (x,ω)) x) (x : H) :
    HasFDerivAt (fun y => ∫ ω, F (y,ω) ∂μ) (∫ ω, D (x,ω) ∂μ) x := by
  let K := closedBall x (1:ℝ) ×ˢ (univ : Set S)
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_univ
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hd.continuousOn
  have hFi (y : H) : Integrable (fun ω => F (y,ω)) μ :=
    compact_parameter_integrable (hf.comp (continuous_const.prodMk continuous_id))
  have hDi : Integrable (fun ω => D (x,ω)) μ :=
    compact_parameter_integrable (hd.comp (continuous_const.prodMk continuous_id))
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y ω => F (y,ω)) (F' := fun y ω => D (y,ω))
    (ε := 1) (bound := fun _ => M) zero_lt_one
    (Eventually.of_forall fun y => (hFi y).aestronglyMeasurable) (hFi x) hDi.aestronglyMeasurable
    (Eventually.of_forall fun ω y hy => hM (y,ω) ⟨ball_subset_closedBall hy,mem_univ ω⟩)
    (integrable_const _) (Eventually.of_forall fun ω y _ => hD y ω)

private abbrev AxialRadial := ℝ × ℝ

private def sphereRayMap (w : Spatial) : AxialRadial →L[ℝ] (ℝ × Spatial) :=
  (ContinuousLinearMap.inl ℝ ℝ Spatial).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) +
    (ContinuousLinearMap.inr ℝ ℝ Spatial).comp ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight w)

private theorem sphere_ray_map_apply (w : Spatial) (z : AxialRadial) :
    sphereRayMap w z = (z.1, z.2 • w) := by
  simp [sphereRayMap]

private theorem sphere_ray_map_continuous : Continuous sphereRayMap := by
  unfold sphereRayMap
  exact continuous_const.add
    (((ContinuousLinearMap.smulRightL ℝ AxialRadial Spatial)
      (ContinuousLinearMap.snd ℝ ℝ ℝ)).continuous.const_clm_comp (ContinuousLinearMap.inr ℝ ℝ Spatial))

/-- Spatial averaging preserves two full Cartesian derivatives. In
particular this includes the mixed derivative in the axial and radial
slots needed for the two-normal test function. -/
theorem cone_spatial_mean_contDiff {f : ℝ × Spatial → ℂ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (coneSpatialMean f) := by
  letI : CompactSpace ConeSpatialSphere := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let L (ω : ConeSpatialSphere) := sphereRayMap (ω : Spatial)
  let X := ℝ × Spatial
  let df := fderiv ℝ f
  let Lc (ω : ConeSpatialSphere) := (ContinuousLinearMap.compL ℝ AxialRadial X ℂ).flip (L ω)
  let F (p : AxialRadial × ConeSpatialSphere) := f (L p.2 p.1)
  let D (p : AxialRadial × ConeSpatialSphere) := Lc p.2 (df (L p.2 p.1))
  let DD (p : AxialRadial × ConeSpatialSphere) :=
    ((Lc p.2).comp (fderiv ℝ df (L p.2 p.1))).comp (L p.2)
  have hcL : Continuous L := sphere_ray_map_continuous.comp continuous_subtype_val
  have hcLc : Continuous Lc :=
    (ContinuousLinearMap.compL ℝ AxialRadial X ℂ).flip.continuous.comp hcL
  have hcR : Continuous (fun p : AxialRadial × ConeSpatialSphere => L p.2 p.1) :=
    (hcL.comp continuous_snd).clm_apply continuous_fst
  have hdf : ContDiff ℝ 1 df := (contDiff_succ_iff_fderiv (n := 1)).mp hf |>.2.2
  have hF : Continuous F := hf.continuous.comp hcR
  have hD : Continuous D := (hcLc.comp continuous_snd).clm_apply (hdf.continuous.comp hcR)
  have hDD : Continuous DD :=
    ((hcLc.comp continuous_snd).clm_comp ((hdf.continuous_fderiv le_rfl).comp hcR)).clm_comp
      (hcL.comp continuous_snd)
  have h₁ (z : AxialRadial) (ω : ConeSpatialSphere) : HasFDerivAt (fun y => F (y,ω)) (D (z,ω)) z :=
    ((hf.differentiable (by norm_num) (L ω z)).hasFDerivAt).comp z (L ω).hasFDerivAt
  have h₂ (z : AxialRadial) (ω : ConeSpatialSphere) : HasFDerivAt (fun y => D (y,ω)) (DD (z,ω)) z :=
    (Lc ω).hasFDerivAt.comp z (((hdf.differentiable le_rfl _).hasFDerivAt).comp z (L ω).hasFDerivAt)
  let A (z : AxialRadial) := ∫ ω, F (z,ω) ∂coneSpatialSphereMeasure
  let B (z : AxialRadial) := ∫ ω, D (z,ω) ∂coneSpatialSphereMeasure
  let C (z : AxialRadial) := ∫ ω, DD (z,ω) ∂coneSpatialSphereMeasure
  have hA (z : AxialRadial) : HasFDerivAt A (B z) z :=
    compact_parameter_average_hasFDerivAt hF hD h₁ z
  have hB (z : AxialRadial) : HasFDerivAt B (C z) z :=
    compact_parameter_average_hasFDerivAt hD hDD h₂ z
  have hCa : Continuous C := compact_parameter_average_continuous hDD
  have hdiff : ContDiff ℝ 2 A := by
    apply (contDiff_succ_iff_fderiv (n := 1)).mpr
    refine ⟨fun z => (hA z).differentiableAt, by norm_num,?_⟩
    rw [show fderiv ℝ A = B from funext fun z => (hA z).fderiv]
    apply contDiff_one_iff_fderiv.mpr
    exact ⟨fun z => (hB z).differentiableAt,(show fderiv ℝ B = C from funext fun z => (hB z).fderiv) ▸ hCa⟩
  have hav : coneSpatialMean f = fun z => (4 * Real.pi)⁻¹ • A z := by
    funext z
    simp [coneSpatialMean,A,F,L,sphere_ray_map_apply]
  rw [hav]
  exact contDiff_const.smul hdiff

end UV.SectorPlane
