import UV.ContinueHeatMaxwellSignResponse
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The native transverse coefficient in the original four-dimensional plane
volume, its Haar angular integral and the substitution u = ‖k‖². -/

noncomputable section
open MeasureTheory Set Metric Real UV.SectorPlane UV.RelativeSoft
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace UV.HeatMaxwell

private theorem heat_radial_square (H : ℝ → ℝ) :
    (∫ r in Ioi (0:ℝ), r^3 * H (r^2)) = (1/2:ℝ)*(∫ u in Ioi (0:ℝ), u*H u) := by
  let G := fun u : ℝ => (1/2)*(u*H u)
  have h := integral_comp_rpow_Ioi G (p := 2) (by norm_num)
  rw [←integral_const_mul]
  change _ = ∫ u in Ioi 0, G u
  rw [←h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  dsimp [G]
  norm_num
  ring

theorem heat_polar_chart {f : ScalarMomentum → ℝ} (hi : Integrable f) :
    (∫ k, f k) = ∫ r in Ioi (0:ℝ), r^3 * ∫ n : HeatUnitSphere, f (r • n.1)
      ∂(volume : Measure ScalarMomentum).toSphere := by
  let μ : Measure ScalarMomentum := volume
  let e := (homeomorphUnitSphereProd ScalarMomentum).toMeasurableEquiv
  have hp : MeasurePreserving e (μ.comap Subtype.val) (μ.toSphere.prod (Measure.volumeIoiPow 3)) := by
    simpa only [finrank_euclideanSpace,Fintype.card_fin,Nat.reduceSub] using μ.measurePreserving_homeomorphUnitSphereProd
  let g := fun p : HeatUnitSphere × Ioi (0:ℝ) => f ((p.2:ℝ) • p.1.1)
  have he : (fun p => f (e.symm p).1) = g := by
    funext p
    exact congrArg f (homeomorphUnitSphereProd_symm_apply_coe _ _)
  have hi' : Integrable (fun v : ({(0:ScalarMomentum)}ᶜ : Set ScalarMomentum) => f v.1) (μ.comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).1 hi.integrableOn
  have hgp := ((MeasurePreserving.symm e hp).integrable_comp_emb e.symm.measurableEmbedding).2 hi'
  have h := (MeasurePreserving.symm e hp).integral_comp e.symm.measurableEmbedding
    (fun v : ({(0:ScalarMomentum)}ᶜ : Set ScalarMomentum) => f v.1)
  rw [integral_subtype_comap (measurableSet_singleton _).compl f, restrict_compl_singleton] at h
  change (∫ k, f k ∂μ) = _
  rw [←h,he]
  have hg : Integrable g (μ.toSphere.prod (Measure.volumeIoiPow 3)) := by simpa only [Function.comp_def,he] using hgp
  rw [integral_prod_symm g hg]
  unfold Measure.volumeIoiPow
  have hm : Measurable (fun r : Ioi (0:ℝ) => Real.toNNReal (r.1^3)) :=
    (measurable_subtype_coe.pow_const _).real_toNNReal
  simp_rw [ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul hm,
    integral_subtype_comap measurableSet_Ioi (fun r : ℝ => Real.toNNReal (r^3) • ∫ n : HeatUnitSphere, f (r • n.1) ∂μ.toSphere)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [NNReal.smul_def,Real.coe_toNNReal _ (pow_nonneg hr.le _),smul_eq_mul]

local instance polarSectorMeasurable : MeasurableSpace EuclideanPlaneMomentum := borel _
local instance polarSectorBorel : BorelSpace EuclideanPlaneMomentum := ⟨rfl⟩

def heatSectorQuadratic (m a : ℝ) (k : EuclideanPlaneMomentum) : ℝ :=
  heatTwoMarkQuadratic (‖k‖^2) ⟪k,softLongitudinal.val⟫ ⟪k,softTransverse.val⟫
    (heatNormalizedGaussian ((m*a)^2) (‖k‖^2))

theorem heat_sector_polar_coefficient (m a : ℝ) (hi : Integrable (heatSectorQuadratic m a)) :
    (4/(2*Real.pi)^4)*(∫ k, heatSectorQuadratic m a k) = heatTransverseSoftCoefficient m a := by
  let f := fun y : ScalarMomentum => heatTwoMarkQuadratic (‖y‖^2) (y 1) (y 2)
    (heatNormalizedGaussian ((m*a)^2) (‖y‖^2))
  have he (k : EuclideanPlaneMomentum) : f (heatSectorCoordinates k) = heatSectorQuadratic m a k := by
    simp only [f,heatSectorQuadratic,heatSectorCoordinates.norm_map,heatSectorCoordinates_longitudinal,
      heatSectorCoordinates_transverse]
  have hf : Integrable f := (heatSectorCoordinates.measurePreserving.integrable_comp_emb
    heatSectorCoordinates.toHomeomorph.measurableEmbedding).1 (by simpa only [Function.comp_def,he] using hi)
  have hc := heatSectorCoordinates.measurePreserving.integral_comp heatSectorCoordinates.toHomeomorph.measurableEmbedding f
  simp only [he] at hc
  rw [hc,heat_polar_chart hf]
  let H := fun u : ℝ => ∫ n : HeatUnitSphere,
    heatTwoMarkQuadratic u (Real.sqrt u*n.1 1) (Real.sqrt u*n.1 2)
      (heatNormalizedGaussian ((m*a)^2) u) ∂(volume : Measure ScalarMomentum).toSphere
  have hrad (r : ℝ) (hr : r ∈ Ioi (0:ℝ)) :
      (∫ n : HeatUnitSphere, f (r • n.1) ∂(volume : Measure ScalarMomentum).toSphere) = H (r^2) := by
    change 0<r at hr
    apply integral_congr_ae
    filter_upwards with n
    have hnorm : ‖n.1‖ = 1 := mem_sphere_zero_iff_norm.mp n.2
    simp only [f,norm_smul,Real.norm_eq_abs,abs_of_pos hr,hnorm,mul_one,Real.sqrt_sq hr.le,
      PiLp.smul_apply, smul_eq_mul]
  have hr : (∫ r in Ioi (0:ℝ), r^3 * ∫ n : HeatUnitSphere, f (r • n.1) ∂(volume : Measure ScalarMomentum).toSphere) =
      ∫ r in Ioi (0:ℝ), r^3*H (r^2) := setIntegral_congr_fun measurableSet_Ioi (fun r hr => by rw [hrad r hr])
  rw [hr,heat_radial_square]
  unfold heatTransverseSoftCoefficient
  dsimp only [H]
  ring

end UV.HeatMaxwell
