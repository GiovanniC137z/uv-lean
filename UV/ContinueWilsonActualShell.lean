import UV.ContinueWilsonShellFourier
import UV.ContinueWilsonPhotonSewing

/-! The physical one-mark shell itself is square integrable on the
rank-four readout. Its two incidences supply the completed photon sewing. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter Metric UV.SectorPlane
open scoped Topology RealInnerProductSpace ENNReal

namespace UV

variable {ι : Type*} [Fintype ι]

def wilsonSingleLaw (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) : Measure OSFourSpace :=
  (wilsonBallMeasure ι).map (wilsonSingleDisplacement L T)

instance wilsonSingleProbability {L : ℝ} {T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι} :
    IsProbabilityMeasure (wilsonSingleLaw L T) :=
  Measure.isProbabilityMeasure_map (wilsonSingleDisplacement L T).continuous.measurable.aemeasurable

theorem wilson_single_support {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    ∀ᵐ x ∂wilsonSingleLaw L T, x ∈ closedBall 0 L := by
  apply (ae_map_iff (wilsonSingleDisplacement L T).continuous.measurable.aemeasurable measurableSet_closedBall).mpr
  filter_upwards [(ProbabilityTheory.ae_cond_mem (μ := (volume : Measure (WilsonBallSpace ι))) (s := ball 0 1) measurableSet_ball)] with y hy
  rw [dist_zero_right]
  have h := T.toContinuousLinearMap.adjoint.le_opNorm y
  rw [LinearIsometryEquiv.norm_map,T.norm_toContinuousLinearMap,one_mul] at h
  have hy' : ‖y‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hy
  simp only [wilsonSingleDisplacement,ContinuousLinearMap.smul_apply,norm_smul,Real.norm_of_nonneg hL.le]
  nlinarith [mul_lt_mul_of_pos_left (h.trans_lt hy') hL]

theorem wilson_pair_sum_law (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    wilsonDisplacementMeasure L T =
      ((wilsonSingleLaw L T).prod (wilsonSingleLaw L T)).map (fun z => z.1+z.2) := by
  let R := wilsonSingleDisplacement L T
  have hh : MeasurePreserving R (wilsonBallMeasure ι) (wilsonSingleLaw L T) := ⟨R.continuous.measurable,rfl⟩
  have hp := hh.prod hh
  rw [wilsonDisplacementMeasure,←hp.map_eq,Measure.map_map (measurable_fst.add measurable_snd) hp.measurable]
  congr 1
  funext z
  exact map_add R z.1 z.2

theorem wilson_continuous_single_L2 {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    {f : OSFourSpace → ℂ} (hf : Continuous f) : MemLp (wilsonMarkedTransform (wilsonSingleLaw L T) f) 2 volume := by
  obtain ⟨C,hC,hμ⟩ := wilson_single_density_bound hL T
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0:OSFourSpace) L).bddAbove_image hf.norm.continuousOn
  have hb : ∀ᵐ x ∂wilsonSingleLaw L T, ‖f x‖ ≤ max B 0 := by
    filter_upwards [wilson_single_support hL T] with x hx
    exact (hB ⟨x,hx,rfl⟩).trans (le_max_left _ _)
  apply (memLp_two_iff_integrable_sq_norm (wilson_marked_transform_measurable _ hf.measurable).aestronglyMeasurable).mpr
  exact wilson_marked_transform_square_integrable (wilsonSingleLaw L T) hμ hC hf.measurable (le_max_right _ _) hb

def wilsonShellPhotonForm (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (p : OSFourSpace) : ℂ :=
  ∫ y, Complex.exp (Complex.I*(⟪L • T p,y⟫:ℝ)) ∂wilsonBallMeasure ι

theorem wilson_shell_photon_transform (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    wilsonShellPhotonForm L T = wilsonMarkedTransform (wilsonSingleLaw L T) (fun _ => 1) := by
  funext p
  unfold wilsonShellPhotonForm wilsonMarkedTransform wilsonSingleLaw
  rw [integral_map (wilsonSingleDisplacement L T).continuous.measurable.aemeasurable
    (show Continuous (fun x : OSFourSpace => thinPlaneWave p x * 1) by unfold thinPlaneWave; fun_prop).aestronglyMeasurable]
  congr 1
  funext y
  simp only [mul_one,thinPlaneWave,wilsonSingleDisplacement,ContinuousLinearMap.smul_apply,
    real_inner_smul_right,real_inner_smul_left,T.toContinuousLinearMap.adjoint_inner_right]
  rfl

theorem wilson_actual_shell_square_integrable {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    Integrable (fun p => ‖wilsonShellPhotonForm L T p‖^2) := by
  simp only [wilson_shell_photon_transform]
  have hc := wilson_continuous_single_L2 hL T (continuous_const (y := (1:ℂ)))
  exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mp hc

theorem wilson_actual_shell_sewing {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (d e : ℕ → ThinCurrentPlane) (N M : ℕ) (hc : wilsonPolygonStart d N = 0) (hc' : wilsonPolygonStart e M = 0) :
    Integrable (wilsonSewnPhoton (wilsonShellPhotonForm L T) d e N M) :=
  wilson_sewn_photon_integrable (wilson_actual_shell_square_integrable hL T) d e N M hc hc'

theorem wilson_actual_independent_photons {κ : Type*} [Fintype κ] {L : ℝ} (hL : 0 < L)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (d e : κ → ℕ → ThinCurrentPlane) (N M : κ → ℕ)
    (hc : ∀ j, wilsonPolygonStart (d j) (N j) = 0) (hc' : ∀ j, wilsonPolygonStart (e j) (M j) = 0) :
    Integrable (fun q : κ → ThinCurrentPlane => ∏ j, wilsonSewnPhoton (wilsonShellPhotonForm L T) (d j) (e j) (N j) (M j) (q j))
      (Measure.pi (fun _ => volume)) :=
  wilson_independent_sewn_photons (fun _ => wilson_actual_shell_square_integrable hL T) d e N M hc hc'

end UV
