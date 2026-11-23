import UV.ContinueWilsonLinkMarks
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! The full rank-four pushforward density for the pair of independent
A4 marks and its exact use in the charged Wilson operator. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter Metric
open scoped Topology ENNReal Matrix RealInnerProductSpace

namespace UV

variable {ι : Type*} [Fintype ι]

/-- Pulling real four-volume null sets back through the rank-four readout
gives shell-volume null sets. Averaging over translations along its
isometric right inverse allows a direct Tonelli argument in every dimension. -/
theorem wilson_adjoint_readout_quasi (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    QuasiMeasurePreserving T.toContinuousLinearMap.adjoint volume volume := by
  let R := T.toContinuousLinearMap.adjoint
  have hRT (x : OSFourSpace) : R (T x) = x := by
    have h := T.toContinuousLinearMap.norm_map_iff_adjoint_comp_self.mp T.norm_map
    exact congrArg (fun f : OSFourSpace →L[ℝ] OSFourSpace => f x) h
  refine ⟨R.continuous.measurable, AbsolutelyContinuous.mk (fun S hS hnull => ?_)⟩
  let U := (fun p : OSFourSpace × WilsonBallSpace ι => R (p.2 + T p.1)) ⁻¹' S
  have hU : MeasurableSet U := (R.continuous.comp (continuous_snd.add (T.continuous.comp continuous_fst))).measurable hS
  let ν := wilsonBallMeasure (Fin 4)
  have hν : ν ≪ volume := cond_absolutelyContinuous
  have hzero : ν.prod (volume : Measure (WilsonBallSpace ι)) U = 0 := by
    rw [Measure.prod_apply_symm hU]
    have hz (y : WilsonBallSpace ι) : ν ((fun x => (x,y)) ⁻¹' U) = 0 := by
      have hs : (fun x => (x,y)) ⁻¹' U = (R y+·) ⁻¹' S := by ext x; simp [U,hRT]
      rw [hs]
      exact hν (((measurePreserving_add_left (volume : Measure OSFourSpace) (R y)).measure_preimage hS.nullMeasurableSet).trans hnull)
    simp only [hz,lintegral_zero]
  have hx (x : OSFourSpace) : (volume : Measure (WilsonBallSpace ι)) (Prod.mk x ⁻¹' U) = volume (R ⁻¹' S) :=
    (measurePreserving_add_right volume (T x)).measure_preimage (R.continuous.measurable hS).nullMeasurableSet
  rw [Measure.prod_apply hU] at hzero
  simp only [hx,lintegral_const,measure_univ,mul_one] at hzero
  rw [Measure.map_apply R.continuous.measurable hS]
  exact hzero

def wilsonDisplacementMeasure (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) : Measure OSFourSpace :=
  ((wilsonBallMeasure ι).prod (wilsonBallMeasure ι)).map (wilsonPairDisplacement L T)

theorem wilson_displacement_continuous (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    Continuous (wilsonPairDisplacement L T) :=
  continuous_const.smul (T.toContinuousLinearMap.adjoint.continuous.comp (continuous_fst.add continuous_snd))

instance wilsonDisplacementProbability {L : ℝ} {T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι} :
    IsProbabilityMeasure (wilsonDisplacementMeasure L T) :=
  Measure.isProbabilityMeasure_map (wilson_displacement_continuous L T).measurable.aemeasurable

theorem wilson_displacement_absolutely_continuous {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    wilsonDisplacementMeasure L T ≪ volume := by
  have hβ : wilsonBallMeasure ι ≪ volume := cond_absolutelyContinuous
  have h := (Measure.quasiMeasurePreserving_smul (volume : Measure OSFourSpace) hL.ne').comp
    ((wilson_adjoint_readout_quasi T).comp (quasiMeasurePreserving_add (volume : Measure (WilsonBallSpace ι)) volume))
  exact (h.mono_left (hβ.prod hβ)).absolutelyContinuous

def wilsonDisplacementDensity (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (d : OSFourSpace) : ℝ≥0∞ :=
  (wilsonDisplacementMeasure L T).rnDeriv volume d

theorem wilson_displacement_density_eq {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    volume.withDensity (wilsonDisplacementDensity L T) = wilsonDisplacementMeasure L T :=
  Measure.withDensity_rnDeriv_eq _ _ (wilson_displacement_absolutely_continuous hL T)

theorem wilson_displacement_band {L : ℝ} (hL : 0 ≤ L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    ∀ᵐ d ∂wilsonDisplacementMeasure L T, ‖d‖ ≤ 2*L := by
  apply (ae_map_iff (wilson_displacement_continuous L T).measurable.aemeasurable
    (measurableSet_le measurable_norm measurable_const)).mpr
  have hb : ∀ᵐ y ∂wilsonBallMeasure ι, y ∈ ball (0:WilsonBallSpace ι) 1 := ae_cond_mem measurableSet_ball
  filter_upwards [(quasiMeasurePreserving_fst (ν := wilsonBallMeasure ι)).ae hb,
    (quasiMeasurePreserving_snd (μ := wilsonBallMeasure ι)).ae hb] with y hy hy'
  apply wilson_pair_displacement_bound hL T y
  · exact (show ‖y.1‖ < 1 by simpa only [mem_ball,dist_zero_right] using hy).le
  · exact (show ‖y.2‖ < 1 by simpa only [mem_ball,dist_zero_right] using hy').le

theorem wilson_displacement_density_mass {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    ∫⁻ d, wilsonDisplacementDensity L T d = 1 := by
  have h := congrArg (fun μ : Measure OSFourSpace => μ univ) (wilson_displacement_density_eq hL T)
  simpa only [withDensity_apply _ MeasurableSet.univ,restrict_univ,measure_univ] using h

/-- The ordinary Euclidean characteristic function carries the angular
frequency convention exp(i p·d). Two independent marks give the square
of the normalized, single-ball characteristic function at LTp. -/
theorem wilson_displacement_characteristic (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (p : OSFourSpace) :
    ∫ d, Complex.exp (Complex.I*(⟪p,d⟫:ℝ)) ∂wilsonDisplacementMeasure L T =
      (∫ y, Complex.exp (Complex.I*(⟪L • T p,y⟫:ℝ)) ∂wilsonBallMeasure ι)^2 := by
  rw [wilsonDisplacementMeasure,integral_map (wilson_displacement_continuous L T).measurable.aemeasurable
    (show Continuous (fun d : OSFourSpace => Complex.exp (Complex.I*(⟪p,d⟫:ℝ))) by fun_prop).aestronglyMeasurable,
    pow_two,←integral_prod_mul]
  congr 1
  funext y
  rw [wilsonPairDisplacement,real_inner_smul_right,T.toContinuousLinearMap.adjoint_inner_right,
    inner_add_right,real_inner_smul_left,real_inner_smul_left,←Complex.exp_add]
  push_cast
  ring_nf
  rfl

/-- The charged hop written with the actual normalized four-volume density
h(d), the complete spin factor, the straight Wilson link and the translated
spinor. The integrand is tested on measurable spinors and continuous links. -/
theorem wilson_density_hop_integral {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (B : WilsonConnection) (ψ : OSFourSpace → WilsonSpinor) (x : OSFourSpace) (i : Fin 4)
    (h : StronglyMeasurable (fun d => wilsonLinkPhase B x d * (wilsonSpinWeight L d *ᵥ ψ (x+d)) i)) :
    wilsonGaugedHop L T B ψ x i = ∫ d, ((wilsonDisplacementDensity L T d).toReal:ℂ) *
      (wilsonLinkPhase B x d * (wilsonSpinWeight L d *ᵥ ψ (x+d)) i) := by
  let G := fun d => wilsonLinkPhase B x d * (wilsonSpinWeight L d *ᵥ ψ (x+d)) i
  have he : wilsonGaugedHop L T B ψ x i = ∫ d, G d ∂wilsonDisplacementMeasure L T :=
    (integral_map (wilson_displacement_continuous L T).measurable.aemeasurable h.aestronglyMeasurable).symm
  rw [he]
  exact (integral_rnDeriv_smul (f := G) (wilson_displacement_absolutely_continuous hL T)).symm

theorem wilson_line_measurable {B : WilsonConnection} (hB : Continuous B) (x : OSFourSpace) :
    Measurable (wilsonLineIntegral B x) := by
  have h : Continuous (fun p : OSFourSpace × ℝ => B (x+p.2 • p.1) p.1) :=
    (hB.comp (continuous_const.add (continuous_snd.smul continuous_fst))).clm_apply continuous_fst
  change Measurable (fun d => ∫ t in (0:ℝ)..1, B (x+t • d) d)
  simp only [intervalIntegral.integral_of_le zero_le_one]
  exact (h.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0:ℝ) 1))).measurable

/-- The density identity applies directly to continuous real connections and
measurable spinors, component by component. -/
theorem wilson_density_hop_for_fields {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    {B : WilsonConnection} (hB : Continuous B) {ψ : OSFourSpace → WilsonSpinor} (hψ : Measurable ψ)
    (x : OSFourSpace) (i : Fin 4) :
    wilsonGaugedHop L T B ψ x i = ∫ d, ((wilsonDisplacementDensity L T d).toReal:ℂ) *
      (wilsonLinkPhase B x d * (wilsonSpinWeight L d *ᵥ ψ (x+d)) i) := by
  apply wilson_density_hop_integral hL T
  apply Measurable.stronglyMeasurable
  have hphase : Measurable (wilsonLinkPhase B x) := Complex.continuous_exp.measurable.comp
    (measurable_const.mul (Complex.continuous_ofReal.measurable.comp (wilson_line_measurable hB x)))
  apply hphase.mul
  simp only [wilsonSpinWeight,diracSlash,Matrix.mulVec,dotProduct,Matrix.sub_apply,Matrix.smul_apply,
    Matrix.sum_apply,smul_eq_mul]
  have hψ' (j : Fin 4) : Measurable (fun d => ψ (x+d) j) :=
    (measurable_pi_apply j).comp (hψ.comp (continuous_const.add continuous_id).measurable)
  fun_prop (disch := assumption)

private theorem wilson_spin_component_continuous {ψ : OSFourSpace → WilsonSpinor} (hψ : Continuous ψ)
    (L : ℝ) (x : OSFourSpace) (i : Fin 4) :
    Continuous (fun d : OSFourSpace => (wilsonSpinWeight L d *ᵥ ψ (x+d)) i) := by
  have hψ' (j : Fin 4) : Continuous (fun d => ψ (x+d) j) :=
    (continuous_apply j).comp (hψ.comp (continuous_const.add continuous_id))
  simp only [wilsonSpinWeight,diracSlash,Matrix.mulVec,dotProduct,Matrix.sub_apply,Matrix.smul_apply,
    Matrix.sum_apply,smul_eq_mul]
  apply continuous_finset_sum
  intro j _
  apply Continuous.mul _ (hψ' j)
  apply Continuous.sub continuous_const
  apply continuous_const.mul
  apply continuous_finset_sum
  intro k _
  exact (Complex.continuous_ofReal.comp (EuclideanSpace.proj k).continuous).mul continuous_const

/-- Continuous spinor probes give an absolutely integrable component of
the actual hop. Compact support of the displacement law suffices even
when the spinor is unbounded at infinity. -/
theorem wilson_density_hop_integrable {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    {B : WilsonConnection} (hB : Continuous B) {ψ : OSFourSpace → WilsonSpinor} (hψ : Continuous ψ)
    (x : OSFourSpace) (i : Fin 4) :
    Integrable (fun d => ((wilsonDisplacementDensity L T d).toReal:ℂ) *
      (wilsonLinkPhase B x d * (wilsonSpinWeight L d *ᵥ ψ (x+d)) i)) := by
  let F := fun d => (wilsonSpinWeight L d *ᵥ ψ (x+d)) i
  have hc : Continuous F := wilson_spin_component_continuous hψ L x i
  have hm : ∀ᵐ d ∂wilsonDisplacementMeasure L T, d ∈ closedBall 0 (2*L) := by
    simpa only [mem_closedBall,dist_zero_right] using wilson_displacement_band hL.le T
  have hi := hc.continuousOn.integrableOn_compact (μ := wilsonDisplacementMeasure L T) (isCompact_closedBall 0 (2*L))
  rw [IntegrableOn,Measure.restrict_eq_self_of_ae_mem hm] at hi
  have hp : Measurable (wilsonLinkPhase B x) := Complex.continuous_exp.measurable.comp
    (measurable_const.mul (Complex.continuous_ofReal.measurable.comp (wilson_line_measurable hB x)))
  apply (integrable_rnDeriv_smul_iff (wilson_displacement_absolutely_continuous hL T)).mpr
  apply hi.norm.mono' (hp.mul hc.measurable).aestronglyMeasurable
  exact Eventually.of_forall (fun d => by simp [wilson_link_unit_modulus,F])

end UV
