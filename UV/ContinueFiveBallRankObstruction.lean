import UV.ContinueNormalRankGraph
import UV.ContinueFiveBallSharp

/-! The continuum single-photon majorant with an A4 readout of rank
at most two. A whole kernel fibre of dimension at least two is left
undamped. Escaping balls quantify its logarithmic or stronger UV tail. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Metric
open scoped Topology InnerProductSpace RealInnerProductSpace ENNReal

namespace UV

/-- A translated ball of radius R, centered three radii from the
origin, carries uniformly positive mass under the inverse-square weight
in every real dimension d ≥ 2. -/
theorem normal_inverse_square_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (hd : 2 ≤ Module.finrank ℝ E) :
    ¬ Integrable (normalPhotonWeight (E := E) 2) μ := by
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨u,hu⟩ := exists_norm_eq E (by norm_num : (0:ℝ) ≤ 1)
  let B := fun R : ℝ => ball ((3*R) • u) R
  let f := normalPhotonWeight (E := E) 2
  have hn (x) : 0 ≤ f x := by dsimp [f,normalPhotonWeight]; positivity
  intro hi
  have hc (R : ℝ) (hR : 0 ≤ R) : ‖(3*R) • u‖ = 3*R := by simp [norm_smul,hu,abs_of_nonneg hR]
  have hbig (R : ℝ) (hR : 1 ≤ R) (x : E) (hx : x ∈ B R) : 2*R ≤ ‖x‖ ∧ ‖x‖ ≤ 4*R := by
    have h := abs_norm_sub_norm_le x ((3*R) • u)
    rw [hc R (by linarith)] at h
    have hlt : ‖x-(3*R) • u‖ < R := by simpa only [B,mem_ball,dist_eq_norm] using hx
    have hp := abs_lt.mp (h.trans_lt hlt)
    constructor <;> linarith [hp.1,hp.2]
  have he (R) : MeasurableSet (B R) := measurableSet_ball
  have hlim : Tendsto (fun R => ∫ x, (B R).indicator f x ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (l := atTop) (F := fun R => (B R).indicator f) (f := fun _ => (0:ℝ)) f
      (Eventually.of_forall fun R => (hi.indicator (he R)).aestronglyMeasurable)
      (Eventually.of_forall fun R => Eventually.of_forall fun x => by
        by_cases hx : x ∈ B R <;> simp [hx,Real.norm_of_nonneg (hn x),hn x]) hi
      (Eventually.of_forall fun x => ?_)
    · simpa using h
    · apply tendsto_nhds_of_eventually_eq
      filter_upwards [eventually_ge_atTop (max 1 (‖x‖+1))] with R hR
      have h1 := (le_max_left _ _).trans hR
      have h2 := (le_max_right _ _).trans hR
      exact indicator_of_notMem (fun hx => by linarith [(hbig R h1 x hx).1,norm_nonneg x]) _
  let v := μ.real (ball (0:E) 1)
  have hv : 0 < v := ENNReal.toReal_pos (measure_ball_pos μ 0 zero_lt_one).ne' measure_ball_ne_top
  have hlow : ∀ᶠ R : ℝ in atTop, v/25 ≤ ∫ x, (B R).indicator f x ∂μ := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
    have hR' : 0 < R := by linarith
    have hvol : μ.real (B R) = R^(Module.finrank ℝ E)*v := by
      simp only [B,v,measureReal_def,Measure.addHaar_ball_of_pos μ _ hR',ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg hR'.le _)]
    have hpow : R^2 ≤ R^(Module.finrank ℝ E) := pow_le_pow_right₀ hR hd
    rw [integral_indicator (he R)]
    calc v/25 ≤ μ.real (B R) * ((1+4*R)^2)⁻¹ := by
           rw [hvol,←div_eq_mul_inv,div_le_div_iff₀ (by norm_num) (by positivity)]
           have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 1+4*R) (by linarith : 1+4*R ≤ 5*R) 2
           nlinarith [mul_le_mul_of_nonneg_left hsq hv.le,mul_le_mul_of_nonneg_right hpow hv.le]
         _ = ∫ _ in B R, ((1+4*R)^2)⁻¹ ∂μ := (setIntegral_const _).symm
         _ ≤ _ := by
           apply setIntegral_mono_on (integrableOn_const (hs := measure_ball_ne_top)) hi.integrableOn (he R)
           intro x hx
           apply inv_anti₀ (by positivity : 0 < (1+‖x‖)^2)
           exact pow_le_pow_left₀ (by positivity) (by linarith [(hbig R hR x hx).2]) 2
  have hzero := le_of_tendsto_of_tendsto tendsto_const_nhds hlim hlow
  linarith

/-- Rank at most two leaves an undamped kernel of dimension at least two.
Continuity and the exact normalization at zero give a positive-measure
family of divergent fibres, even for the infrared-regularized envelope. -/
theorem normal_low_rank_photon_soft {ι : Type*} [Fintype ι] (L : ℝ)
    (T : OSFourSpace →L[ℝ] WilsonBallSpace ι) (hr : Module.finrank ℝ (LinearMap.range T.toLinearMap) ≤ 2) :
    ¬ Integrable (fun p => ‖normalPhotonForm L T p‖^2 * normalPhotonWeight 2 p) := by
  let K := LinearMap.ker T.toLinearMap
  let S := Kᗮ
  have hd : 2 ≤ Module.finrank ℝ K := by
    have h := T.toLinearMap.finrank_range_add_finrank_ker
    rw [finrank_euclideanSpace_fin] at h
    dsimp only [K]
    omega
  let U := (S.prodEquivOfIsCompl K K.isCompl_orthogonal_of_hasOrthogonalProjection.symm).toContinuousLinearEquiv
  let μ := (volume : Measure S).prod (volume : Measure K)
  let g := fun v:S => normalPhotonForm L T (v : OSFourSpace)
  let f := fun p => ‖normalPhotonForm L T p‖^2 * normalPhotonWeight 2 p
  have hfc : Continuous f := by
    dsimp only [f,normalPhotonWeight]
    exact ((normal_photon_form_continuous L T).norm.pow 2).mul (((continuous_const.add continuous_norm).pow 2).inv₀ fun p => by positivity)
  have hgc : Continuous g := (normal_photon_form_continuous L T).comp continuous_subtype_val
  have hg0 : g 0 = 1 := by simp [g,normalPhotonForm,normalShellCharacteristic]
  have hpos := hgc.isOpen_support.measure_pos (volume : Measure S) ⟨0, hg0.trans_ne one_ne_zero⟩
  intro hi
  haveI : IsAddHaarMeasure (μ.map U) := U.isAddHaarMeasure_map μ
  have hI : Integrable (f ∘ U) μ := by
    apply (integrable_map_measure hfc.aestronglyMeasurable U.continuous.aemeasurable).mp
    rw [isAddLeftInvariant_eq_smul (μ.map U) volume]
    exact hi.smul_measure ENNReal.coe_ne_top
  obtain ⟨v,hv,hk⟩ := exists_mem_of_measure_ne_zero_of_ae hpos.ne' (ae_restrict_of_ae hI.prod_right_ae)
  have hn : ‖g v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hfibre (k:K) : normalPhotonForm L T (U (v,k)) = g v := by
    change normalShellCharacteristic (L • T ((v:OSFourSpace)+(k:OSFourSpace))) = _
    rw [map_add,show T k.val=0 from k.property,add_zero]
    rfl
  let c := (1+‖v‖)^2 / ‖g v‖^2
  apply normal_inverse_square_tail (E := K) volume hd
  apply (hk.const_mul c).mono' (show Measurable (fun k:K => ((1+‖k‖)^2)⁻¹) by fun_prop).aestronglyMeasurable
  refine Eventually.of_forall fun k => ?_
  change ‖normalPhotonWeight 2 k‖ ≤ c*f (U (v,k))
  rw [Real.norm_of_nonneg (by dsimp [normalPhotonWeight]; positivity)]
  change normalPhotonWeight 2 k ≤ c*(‖normalPhotonForm L T (U (v,k))‖^2*normalPhotonWeight 2 (U (v,k)))
  rw [hfibre,←mul_assoc,show c*‖g v‖^2 = (1+‖v‖)^2 from div_mul_cancel₀ _ (pow_ne_zero _ hn)]
  change normalPhotonWeight 2 (k:OSFourSpace) ≤ _*normalPhotonWeight 2 ((v:OSFourSpace)+(k:OSFourSpace))
  rw [add_comm (v:OSFourSpace)]
  exact normal_photon_weight_cell (norm_nonneg (v:OSFourSpace)) _ _ le_rfl 2

/-- The divergence persists outside every finite infrared cut. This is
the scalar single-photon majorant in the manuscript, before any extra
decay contributed by a particular charged graph. -/
theorem normal_low_rank_photon_hard {ι : Type*} [Fintype ι] (L ρ : ℝ)
    (T : OSFourSpace →L[ℝ] WilsonBallSpace ι) (hr : Module.finrank ℝ (LinearMap.range T.toLinearMap) ≤ 2) :
    ¬ IntegrableOn (fun p => ‖normalPhotonForm L T p‖^2 / ‖p‖^2) (ball 0 ρ)ᶜ := by
  let R := max 1 ρ
  let f := fun p => ‖normalPhotonForm L T p‖^2 * normalPhotonWeight 2 p
  have hc : Continuous f := ((normal_photon_form_continuous L T).norm.pow 2).mul
    (((continuous_const.add continuous_norm).pow 2).inv₀ fun p => by positivity)
  intro hi
  have hout : IntegrableOn f (ball 0 R)ᶜ := by
    have hg := hi.mono_set (compl_subset_compl.mpr (ball_subset_ball (le_max_right 1 ρ)))
    apply hg.mono' hc.aestronglyMeasurable
    rw [ae_restrict_iff' measurableSet_ball.compl]
    refine Eventually.of_forall fun p hp => ?_
    have hp' : R ≤ ‖p‖ := by simpa [R,mem_ball] using hp
    have hp0 : 0 < ‖p‖ := lt_of_lt_of_le zero_lt_one ((le_max_left 1 ρ).trans hp')
    change ‖‖normalPhotonForm L T p‖^2 * ((1+‖p‖)^2)⁻¹‖ ≤ _
    rw [Real.norm_of_nonneg (by positivity),div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (pow_le_pow_left₀ (norm_nonneg _) (by linarith) _)) (by positivity)
  have hin : IntegrableOn f (ball 0 R) := (hc.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).mono_set ball_subset_closedBall
  apply normal_low_rank_photon_soft L T hr
  simpa only [union_compl_self,integrableOn_univ] using hin.union hout

/-- Sharp continuum readout criterion at nonzero length, for any fixed
soft cut (including a vanishing cut). -/
theorem normal_photon_rank_criterion {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L) (ρ : ℝ)
    (T : OSFourSpace →L[ℝ] WilsonBallSpace ι) :
    IntegrableOn (wilsonPhotonDensity (normalPhotonForm L T)) (ball 0 ρ)ᶜ ↔ 3 ≤ Module.finrank ℝ (LinearMap.range T.toLinearMap) := by
  constructor
  · intro h
    by_contra! hbad
    exact normal_low_rank_photon_hard L ρ T (by omega) h
  · intro h
    exact (normal_continuum_maxwell_integrable hL T h).integrableOn

end UV
