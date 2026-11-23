import UV.ContinueNormalLegHessian
import UV.ContinueWilsonCurrentRotation
import Mathlib.Analysis.Normed.Group.Tannery

/-! The limit of the two transverse insertions as the external
four-transfer tends to zero. Both charged and photon form factors and
all shifted normal modes enter the amplitude. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Metric UV.SectorPlane
open scoped RealInnerProductSpace Matrix.Norms.L2Operator Topology

namespace UV

variable {ι : Type*} [Fintype ι]

theorem normal_frequency_continuous {m : ℝ} (hm : 0 < m) (ξ : ℝ) : Continuous (fun p => normalDiracFrequency m p ξ) := by
  have hN : Continuous (freeDiracNumerator m) := by
    unfold freeDiracNumerator diracSlash
    apply Continuous.add _ continuous_const
    apply continuous_const.smul (continuous_finset_sum _ (fun j _ =>
      (Complex.continuous_ofReal.comp (EuclideanSpace.proj j).continuous).smul continuous_const))
  unfold normalDiracFrequency
  apply Continuous.smul _ (hN.add continuous_const)
  apply Continuous.inv₀
  · unfold normalFiveDenom; fun_prop
  · intro p
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by unfold normalFiveDenom; positivity))

theorem normal_frequency_mass_bound {m : ℝ} (hm : 0 < m) (p : OSFourSpace) (ξ : ℝ) :
    ‖normalDiracFrequency m p ξ‖ ≤ m⁻¹ := by
  rw [normal_dirac_frequency_norm hm]
  apply inv_anti₀ hm
  apply (Real.le_sqrt hm.le (by unfold normalFiveDenom; positivity)).mpr
  unfold normalFiveDenom; nlinarith [sq_nonneg ‖p‖,sq_nonneg ξ]

def normalLegNearby (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (u : UnitVector OSFourSpace) (Q p : OSFourSpace) : ℝ :=
  let A := fun k => normalDiracFrequency m k ξ * diracSlash u.val
  let photon := -(normalLegForm L T 0 Q)^2
  photon * (normalLegForm L T ξ p)^2 * (normalLegForm L T ξ (p+Q))^2 * ((A p)*(A (p+Q))).trace.re

/-- Two separate charged compressions at each of the two vertices, and
one projected photon factor at each incidence. -/
theorem normal_leg_nearby_vertices (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (u : UnitVector OSFourSpace) (Q p : OSFourSpace) :
    let c := normalLegForm L T 0 Q*normalLegForm L T ξ p*normalLegForm L T ξ (p+Q)
    let V := (Complex.I*(c:ℂ)) • diracSlash u.val
    normalLegNearby m L T ξ u Q p = ((normalDiracFrequency m p ξ*V)*(normalDiracFrequency m (p+Q) ξ*V)).trace.re := by
  dsimp only [normalLegNearby]
  rw [mul_smul_comm,mul_smul_comm,smul_mul_smul,Matrix.trace_smul,smul_eq_mul]
  have hi (c : ℝ) : (Complex.I*(c:ℂ))*(Complex.I*(c:ℂ)) = -((c^2:ℝ):ℂ) := by
    push_cast
    calc _ = (Complex.I*Complex.I)*(c:ℂ)^2 := by ring
         _ = _ := by rw [Complex.I_mul_I,neg_one_mul]
  rw [hi]
  simp only [neg_mul,Complex.neg_re,Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re,zero_mul,sub_zero]
  ring

theorem normal_leg_form_origin (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) : normalLegForm L T 0 0 = 1 := by
  have h : normalBallJoin 0 (0:OSFourSpace) = 0 := by
    apply norm_eq_zero.mp
    have he := normal_ball_join_norm 0 (0:OSFourSpace)
    simp only [norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,add_zero] at he
    nlinarith
  simp [normalLegForm,h,normalShellCharacteristic]

theorem normal_leg_nearby_zero (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ) (i : Fin 4) (p : OSFourSpace) :
    normalLegNearby m L T ξ (osAxis i) 0 p = normalLegHessian m L T ξ i p := by
  rw [normal_leg_nearby_vertices]
  simp only [normal_leg_form_origin,one_mul,add_zero,←pow_two,Complex.ofReal_pow,normalLegHessian]

theorem normal_leg_nearby_continuous {m : ℝ} (hm : 0 < m) (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (ξ : ℝ) (u : UnitVector OSFourSpace) : Continuous (fun z : OSFourSpace × OSFourSpace => normalLegNearby m L T ξ u z.1 z.2) := by
  let tr := (Matrix.traceLinearMap (Fin 4) ℂ ℂ).toContinuousLinearMap
  let A := fun k => normalDiracFrequency m k ξ * diracSlash u.val
  have ha : Continuous A := (normal_frequency_continuous hm ξ).mul continuous_const
  have hq : Continuous (fun z : OSFourSpace × OSFourSpace => normalLegForm L T 0 z.1) := (normal_leg_form_continuous L T 0).comp continuous_fst
  have hp : Continuous (fun z : OSFourSpace × OSFourSpace => normalLegForm L T ξ z.2) := (normal_leg_form_continuous L T ξ).comp continuous_snd
  have hs : Continuous (fun z : OSFourSpace × OSFourSpace => z.2+z.1) := continuous_snd.add continuous_fst
  change Continuous (fun z : OSFourSpace × OSFourSpace => -(normalLegForm L T 0 z.1)^2 * (normalLegForm L T ξ z.2)^2 *
    (normalLegForm L T ξ (z.2+z.1))^2 * (tr ((A z.2)*(A (z.2+z.1)))).re)
  have hsc := ((hq.pow 2).neg.mul (hp.pow 2)).mul (((normal_leg_form_continuous L T ξ).comp hs).pow 2)
  exact hsc.mul (Complex.continuous_re.comp (tr.continuous.comp ((ha.comp continuous_snd).mul (ha.comp hs))))

theorem normal_leg_nearby_uniform {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (u : UnitVector OSFourSpace) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (ξ : ℝ) (Q p : OSFourSpace), ‖Q‖ ≤ 1 →
      |normalLegNearby m L T ξ u Q p| ≤ K*normalPhotonWeight 2 ξ*normalPhotonWeight 6 p := by
  obtain ⟨C,hC,h⟩ := normal_leg_fourth_power hL T
  let B := 4*(m⁻¹*m⁻¹)
  let K := B*(C*65)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨K,by dsimp [K]; positivity,fun ξ Q p hQ => ?_⟩
  let A := fun k => normalDiracFrequency m k ξ * diracSlash u.val
  have ha (k) : ‖A k‖ ≤ m⁻¹ := by
    apply (norm_mul_le _ _).trans
    rw [wilson_slash_opnorm,u.property,mul_one]
    exact normal_frequency_mass_bound hm _ _
  have ht : |((A p)*(A (p+Q))).trace.re| ≤ B := by
    apply (Complex.abs_re_le_norm _).trans (wilson_trace_le_opnorm _ |>.trans ?_)
    exact mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans (mul_le_mul (ha _) (ha _) (norm_nonneg _) (inv_nonneg.mpr hm.le))) (by norm_num)
  have hχ : |normalLegForm L T 0 Q| ≤ 1 := (Complex.abs_re_le_norm _).trans (normal_shell_characteristic_le_one _)
  let f := normalLegForm L T ξ
  have hf : 0 ≤ (f p)^2*(f (p+Q))^2 := by positivity
  have hsum : (f p)^2*(f (p+Q))^2 ≤ (f p)^4+(f (p+Q))^4 := by nlinarith [sq_nonneg ((f p)^2-(f (p+Q))^2),sq_nonneg ((f p)^2),sq_nonneg ((f (p+Q))^2)]
  have hc : normalPhotonWeight 6 (p+Q) ≤ 64*normalPhotonWeight 6 p := by
    simpa [show (1+1:ℝ)^6=64 by norm_num] using normal_photon_weight_cell (by norm_num : (0:ℝ) ≤ 1) (p+Q) (-Q) (by simpa using hQ) 6
  have hw : 0 ≤ normalPhotonWeight 2 ξ := by unfold normalPhotonWeight; positivity
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hC.le) hw
  have h4 : (f p)^4+(f (p+Q))^4 ≤ C*65*normalPhotonWeight 2 ξ*normalPhotonWeight 6 p := by
    apply (add_le_add (h ξ p) ((h ξ (p+Q)).trans h2)).trans_eq
    ring
  change |-(normalLegForm L T 0 Q)^2*(f p)^2*(f (p+Q))^2*((A p)*(A (p+Q))).trace.re| ≤ _
  rw [abs_mul,abs_mul,abs_mul,abs_neg,abs_of_nonneg (sq_nonneg _),abs_of_nonneg (sq_nonneg _),abs_of_nonneg (sq_nonneg _)]
  have hχ2 : (normalLegForm L T 0 Q)^2 ≤ 1 := by nlinarith [sq_abs (normalLegForm L T 0 Q),abs_nonneg (normalLegForm L T 0 Q)]
  calc _ ≤ 1*(f p)^2*(f (p+Q))^2*B := by gcongr
       _ ≤ B*(C*65*normalPhotonWeight 2 ξ*normalPhotonWeight 6 p) := by
         rw [one_mul,mul_comm _ B]; exact mul_le_mul_of_nonneg_left (hsum.trans h4) hB
       _ = _ := by dsimp [K]; ring

theorem normal_leg_zero_unit_formula (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (u : UnitVector OSFourSpace) (p : OSFourSpace) : normalLegNearby m L T ξ u 0 p =
      -(4*normalLegForm L T ξ p^4*(normalFiveDenom m p ξ-2*⟪u.val,p⟫^2)/normalFiveDenom m p ξ^2) := by
  rw [normal_leg_nearby_vertices]
  simp only [normal_leg_form_origin,one_mul,add_zero,←pow_two,Complex.ofReal_pow]
  simpa only [pow_two] using normal_zero_transfer_hessian m p ξ (normalLegForm L T ξ p) u

theorem normal_leg_integral_unit (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (u : UnitVector OSFourSpace) : (∫ p, normalLegNearby m L T ξ u 0 p) = ∫ p, normalLegHessian m L T ξ 0 p := by
  let v := osAxis 0
  let e := (ℝ ∙ (v.val-u.val))ᗮ.reflection
  have he : e v.val = u.val := Submodule.reflection_sub (v.property.trans u.property.symm)
  rw [←e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding]
  apply integral_congr_ae (Eventually.of_forall fun p => ?_)
  change normalLegNearby m L T ξ u 0 (e p) = _
  rw [←normal_leg_nearby_zero,normal_leg_zero_unit_formula,normal_leg_zero_unit_formula,
    normal_leg_form_radial L T ξ (e.norm_map p),←he,e.inner_map_map]
  simp only [normalFiveDenom,e.norm_map,v]

/-- The Euclidean loop kernel in a fixed unit transverse polarization
has a strictly negative zero-momentum limit, including the conventional
four-volume normalization. Adding the Maxwell eigenvalue leaves this limit. -/
theorem normal_leg_photon_obstruction {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (θ : ℝ) (u : UnitVector OSFourSpace) :
    let A := fun Q : OSFourSpace => (∑' j : ℤ, ∫ p, normalLegNearby m L T (normalLegFrequency L θ j) u Q p) / (2*Real.pi)^4
    Tendsto A (𝓝 0) (𝓝 (A 0)) ∧ A 0 < 0 ∧ Tendsto (fun Q => ‖Q‖^2+A Q) (𝓝 0) (𝓝 (A 0)) := by
  let ξ := normalLegFrequency L θ
  let F := fun j => normalLegNearby m L T (ξ j) u
  let W := normalPhotonWeight (E := OSFourSpace) 6
  have hi : Integrable W := normal_photon_weight_integrable volume (by rw [finrank_euclideanSpace_fin]; decide)
  obtain ⟨K,_,hb⟩ := normal_leg_nearby_uniform hm hL T u
  let M := fun j => K*normalPhotonWeight 2 (ξ j)
  have hB (j) : Integrable (fun p => M j*W p) := hi.const_mul (M j)
  have hnear : ∀ᶠ Q : OSFourSpace in 𝓝 0, ‖Q‖ ≤ 1 := by
    filter_upwards [Metric.ball_mem_nhds (0:OSFourSpace) (by norm_num : (0:ℝ)<1)] with Q hQ
    exact (show ‖Q‖ < 1 by simpa using hQ).le
  have hcont (j) := normal_leg_nearby_continuous hm L T (ξ j) u
  have hj (j) : Tendsto (fun Q => ∫ p, F j Q p) (𝓝 0) (𝓝 (∫ p, F j 0 p)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun p => M j*W p)
      (Eventually.of_forall fun Q => ((hcont j).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable) _ (hB j)
    · exact Eventually.of_forall fun p => ((hcont j).comp (continuous_id.prodMk continuous_const)).tendsto 0
    · exact hnear.mono fun Q hQ => Eventually.of_forall fun p => hb _ Q p hQ
  have hs : Summable (fun j => M j*∫ p, W p) := ((normal_shifted_frequency_summable hL θ).mul_left K).mul_right _
  have hts : Tendsto (fun Q => ∑' j, ∫ p, F j Q p) (𝓝 0) (𝓝 (∑' j, ∫ p, F j 0 p)) := by
    apply tendsto_tsum_of_dominated_convergence hs hj
    filter_upwards [hnear] with Q hQ j
    have h := hb (ξ j) Q
    have hle (p) : ‖F j Q p‖ ≤ M j*W p := h p hQ
    have hI := (hB j).mono' ((hcont j).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable (Eventually.of_forall hle)
    exact (norm_integral_le_integral_norm _).trans ((integral_mono hI.norm (hB j) hle).trans_eq (integral_const_mul ..))
  have h := hts.div_const ((2*Real.pi)^4)
  refine ⟨h,?_,?_⟩
  · simp_rw [normal_leg_integral_unit]
    exact div_neg_of_neg_of_pos (normal_leg_hessian_zero hm hL T θ 0).2.2 (by positivity)
  · simpa only [norm_zero,zero_pow (by decide : 2 ≠ 0),zero_add] using ((continuous_norm.pow 2).tendsto (0:OSFourSpace)).add h

def SectorPlane.Plane.normalLegChartResponse {E : Type*} [Norm E] (diamond : Plane E) (m L : ℝ)
    (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (θ : ℝ) (u : UnitVector OSFourSpace) (Q : OSFourSpace) : ℝ :=
  let R := diamond.osOrientedChart
  (∑' j : ℤ, ∫ p, normalLegNearby m L T (normalLegFrequency L θ j) (wilsonRotateUnit R u) (R Q) (R p))/(2*Real.pi)^4

/-- In the sector plane, the same chart acts on the polarization,
the transfer and the carrier integration variable. Restrict to transverse
nonzero transfers, as in the physical one-loop test. -/
theorem SectorPlane.Plane.normal_leg_transverse_limit {E : Type*} [Norm E] (diamond : Plane E) {m L : ℝ}
    (hm : 0 < m) (hL : 0 < L) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (θ : ℝ) (u : UnitVector OSFourSpace) :
    let A := diamond.normalLegChartResponse m L T θ u
    let S := {Q : OSFourSpace | Q ≠ 0 ∧ ⟪u.val,Q⟫ = 0}
    A 0 < 0 ∧ Tendsto (fun Q => ‖Q‖^2+A Q) (𝓝[S] 0) (𝓝 (A 0)) := by
  let R := diamond.osOrientedChart
  let v := wilsonRotateUnit R u
  let F := fun Q : OSFourSpace => (∑' j : ℤ, ∫ p, normalLegNearby m L T (normalLegFrequency L θ j) v Q p)/(2*Real.pi)^4
  have he (Q : OSFourSpace) (j : ℤ) : (∫ p, normalLegNearby m L T (normalLegFrequency L θ j) v (R Q) (R p)) =
      ∫ p, normalLegNearby m L T (normalLegFrequency L θ j) v (R Q) p :=
    R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding _
  let A := diamond.normalLegChartResponse m L T θ u
  have hA (Q) : A Q = F (R Q) := by
    change (∑' j, ∫ p, normalLegNearby m L T (normalLegFrequency L θ j) v (R Q) (R p))/(2*Real.pi)^4 = _
    simp_rw [he]
    rfl
  have h0 : A 0 = F 0 := (hA 0).trans (congrArg F R.map_zero)
  have h := normal_leg_photon_obstruction hm hL T θ v
  have hR : Tendsto R (𝓝 0) (𝓝 0) := by simpa only [map_zero] using R.continuous.tendsto 0
  have ht : Tendsto (fun Q => ‖R Q‖^2+F (R Q)) (𝓝 0) (𝓝 (F 0)) := h.2.2.comp hR
  change A 0 < 0 ∧ Tendsto (fun Q => ‖Q‖^2+A Q) _ (𝓝 (A 0))
  rw [h0]
  refine ⟨h.2.1,?_⟩
  simp_rw [hA]
  exact (show Tendsto (fun Q => ‖Q‖^2+F (R Q)) (𝓝 0) (𝓝 (F 0)) by simpa only [R.norm_map] using ht).mono_left nhdsWithin_le_nhds

end UV
