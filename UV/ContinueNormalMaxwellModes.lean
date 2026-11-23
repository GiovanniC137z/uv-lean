import UV.ContinueNormalRankReadout

/-! Integrability of the actual massless transverse photon majorant
with two compressed A4 shell incidences in any linear readout of rank
at least three. A full reciprocal lattice includes every nonzero mode. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Metric Filter Set UV.SectorPlane
open scoped ENNReal

namespace UV

theorem normal_hard_density_bound {χ : OSFourSpace → ℂ} (U : NormalPhotonChart) {C ρ : ℝ}
    (hρ : 0 < ρ) (hf : ∀ p, ‖χ p‖ ≤ C/(1+‖(U p).1‖)^2) (p : OSFourSpace) (hp : ρ ≤ ‖p‖) :
    wilsonPhotonDensity χ p ≤ (C^2*(ρ⁻¹+‖U.toContinuousLinearMap‖)^2)*normalPhotonEnvelope U p := by
  have hp' : 0 < ‖p‖ := hρ.trans_le hp
  have hnorm := (norm_snd_le (U p)).trans (U.toContinuousLinearMap.le_opNorm p)
  have hunit : 1 ≤ ρ⁻¹*‖p‖ := by rw [inv_mul_eq_div,le_div_iff₀ hρ,one_mul]; exact hp
  have hω : 1+‖(U p).2‖ ≤ (ρ⁻¹+‖U.toContinuousLinearMap‖)*‖p‖ := by linarith
  have hden : (‖p‖^2)⁻¹ ≤ (ρ⁻¹+‖U.toContinuousLinearMap‖)^2 * normalPhotonWeight 2 (U p).2 := by
    rw [normalPhotonWeight,←div_eq_mul_inv,le_div_iff₀ (by positivity),inv_mul_eq_div,div_le_iff₀ (by positivity : 0 < ‖p‖^2),←mul_pow]
    exact pow_le_pow_left₀ (by positivity) hω 2
  have hnum : ‖χ p‖^2 ≤ C^2*normalPhotonWeight 4 (U p).1 := by
    apply (pow_le_pow_left₀ (norm_nonneg _) (hf p) 2).trans_eq
    rw [normalPhotonWeight,div_pow,div_eq_mul_inv,←pow_mul]
  rw [wilsonPhotonDensity,div_eq_mul_inv]
  have hN : 0 ≤ C^2*normalPhotonWeight 4 (U p).1 := by dsimp [normalPhotonWeight]; positivity
  apply (mul_le_mul hnum hden (inv_nonneg.mpr (sq_nonneg _)) hN).trans_eq
  dsimp only [normalPhotonEnvelope]; ring

theorem normal_continuum_maxwell_integrable {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L)
    (T : OSFourSpace →L[ℝ] WilsonBallSpace ι) (hr : 3 ≤ Module.finrank ℝ (LinearMap.range T.toLinearMap)) :
    Integrable (wilsonPhotonDensity (normalPhotonForm L T)) := by
  obtain ⟨U,C,_,hf⟩ := normal_rank_three_form_bound hL T hr
  let χ := normalPhotonForm L T
  have hm : Measurable (wilsonPhotonDensity χ) := ((normal_photon_form_continuous L T).measurable.norm.pow_const 2).div (measurable_norm.pow_const 2)
  have hsmall : IntegrableOn (wilsonPhotonDensity χ) (closedBall 0 1) := by
    apply wilson_local_maxwell_integrable.mono' hm.aestronglyMeasurable
    refine Eventually.of_forall fun p => ?_
    rw [Real.norm_of_nonneg (wilson_photon_density_nonneg _ _),wilsonPhotonDensity,div_eq_mul_inv]
    apply mul_le_of_le_one_left (inv_nonneg.mpr (sq_nonneg _))
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (normal_shell_characteristic_le_one (L • T p)) 2
  have hbig : IntegrableOn (wilsonPhotonDensity χ) (closedBall 0 1)ᶜ := by
    apply ((normal_photon_envelope_integrable U).const_mul (C^2*((1:ℝ)⁻¹+‖U.toContinuousLinearMap‖)^2)).integrableOn.mono'
      hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet.compl] with p hp
    have hp' : 1 < ‖p‖ := by simpa using hp
    rw [Real.norm_of_nonneg (wilson_photon_density_nonneg _ _)]
    exact normal_hard_density_bound U zero_lt_one hf p hp'.le
  exact integrableOn_univ.mp (by simpa only [union_compl_self] using hsmall.union hbig)

theorem normal_lattice_maxwell_integrable {ι : Type*} [Fintype ι] (b : NormalReciprocalBasis)
    {L : ℝ} (hL : 0 < L) (T : OSFourSpace →L[ℝ] WilsonBallSpace ι)
    (hr : 3 ≤ Module.finrank ℝ (LinearMap.range T.toLinearMap)) :
    Integrable (wilsonPhotonDensity (normalPhotonForm L T)) (normalLatticeMeasure b) := by
  obtain ⟨U,C,_,hf⟩ := normal_rank_three_form_bound hL T hr
  obtain ⟨ρ,hρ,hgap⟩ := normal_lattice_mode_gap b
  let χ := normalPhotonForm L T
  let K := C^2*(ρ⁻¹+‖U.toContinuousLinearMap‖)^2
  have hm : Measurable (wilsonPhotonDensity χ) := ((normal_photon_form_continuous L T).measurable.norm.pow_const 2).div (measurable_norm.pow_const 2)
  apply ((normal_lattice_photon_envelope_integrable b U).const_mul K).mono' hm.aestronglyMeasurable
  have h : ∀ᵐ p ∂normalLatticeMeasure b, p ∈ (NormalReciprocalLattice b : Set OSFourSpace) := by
    have hset : (NormalReciprocalLattice b : Set OSFourSpace).Countable :=
      Set.countable_coe_iff.mp (show Countable (NormalReciprocalLattice b) from inferInstance)
    exact (ae_map_iff measurable_subtype_coe.aemeasurable hset.measurableSet).mpr (Eventually.of_forall fun k => k.property)
  filter_upwards [h] with p hp
  rw [Real.norm_of_nonneg (wilson_photon_density_nonneg _ _)]
  by_cases hz : p = 0
  · subst p
    simp only [wilsonPhotonDensity,norm_zero,zero_pow (by decide : 2 ≠ 0),div_zero]
    dsimp [K,normalPhotonEnvelope,normalPhotonWeight]; positivity
  · exact normal_hard_density_bound U hρ hf p (hgap ⟨p,hp⟩ (fun he => hz (congrArg Subtype.val he)))

end UV
