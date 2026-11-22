import UV.FurtherOpticalProjector

/-! Large spatial shifts of the explicit optical projector. No boost or
rotation of the Lorentzian carrier axis is made in taking this limit. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal InnerProductSpace

namespace UV.FurtherOptical

def departure (m τ : ℝ) (k : ChargeSpatialMomentum) : DiracMomentum :=
  coefficients m τ k-massAxis

theorem departure_norm_bound {m τ : ℝ} (hm : 0 < m) (hτ : 0 ≤ τ)
    (k : ChargeSpatialMomentum) :
    ‖departure m τ k‖ ≤ Real.sqrt 2 * attenuation τ k := by
  have h := projector_gaussian_bound hm hτ k
  rw [projector_difference_sq] at h
  have he : attenuation τ k ^ 2 = Real.exp (-(2*τ)*‖k‖^2) := by
    unfold attenuation
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hp : 0 ≤ Real.sqrt 2 * attenuation τ k :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) hp).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num), he]
  exact h

private theorem attenuation_tendsto_zero {τ : ℝ} (hτ : 0 < τ)
    {α : Type*} {l : Filter α} {z : α → ChargeSpatialMomentum}
    (hz : Tendsto (fun p => ‖z p‖) l atTop) :
    Tendsto (fun p => attenuation τ (z p)) l (𝓝 0) := by
  have hp : Tendsto (fun r : ℝ => r^2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have h₁ := (hp.comp hz).const_mul_atTop hτ
  have h₂ := tendsto_neg_atTop_atBot.comp h₁
  simpa only [attenuation, Function.comp_apply, neg_mul] using Real.tendsto_exp_atBot.comp h₂

private theorem shiftedNorm_tendsto_atTop (k : ChargeSpatialMomentum)
    {α : Type*} {l : Filter α} (p : α → ChargeSpatialMomentum)
    (hp : Tendsto (fun z => ‖p z‖) l atTop) :
    Tendsto (fun z => ‖k+p z‖) l atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [hp.eventually_ge_atTop (b+‖k‖)] with z hz
  have he := norm_sub_le (k+p z) k
  have heq : k+p z-k = p z := by abel
  rw [heq] at he
  linarith

private theorem departure_inner_bound {m τ : ℝ} (hm : 0 < m) (hτ : 0 ≤ τ)
    (p k : ChargeSpatialMomentum) :
    ‖⟪departure m τ (k+p), departure m τ k⟫_ℝ‖ ≤ 2*attenuation τ k := by
  have hle : attenuation τ (k+p) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hτ)
      (sq_nonneg ‖k+p‖))
  have hnorm := (departure_norm_bound hm hτ (k+p)).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg 2))
  calc
    _ ≤ ‖departure m τ (k+p)‖ * ‖departure m τ k‖ := norm_inner_le_norm _ _
    _ ≤ Real.sqrt 2 * (Real.sqrt 2 * attenuation τ k) :=
      mul_le_mul hnorm (departure_norm_bound hm hτ k) (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by rw [← mul_assoc, ← pow_two, Real.sq_sqrt (by norm_num)]

/-- For the actual Gaussian spinor, overlap with any spatially translated
copy of its departure from the constant sea tends to zero at infinity. -/
theorem optical_overlap_tendsto_zero {m τ : ℝ} (hm : 0 < m) (hτ : 0 < τ)
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated] (p : α → ChargeSpatialMomentum)
    (hp : Tendsto (fun z => ‖p z‖) l atTop) :
    Tendsto (fun z => ∫ k : ChargeSpatialMomentum,
      ⟪departure m τ (k+p z), departure m τ k⟫_ℝ) l (𝓝 0) := by
  have hc : Continuous (departure m τ) :=
    (coefficients_continuous hm).sub continuous_const
  have hi : Integrable (fun k : ChargeSpatialMomentum => 2*attenuation τ k) := by
    simpa [attenuation, show (1:ℝ)+1=2 by norm_num, neg_mul] using
      integrable_real_degree_gaussian (E := ChargeSpatialMomentum) (μ := volume)
        (a := τ) (D := 0) hτ (by norm_num)
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (F := fun z k => ⟪departure m τ (k+p z), departure m τ k⟫_ℝ)
    (f := fun _ : ChargeSpatialMomentum => (0:ℝ))
    (fun k => 2*attenuation τ k)
    (Eventually.of_forall fun z =>
      ((hc.comp (continuous_id.add continuous_const)).inner hc).aestronglyMeasurable)
    (Eventually.of_forall fun z => Eventually.of_forall fun k => departure_inner_bound hm hτ.le (p z) k)
    hi (by
      refine Eventually.of_forall fun k => ?_
      have hfield := attenuation_tendsto_zero hτ (shiftedNorm_tendsto_atTop k p hp)
      have hmajor : Tendsto (fun z => Real.sqrt 2*attenuation τ (k+p z) * ‖departure m τ k‖) l (𝓝 0) := by
        simpa using (hfield.const_mul (Real.sqrt 2)).mul_const ‖departure m τ k‖
      apply squeeze_zero_norm (fun z => ?_) hmajor
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
        (departure_norm_bound hm hτ.le _) (norm_nonneg _)))
  simpa only [integral_zero] using h

theorem optical_canonicalDensity_overlap_identity {m τ : ℝ} (hm : 0 < m) (hτ : 0 < τ)
    (p : ChargeSpatialMomentum) :
    ContinuationBoostSpectrum.canonicalDensity (fun k => projector (coefficients m τ k)) p =
      ContinuationBoostSpectrum.spatialMeasureFactor *
        ((∫ k : ChargeSpatialMomentum, ‖departure m τ k‖^2) -
          ∫ k : ChargeSpatialMomentum, ⟪departure m τ (k+p), departure m τ k⟫_ℝ) := by
  have hf : Integrable (fun k : ChargeSpatialMomentum => ‖departure m τ k‖^2) := by
    simpa only [projector_difference_sq, departure] using projector_departure_integrable hm hτ
  have hpres : MeasurePreserving (fun k : ChargeSpatialMomentum => k+p) volume volume :=
    measurePreserving_add_right volume p
  have hshift : Integrable (fun k : ChargeSpatialMomentum => ‖departure m τ (k+p)‖^2) :=
    hpres.integrable_comp_of_integrable hf
  have hshiftEq := hpres.integral_comp (Homeomorph.addRight p).isClosedEmbedding.measurableEmbedding
    (fun k => ‖departure m τ k‖^2)
  change (∫ k, ‖departure m τ (k+p)‖^2) = (∫ k, ‖departure m τ k‖^2) at hshiftEq
  have hc : Continuous (departure m τ) := (coefficients_continuous hm).sub continuous_const
  have hj : Integrable (fun k : ChargeSpatialMomentum => 2*attenuation τ k) := by
    simpa [attenuation, show (1:ℝ)+1=2 by norm_num, neg_mul] using
      integrable_real_degree_gaussian (E := ChargeSpatialMomentum) (μ := volume)
        (a := τ) (D := 0) hτ (by norm_num)
  have hi : Integrable (fun k : ChargeSpatialMomentum => ⟪departure m τ (k+p), departure m τ k⟫_ℝ) :=
    hj.mono' (((hc.comp (continuous_id.add continuous_const)).inner hc).aestronglyMeasurable)
      (Eventually.of_forall fun k => departure_inner_bound hm hτ.le p k)
  unfold ContinuationBoostSpectrum.canonicalDensity
  congr 1
  change (∫ k, pairWeight m τ p k) = _
  simp_rw [pairWeight_eq_coefficientDistance hm hτ.le p]
  have hpoint (k : ChargeSpatialMomentum) :
      ‖coefficients m τ (k+p)-coefficients m τ k‖^2/2 =
        (‖departure m τ (k+p)‖^2 -
          2*⟪departure m τ (k+p), departure m τ k⟫_ℝ + ‖departure m τ k‖^2)/2 := by
    rw [show coefficients m τ (k+p)-coefficients m τ k =
      departure m τ (k+p)-departure m τ k by unfold departure; abel, norm_sub_sq_real]
  simp_rw [hpoint]
  have hdouble : Integrable (fun k : ChargeSpatialMomentum =>
      2 * ⟪departure m τ (k+p), departure m τ k⟫_ℝ) := hi.const_mul 2
  have hminus : Integrable (fun k : ChargeSpatialMomentum =>
      ‖departure m τ (k+p)‖^2 - 2 * ⟪departure m τ (k+p), departure m τ k⟫_ℝ) :=
    hshift.sub hdouble
  rw [integral_div, integral_add hminus hf,
    integral_sub hshift hdouble, integral_const_mul, hshiftEq]
  ring

/-- The normalized canonical equal-time density tends to the full normalized
square-integrable projector-departure mass. -/
theorem optical_canonicalDensity_tendsto_departure_mass {m τ : ℝ} (hm : 0 < m) (hτ : 0 < τ)
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated] (p : α → ChargeSpatialMomentum)
    (hp : Tendsto (fun z => ‖p z‖) l atTop) :
    Tendsto (fun z => ContinuationBoostSpectrum.canonicalDensity
      (fun k => projector (coefficients m τ k)) (p z)) l
      (𝓝 (ContinuationBoostSpectrum.spatialMeasureFactor *
        ∫ k : ChargeSpatialMomentum, chargeInclusiveSquare
          (projector (coefficients m τ k)-projector massAxis))) := by
  simp_rw [projector_difference_sq]
  have h := optical_overlap_tendsto_zero hm hτ p hp
  have hc : Tendsto (fun _ : α => ∫ k : ChargeSpatialMomentum, ‖departure m τ k‖^2) l
      (𝓝 (∫ k : ChargeSpatialMomentum, ‖departure m τ k‖^2)) := tendsto_const_nhds
  have he := (hc.sub h).const_mul ContinuationBoostSpectrum.spatialMeasureFactor
  simp only [sub_zero] at he
  exact he.congr (fun z => (optical_canonicalDensity_overlap_identity hm hτ (p z)).symm)

end UV.FurtherOptical
