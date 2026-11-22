import UV.NextOpticalBandUpper

/-! The exact optical pair mass band on the intrinsic spatial chart.
Polar integration of the transverse tube gives a radial interval bound. -/

noncomputable section

open Filter Set MeasureTheory Metric
open scoped Topology ENNReal InnerProductSpace Pointwise

namespace UV.NextOpticalRadial

/-- The invariant mass squared of the two future massive constituent
momenta (k+p) and (-k), with total spatial transfer (p). -/
def pairInvariantMass (m : ℝ) (p k : ChargeSpatialMomentum) : ℝ :=
  (FurtherOptical.energy m (k+p)+FurtherOptical.energy m (-k))^2 - ‖p‖^2

def compactPairBand (m : ℝ) (p : ChargeSpatialMomentum) (s₁ s₂ : ℝ) :
    Set ChargeSpatialMomentum :=
  pairInvariantMass m p ⁻¹' Icc s₁ s₂

theorem compactPairBand_measurable (m : ℝ) (p : ChargeSpatialMomentum) (s₁ s₂ : ℝ) :
    MeasurableSet (compactPairBand m p s₁ s₂) := by
  apply measurableSet_Icc.preimage
  unfold pairInvariantMass FurtherOptical.energy
  fun_prop

theorem compactPairBand_exchange (m : ℝ) (p k : ChargeSpatialMomentum) (s₁ s₂ : ℝ) :
    -(k+p) ∈ compactPairBand m p s₁ s₂ ↔ k ∈ compactPairBand m p s₁ s₂ := by
  unfold compactPairBand pairInvariantMass
  simp only [mem_preimage, neg_neg]
  rw [show -(k+p)+p = -k by abel, add_comm]

/-- The actual boosted pair in the compact band lies in the radial
interval and the transverse tube. Both estimates use the same unit
spatial axis and the same invariant mass bound. -/
theorem compactPairBand_radial_support {m S s₁ s₂ : ℝ} (hm : 0 < m) (hS : 0 < S)
    (hs₂ : 0 < s₂) (hLarge : s₂/m ≤ S) (hWidth : Real.sqrt (s₂/4) ≤ S)
    {k : ChargeSpatialMomentum}
    (hk : k ∈ compactPairBand m (S • (spatialAxis : ChargeSpatialMomentum)) s₁ s₂) :
    ‖k‖ ∈ Icc ((m^2/(2*s₂))*S) (2*S) ∧
      ∀ i : Fin 3, i ≠ 0 → |k i| ≤ Real.sqrt (s₂/4) := by
  have hNorm : ‖S • (spatialAxis : ChargeSpatialMomentum)‖ = S := by
    rw [norm_smul, spatialAxis.property, mul_one, Real.norm_of_nonneg hS.le]
  have hk' : pairInvariantMass m (S • (spatialAxis : ChargeSpatialMomentum)) k ≤ s₂ := hk.2
  rw [pairInvariantMass, hNorm] at hk'
  obtain ⟨_, _, hx, hxU, ht⟩ :=
    compactBand_longitudinal_and_transverse spatialAxis k hm hS hs₂ hLarge hk'
  let x₀ := ⟪-k, (spatialAxis : ChargeSpatialMomentum)⟫_ℝ
  have hx' : (m^2/(2*s₂))*S ≤ x₀ := hx
  have hxU' : x₀ ≤ S := hxU
  have hx₀ : 0 ≤ x₀ := (by positivity : 0 ≤ (m^2/(2*s₂))*S).trans hx'
  have hn : x₀ ≤ ‖k‖ := by
    simpa only [x₀, norm_neg, spatialAxis.property, mul_one] using
      real_inner_le_norm (-k) (spatialAxis : ChargeSpatialMomentum)
  have htSq : ‖k‖^2 = x₀^2 + ‖transverseMomentum spatialAxis k‖^2 := by
    rw [transverseMomentum_sq, show x₀ = -⟪k,(spatialAxis : ChargeSpatialMomentum)⟫_ℝ
      by unfold x₀; rw [inner_neg_left], neg_sq]
    ring
  have hSquare : s₂/4 ≤ S^2 := by
    have h := (sq_le_sq₀ (Real.sqrt_nonneg _) hS.le).2 hWidth
    rwa [Real.sq_sqrt (by positivity)] at h
  refine ⟨⟨hx'.trans hn, ?_⟩, ?_⟩
  · apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2*S)).mp
    rw [htSq]
    nlinarith [(sq_le_sq₀ hx₀ hS.le).2 hxU', sq_nonneg S, ht]
  · intro i hi
    have hTrans : (transverseMomentum spatialAxis k) i = k i := by
      simp [transverseMomentum, PiLp.sub_apply, PiLp.smul_apply, spatialAxis,
        EuclideanSpace.single_apply, hi]
    have hAxis := PiLp.norm_apply_le (transverseMomentum spatialAxis k) i
    rw [hTrans, Real.norm_eq_abs] at hAxis
    apply hAxis.trans
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rwa [Real.sq_sqrt (by positivity)]

private def transverseTubeOnSphere (δ : ℝ) : Set TemporalRayDirection :=
  {n | |(n : ChargeSpatialMomentum) 1| ≤ δ ∧ |(n : ChargeSpatialMomentum) 2| ≤ δ}

private theorem transverseTubeOnSphere_measurable (δ : ℝ) :
    MeasurableSet (transverseTubeOnSphere δ) := by
  have hc (i : Fin 3) : Continuous (fun n : TemporalRayDirection => |(n : ChargeSpatialMomentum) i|) :=
    continuous_abs.comp ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp continuous_subtype_val)
  exact (measurableSet_le (hc 1).measurable measurable_const).inter
    (measurableSet_le (hc 2).measurable measurable_const)

/-- The spatial volume on the exact compact band has radial
pushforward bounded by (6s_2,dr) on the interval of admissible radii.
The factor (r^2) is canceled by the quadratic solid-angle estimate. -/
theorem compactPairBand_lintegral_radial_le {m S s₁ s₂ : ℝ}
    (hm : 0 < m) (hS : 0 < S) (hs₂ : 0 < s₂) (hLarge : s₂/m ≤ S)
    (hWidth : Real.sqrt (s₂/4) ≤ S) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ k in compactPairBand m (S • (spatialAxis : ChargeSpatialMomentum)) s₁ s₂, g ‖k‖) ≤
      ENNReal.ofReal (6*s₂) * ∫⁻ r in Icc ((m^2/(2*s₂))*S) (2*S), g r := by
  let p := S • (spatialAxis : ChargeSpatialMomentum)
  let B := compactPairBand m p s₁ s₂
  let I := Icc ((m^2/(2*s₂))*S) (2*S)
  let W := Real.sqrt (s₂/4)
  let μ := (volume : Measure ChargeSpatialMomentum).toSphere
  let F := B.indicator (fun k => g ‖k‖)
  have hB : MeasurableSet B := compactPairBand_measurable m p s₁ s₂
  have hI : MeasurableSet I := measurableSet_Icc
  have hF : Measurable F := (hg.comp measurable_norm).indicator hB
  have hIW : I ⊆ Ioi (0:ℝ) := by
    exact fun _ hr => (by positivity : 0 < (m^2/(2*s₂))*S).trans_le hr.1
  have hNC (r : ℝ) (hr : 0 < r) (n : TemporalRayDirection) :
      ‖r • (n : ChargeSpatialMomentum)‖ = r := by
    rw [norm_smul, temporalRayDirection_norm n, mul_one, Real.norm_of_nonneg hr.le]
  have hTonelli : AEMeasurable
      (fun z : TemporalRayDirection × ℝ => ENNReal.ofReal (z.2^2) *
        F (z.2 • (z.1 : ChargeSpatialMomentum)))
      (μ.prod (volume.restrict (Ioi (0:ℝ)))) :=
    (((measurable_snd.pow_const 2).ennreal_ofReal).mul
      (hF.comp (measurable_snd.smul (measurable_subtype_coe.comp measurable_fst)))).aemeasurable
  have hInner (r : ℝ) (hr : 0 < r) :
      (∫⁻ n, ENNReal.ofReal (r^2) * F (r • (n : ChargeSpatialMomentum)) ∂μ) ≤
        I.indicator (fun r => ENNReal.ofReal (6*s₂) * g r) r := by
    by_cases hri : r ∈ I
    · rw [indicator_of_mem hri]
      let T := transverseTubeOnSphere (W/r)
      have hT : MeasurableSet T := transverseTubeOnSphere_measurable _
      have hCap : μ T ≤ ENNReal.ofReal (24*(W/r)^2) :=
        transverseTube_measure_le (div_nonneg (Real.sqrt_nonneg _) hr.le)
      have hW : W^2 = s₂/4 := Real.sq_sqrt (by positivity)
      calc
        _ ≤ ∫⁻ n, T.indicator (fun _ => ENNReal.ofReal (r^2) * g r) n ∂μ := by
          apply lintegral_mono
          intro n
          by_cases hn : r • (n : ChargeSpatialMomentum) ∈ B
          · have hh := (compactPairBand_radial_support hm hS hs₂ hLarge hWidth hn).2
            have hTube (i : Fin 3) (hi : i ≠ 0) : |(n : ChargeSpatialMomentum) i| ≤ W/r := by
              apply (le_div_iff₀ hr).2
              have h := hh i hi
              rwa [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hr, mul_comm] at h
            have hmT : n ∈ T := ⟨hTube 1 (by decide), hTube 2 (by decide)⟩
            rw [indicator_of_mem hmT]
            change ENNReal.ofReal (r^2) * B.indicator (fun k => g ‖k‖) (r • (n : ChargeSpatialMomentum)) ≤ _
            rw [indicator_of_mem hn, hNC r hr n]
          · change ENNReal.ofReal (r^2) * B.indicator (fun k => g ‖k‖) (r • (n : ChargeSpatialMomentum)) ≤ _
            rw [indicator_of_notMem hn, mul_zero]
            exact zero_le _
        _ = (ENNReal.ofReal (r^2) * g r) * μ T := by
          rw [lintegral_indicator hT, lintegral_const, Measure.restrict_apply_univ]
        _ ≤ (ENNReal.ofReal (r^2) * g r) * ENNReal.ofReal (24*(W/r)^2) :=
          mul_le_mul_left' hCap _
        _ = _ := by
          rw [mul_right_comm, ← ENNReal.ofReal_mul (sq_nonneg r)]
          congr 2
          calc
            r^2 * (24*(W/r)^2) = 24*W^2 := by field_simp
            _ = 6*s₂ := by rw [hW]; ring
    · rw [indicator_of_notMem hri]
      refine le_of_eq ?_
      suffices h0 : ∀ n : TemporalRayDirection, F (r • (n : ChargeSpatialMomentum)) = 0 by
        simp [h0]
      intro n
      change B.indicator (fun k => g ‖k‖) (r • (n : ChargeSpatialMomentum)) = 0
      apply indicator_of_notMem
      intro hn
      have hh := (compactPairBand_radial_support hm hS hs₂ hLarge hWidth hn).1
      rw [hNC r hr n] at hh
      exact hri hh
  calc
    (∫⁻ k in B, g ‖k‖) = ∫⁻ k, F k := (lintegral_indicator hB _).symm
    _ = ∫⁻ n, (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^2) *
        F (r • (n : ChargeSpatialMomentum))) ∂μ := temporal_lintegral_spatial_polar _ hF
    _ = ∫⁻ r in Ioi (0:ℝ), ∫⁻ n, ENNReal.ofReal (r^2) *
        F (r • (n : ChargeSpatialMomentum)) ∂μ := lintegral_lintegral_swap hTonelli
    _ ≤ ∫⁻ r in Ioi (0:ℝ), I.indicator (fun r => ENNReal.ofReal (6*s₂) * g r) r := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact hInner r hr
    _ = ∫⁻ r in I, ENNReal.ofReal (6*s₂) * g r := by
      rw [lintegral_indicator hI, Measure.restrict_restrict hI, inter_eq_left.mpr hIW]
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end UV.NextOpticalRadial
