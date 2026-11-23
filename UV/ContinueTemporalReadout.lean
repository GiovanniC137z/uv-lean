import UV.ContinueTemporalInterior

/-! The exact derivative of the retained normal transfer with respect
to the squared real carrier frequency. -/

noncomputable section

namespace UV.TemporalRay

open MeasureTheory Filter Set
open scoped Topology

def temporalReadoutIntegral (D : NormalChannel) (u v : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..r, inverseNormalWeight D u t * temporalTail D u v t

private theorem temporal_readout_continuousOn (D : NormalChannel) (u : NormalProfile)
    (hu : ∀ r ≥ 0, 0 < u.amplitude r) {v : ℝ → ℝ} (hv : MemLp v 2 normalRayMeasure) :
    ContinuousOn (fun t => inverseNormalWeight D u.amplitude t * temporalTail D u.amplitude v t)
      (Ici 0) :=
  (inverse_normal_weight_continuousOn D u hu).mul (continuousOn_temporal_tail D u.amplitude_L2 hv)

private theorem temporal_readout_error (D : NormalChannel) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z)
    (u : NormalTransfer D.a (D.potential y)) (v : NormalTransfer D.a (D.potential z))
    (hu : ∀ r ≥ 0, 0 < u.amplitude r) {r : ℝ} (hr : 0 ≤ r) :
    ‖temporalReadoutIntegral D u.amplitude v.amplitude r -
        temporalReadoutIntegral D u.amplitude u.amplitude r‖ ≤
      ((∫ t in (0:ℝ)..r, inverseNormalWeight D u.amplitude t) *
        (D.parMax^2 / (D.spMin*D.k^2) * rayL2Size u.amplitude^2)) * |z-y| := by
  let W := inverseNormalWeight D u.amplitude
  let C := D.parMax^2 / (D.spMin*D.k^2) * rayL2Size u.amplitude^2
  have hs : uIcc (0:ℝ) r ⊆ Ici 0 := by rw [uIcc_of_le hr]; exact fun _ ht => ht.1
  have hA : IntervalIntegrable (fun t => W t*temporalTail D u.amplitude v.amplitude t) volume 0 r :=
    ((temporal_readout_continuousOn D u.toNormalProfile hu v.amplitude_L2).mono hs).intervalIntegrable
  have hB : IntervalIntegrable (fun t => W t*temporalTail D u.amplitude u.amplitude t) volume 0 r :=
    ((temporal_readout_continuousOn D u.toNormalProfile hu u.amplitude_L2).mono hs).intervalIntegrable
  have hW : IntervalIntegrable W volume 0 r :=
    ((inverse_normal_weight_continuousOn D u.toNormalProfile hu).mono hs).intervalIntegrable
  change ‖(∫ t in (0:ℝ)..r, W t*temporalTail D u.amplitude v.amplitude t) -
    (∫ t in (0:ℝ)..r, W t*temporalTail D u.amplitude u.amplitude t)‖ ≤ _
  rw [← intervalIntegral.integral_sub hA hB]
  have hBound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioc 0 r →
      ‖W t*temporalTail D u.amplitude v.amplitude t -
        W t*temporalTail D u.amplitude u.amplitude t‖ ≤ (C * |z-y|)*W t := by
    apply Eventually.of_forall
    intro t ht
    have ht₀ : 0 ≤ t := ht.1.le
    have hW₀ : 0 ≤ W t := by
      unfold W inverseNormalWeight
      exact inv_nonneg.mpr (mul_nonneg (D.aMin_pos.le.trans (D.a_bound t ht₀).1) (sq_nonneg _))
    rw [← mul_sub,norm_mul,Real.norm_of_nonneg hW₀,Real.norm_eq_abs,
      ← temporal_tail_sub_right D u.amplitude_L2 u.amplitude_L2 v.amplitude_L2 ht₀,mul_comm (C*|z-y|)]
    apply mul_le_mul_of_nonneg_left _ hW₀
    have hs := transverse_amplitude_L2_stability D hy hz u v
    have hC : 0 ≤ D.parMax := (D.temporal_bound 0 le_rfl).1.trans (D.temporal_bound 0 le_rfl).2
    calc
      _ ≤ D.parMax * (rayL2Size u.amplitude * rayL2Size (fun r => v.amplitude r-u.amplitude r)) :=
        temporal_tail_bound D u.amplitude_L2 (v.amplitude_L2.sub u.amplitude_L2) ht₀
      _ ≤ D.parMax * (rayL2Size u.amplitude *
          (|z-y| * D.parMax / (D.spMin*D.k^2) * rayL2Size u.amplitude)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (ray_L2_size_nonneg _)) hC
      _ = _ := by dsimp [C]; ring
  have h := intervalIntegral.norm_integral_le_of_norm_le hr hBound (hW.const_mul (C * |z-y|))
  rw [intervalIntegral.integral_const_mul] at h
  refine h.trans_eq ?_
  change (C*|z-y|) * (∫ t in (0:ℝ)..r, W t) = _
  ring

def familyNormalReadout (D : NormalChannel) (U : ∀ y ≥ 0, NormalTransfer D.a (D.potential y))
    (r y : ℝ) : ℝ := if hy : 0 ≤ y then (U y hy).amplitude r else 0

theorem normal_family_readout_hasDerivWithinAt (D : NormalChannel)
    (U : ∀ y ≥ 0, NormalTransfer D.a (D.potential y)) {y : ℝ} (hy : 0 ≤ y)
    (hu : ∀ t ≥ 0, 0 < (U y hy).amplitude t) {r : ℝ} (hr : 0 ≤ r) :
    HasDerivWithinAt (familyNormalReadout D U r)
      (-(U y hy).amplitude r * temporalReadoutIntegral D (U y hy).amplitude (U y hy).amplitude r)
      (Ici 0) y := by
  let u := U y hy
  let L := -u.amplitude r * temporalReadoutIntegral D u.amplitude u.amplitude r
  let C := ‖u.amplitude r‖ * ((∫ t in (0:ℝ)..r, inverseNormalWeight D u.amplitude t) *
    (D.parMax^2 / (D.spMin*D.k^2) * rayL2Size u.amplitude^2))
  rw [hasDerivWithinAt_iff_tendsto_slope]
  change Tendsto (slope (familyNormalReadout D U r) y) (𝓝[Ici 0 \ {y}] y) (𝓝 L)
  have hlim : Tendsto (fun z : ℝ => C * |z-y|) (𝓝[Ici 0 \ {y}] y) (𝓝 0) := by
    have hc : Continuous (fun z : ℝ => C * |z-y|) := by fun_prop
    have h : Tendsto (fun z : ℝ => C * |z-y|) (𝓝[Ici 0 \ {y}] y) (𝓝 (C * |y-y|)) :=
      hc.continuousAt.continuousWithinAt
    simpa only [sub_self,abs_zero,mul_zero] using h
  have h0 : Tendsto (fun z => slope (familyNormalReadout D U r) y z-L)
      (𝓝[Ici 0 \ {y}] y) (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [self_mem_nhdsWithin (s := Ici (0:ℝ) \ {y})] with z hz
    have hz₀ : 0 ≤ z := hz.1
    have hne : z-y ≠ 0 := sub_ne_zero.mpr hz.2
    let v := U z hz₀
    have he : v.amplitude r-u.amplitude r =
        -(z-y)*u.amplitude r*temporalReadoutIntegral D u.amplitude v.amplitude r :=
      transverse_amplitude_exact_difference D u v hu hr
    have hs : (v.amplitude r-u.amplitude r)/(z-y) = -u.amplitude r*
        temporalReadoutIntegral D u.amplitude v.amplitude r := by
      rw [he]
      field_simp
    rw [slope_def_field]
    simp only [familyNormalReadout,dif_pos hz₀,dif_pos hy]
    change ‖(v.amplitude r-u.amplitude r)/(z-y)-L‖ ≤ C * |z-y|
    rw [hs,show L = -u.amplitude r*temporalReadoutIntegral D u.amplitude u.amplitude r from rfl,
      ← mul_sub,norm_mul,norm_neg]
    unfold C
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (temporal_readout_error D hy hz₀ u v hu hr) (norm_nonneg _)
  have h := h0.add_const L
  simpa only [sub_add_cancel,zero_add] using h

end UV.TemporalRay
