import UV.ContinueTemporalReadout
import UV.ContinueTemporalMaximum

/-! Strict dependence of every positive-depth readout on a nonzero
temporal curvature coefficient. -/

noncomputable section

namespace UV.TemporalRay

open MeasureTheory Filter Set
open scoped Topology

private theorem temporal_tail_nonneg (D : NormalChannel) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z)
    (u : NormalTransfer D.a (D.potential y)) (v : NormalTransfer D.a (D.potential z))
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ temporalTail D u.amplitude v.amplitude t := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi t) measurableSet_Ioi] with s hs
  have hs' := ht.trans hs.le
  exact mul_nonneg (mul_nonneg (D.temporal_bound s hs').1
    (normal_transfer_nonneg D hy u hs')) (normal_transfer_nonneg D hz v hs')

theorem temporal_tail_zero_depth_pos (D : NormalChannel) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z)
    (u : NormalTransfer D.a (D.potential y)) (v : NormalTransfer D.a (D.potential z))
    {s : ℝ} (hs : 0 < s) (hD : 0 < D.temporal s) : 0 < temporalTail D u.amplitude v.amplitude 0 := by
  let f (r : ℝ) := D.temporal r*u.amplitude r*v.amplitude r
  have hi := temporal_pairing_integrable D u.amplitude_L2 v.amplitude_L2
  have hn : 0 ≤ᵐ[normalRayMeasure] f := by
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi (0:ℝ)) measurableSet_Ioi] with r hr
    exact mul_nonneg (mul_nonneg (D.temporal_bound r hr.le).1
      (normal_transfer_nonneg D hy u hr.le)) (normal_transfer_nonneg D hz v hr.le)
  change 0 < ∫ r, f r ∂normalRayMeasure
  rw [integral_pos_iff_support_of_nonneg_ae hn hi]
  have hfs : 0 < f s := mul_pos (mul_pos hD (normal_transfer_positive D hy u hs.le))
    (normal_transfer_positive D hz v hs.le)
  have hc : ContinuousAt f s := (D.continuous_temporal.continuousAt.mul
    (u.has_gradient s hs.le).continuousAt).mul (v.has_gradient s hs.le).continuousAt
  have he : ({r | 0 < f r} ∩ Ioi 0) ∈ 𝓝 s :=
    inter_mem (hc (Ioi_mem_nhds hfs)) (Ioi_mem_nhds hs)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp he
  have hv₀ : (volume : Measure ℝ) (Metric.ball s δ) = ENNReal.ofReal (2*δ) := Real.volume_ball _ _
  have hm : 0 < normalRayMeasure (Metric.ball s δ) := by
    rw [normalRayMeasure,Measure.restrict_apply Metric.isOpen_ball.measurableSet,
      inter_eq_left.mpr (fun r hr => (hball hr).2),hv₀,ENNReal.ofReal_pos]
    positivity
  exact hm.trans_le (measure_mono fun r hr => (hball hr).1.ne')

theorem temporal_readout_positive (D : NormalChannel) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z)
    (u : NormalTransfer D.a (D.potential y)) (v : NormalTransfer D.a (D.potential z))
    {s r : ℝ} (hs : 0 < s) (hD : 0 < D.temporal s) (hr : 0 < r) :
    0 < temporalReadoutIntegral D u.amplitude v.amplitude r := by
  have hp (t : ℝ) (ht : 0 ≤ t) : 0 < inverseNormalWeight D u.amplitude t := by
    unfold inverseNormalWeight
    exact inv_pos.mpr (mul_pos (D.aMin_pos.trans_le (D.a_bound t ht).1)
      (pow_pos (normal_transfer_positive D hy u ht) 2))
  unfold temporalReadoutIntegral
  apply intervalIntegral.integral_pos hr
  · exact ((inverse_normal_weight_continuousOn D u.toNormalProfile
      (fun _ ht => normal_transfer_positive D hy u ht)).mul
      (continuousOn_temporal_tail D u.amplitude_L2 v.amplitude_L2)).mono fun _ ht => ht.1
  · exact fun t ht => mul_nonneg (hp t ht.1.le).le (temporal_tail_nonneg D hy hz u v ht.1.le)
  · exact ⟨0,⟨le_rfl,hr.le⟩,mul_pos (hp 0 le_rfl) (temporal_tail_zero_depth_pos D hy hz u v hs hD)⟩

theorem normal_transfer_strict_in_frequency (D : NormalChannel) {y z : ℝ} (hy : 0 ≤ y) (hyz : y < z)
    (u : NormalTransfer D.a (D.potential y)) (v : NormalTransfer D.a (D.potential z))
    {s r : ℝ} (hs : 0 < s) (hD : 0 < D.temporal s) (hr : 0 < r) :
    v.amplitude r < u.amplitude r := by
  have hz := hy.trans hyz.le
  have h := transverse_amplitude_exact_difference D u v
    (fun _ ht => normal_transfer_positive D hy u ht) hr.le
  apply sub_neg.mp
  rw [h]
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith)
    (normal_transfer_positive D hy u hr.le)) (temporal_readout_positive D hy hz u v hs hD hr)

theorem normal_readout_frequency_independent_iff (D : NormalChannel)
    (U : ∀ y ≥ 0, NormalTransfer D.a (D.potential y)) {r : ℝ} (hr : 0 < r) :
    (∀ y (hy : 0 ≤ y), (U y hy).amplitude r = (U 0 le_rfl).amplitude r) ↔
      ∀ t ≥ 0, D.temporal t = 0 := by
  constructor
  · intro hc t ht
    by_contra hne
    have hpos := lt_of_le_of_ne (D.temporal_bound t ht).1 (Ne.symm hne)
    have hw : ∃ s, 0 < s ∧ 0 < D.temporal s := by
      by_cases ht' : 0 < t
      · exact ⟨t,ht',hpos⟩
      · have ht₀ := le_antisymm (le_of_not_gt ht') ht
        rw [ht₀] at hpos
        have he : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < D.temporal s :=
          D.continuous_temporal.continuousAt.continuousWithinAt.eventually (Ioi_mem_nhds hpos)
        have hz : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < s := self_mem_nhdsWithin
        exact (hz.and he).exists
    obtain ⟨s,hs,hD⟩ := hw
    exact (normal_transfer_strict_in_frequency D le_rfl zero_lt_one (U 0 le_rfl) (U 1 zero_le_one)
      hs hD hr).ne (hc 1 zero_le_one)
  · intro hc y hy
    have h := transverse_amplitude_exact_difference D (U 0 le_rfl) (U y hy)
      (fun _ ht => normal_transfer_positive D le_rfl (U 0 le_rfl) ht) hr.le
    have ht (t : ℝ) (ht : t ∈ uIcc (0:ℝ) r) :
        temporalTail D (U 0 le_rfl).amplitude (U y hy).amplitude t = 0 := by
      rw [uIcc_of_le hr.le] at ht
      unfold temporalTail
      calc
        _ = ∫ s in Ioi t, (0:ℝ) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro s hs
          dsimp only
          rw [hc s (ht.1.trans hs.le),zero_mul,zero_mul]
        _ = 0 := integral_zero _ _
    have hi : (∫ t in (0:ℝ)..r, inverseNormalWeight D (U 0 le_rfl).amplitude t *
        temporalTail D (U 0 le_rfl).amplitude (U y hy).amplitude t) = 0 := by
      calc
        _ = ∫ t in (0:ℝ)..r, (0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht'
          dsimp only
          rw [ht t ht',mul_zero]
        _ = 0 := intervalIntegral.integral_zero
    rw [hi,mul_zero,sub_eq_zero] at h
    exact h

end UV.TemporalRay
