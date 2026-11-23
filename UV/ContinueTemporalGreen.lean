import UV.ContinueTemporalStrict
import Mathlib.MeasureTheory.Integral.Prod

/-! The positive half-line kernel obtained from the actual minimizing
profile and the zero-boundary second solution. -/

noncomputable section

namespace UV.TemporalRay

open MeasureTheory Filter Set
open scoped Topology

def normalGreenKernel (D : NormalChannel) (u : ℝ → ℝ) (r s : ℝ) : ℝ :=
  u r * u s * ∫ t in (0:ℝ)..min r s, inverseNormalWeight D u t

theorem normal_green_kernel_positive (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (u : NormalTransfer D.a (D.potential y)) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    0 < normalGreenKernel D u.amplitude r s := by
  have hf (t : ℝ) (ht : 0 ≤ t) : 0 < inverseNormalWeight D u.amplitude t :=
    inv_pos.mpr (mul_pos (D.aMin_pos.trans_le (D.a_bound t ht).1)
      (pow_pos (normal_transfer_positive D hy u ht) 2))
  have ht : 0 < min r s := lt_min hr hs
  unfold normalGreenKernel
  refine mul_pos (mul_pos (normal_transfer_positive D hy u hr.le)
    (normal_transfer_positive D hy u hs.le)) (intervalIntegral.integral_pos ht ?_ ?_ ?_)
  · exact (inverse_normal_weight_continuousOn D u.toNormalProfile
      (fun _ ht => normal_transfer_positive D hy u ht)).mono fun _ ht => ht.1
  · exact fun t ht => (hf t ht.1.le).le
  · exact ⟨0,⟨le_rfl,ht.le⟩,hf 0 le_rfl⟩

theorem normal_green_readout_identity (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (u : NormalTransfer D.a (D.potential y)) {r : ℝ} (hr : 0 ≤ r) :
    u.amplitude r * temporalReadoutIntegral D u.amplitude u.amplitude r =
      ∫ s in Ioi (0:ℝ), normalGreenKernel D u.amplitude r s * D.temporal s * u.amplitude s := by
  let W := inverseNormalWeight D u.amplitude
  let g (s : ℝ) := D.temporal s*u.amplitude s*u.amplitude s
  let μ := (volume : Measure ℝ).restrict (Ioc 0 r)
  let ν := normalRayMeasure
  letI : SFinite ν := by dsimp [ν,normalRayMeasure]; infer_instance
  letI : SFinite μ := by dsimp [μ]; infer_instance
  let F (t s : ℝ) := if t < s then W t*g s else 0
  have hW : Integrable W μ :=
    ((inverse_normal_weight_continuousOn D u.toNormalProfile
      (fun _ ht => normal_transfer_positive D hy u ht)).mono
        (show uIcc (0:ℝ) r ⊆ Ici 0 by rw [uIcc_of_le hr]; exact fun _ ht => ht.1)).intervalIntegrable.1
  have hg : Integrable g ν := temporal_pairing_integrable D u.amplitude_L2 u.amplitude_L2
  have hL : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} := measurableSet_lt measurable_fst measurable_snd
  have hF : Integrable (Function.uncurry F) (μ.prod ν) := by
    convert (hW.mul_prod hg).indicator hL using 1
  have ht (t : ℝ) (ht : 0 ≤ t) :
      (∫ s, F t s ∂ν) = W t * temporalTail D u.amplitude u.amplitude t := by
    have he : F t = fun s => W t * (Ioi t).indicator g s := by
      funext s
      by_cases h : t < s <;> simp [F,h,Set.indicator]
    rw [he,integral_const_mul,integral_indicator measurableSet_Ioi]
    unfold ν normalRayMeasure temporalTail
    rw [Measure.restrict_restrict measurableSet_Ioi,inter_eq_left.mpr (Ioi_subset_Ioi ht)]
  have hs (s : ℝ) (hs : 0 ≤ s) : (∫ t, F t s ∂μ) =
      (∫ t in (0:ℝ)..min r s, W t) * g s := by
    have he : (fun t => F t s) = fun t => (Iio s).indicator W t * g s := by
      funext t
      by_cases h : t < s <;> simp [F,h,Set.indicator]
    rw [he,integral_mul_const,integral_indicator measurableSet_Iio]
    unfold μ
    rw [Measure.restrict_restrict measurableSet_Iio,intervalIntegral.integral_of_le (le_min hr hs)]
    congr 1
    apply setIntegral_congr_set
    have hE : Iio s =ᵐ[(volume : Measure ℝ)] Iic s := Iio_ae_eq_Iic
    apply (hE.inter EventuallyEq.rfl).trans
    rw [show Iic s ∩ Ioc 0 r = Ioc 0 (min r s) by
      ext t; simp only [mem_inter_iff,mem_Iic,mem_Ioc,le_min_iff]; tauto]
  unfold temporalReadoutIntegral
  rw [intervalIntegral.integral_of_le hr]
  have hleft : (∫ t in Ioc (0:ℝ) r, inverseNormalWeight D u.amplitude t *
      temporalTail D u.amplitude u.amplitude t) = ∫ t, ∫ s, F t s ∂ν ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioc (0:ℝ) r) measurableSet_Ioc] with t ht'
    exact (ht t ht'.1.le).symm
  rw [hleft,integral_integral_swap hF,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi (0:ℝ)) measurableSet_Ioi] with s hs'
  change u.amplitude r*(∫ t, F t s ∂μ) = _
  rw [hs s hs'.le]
  unfold g normalGreenKernel W
  ring

theorem normal_family_readout_green_derivative (D : NormalChannel)
    (U : ∀ y ≥ 0, NormalTransfer D.a (D.potential y)) {y : ℝ} (hy : 0 ≤ y)
    {r : ℝ} (hr : 0 ≤ r) :
    HasDerivWithinAt (familyNormalReadout D U r)
      (-(∫ s in Ioi (0:ℝ), normalGreenKernel D (U y hy).amplitude r s *
        D.temporal s * (U y hy).amplitude s)) (Ici 0) y := by
  rw [← normal_green_readout_identity D hy (U y hy) hr,← neg_mul]
  exact normal_family_readout_hasDerivWithinAt D U hy
    (fun _ ht => normal_transfer_positive D hy (U y hy) ht) hr

end UV.TemporalRay
