import UV.ContinueTemporalFlux
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Differentiation of the boundary flux without differentiating the
normal profiles in the energy identity. -/

noncomputable section

namespace UV.TemporalRay

open MeasureTheory Filter Set
open scoped Topology

def normalFamilyFlux (D : NormalChannel) (U : ∀ y ≥ 0, NormalTransfer D.a (D.potential y))
    (y : ℝ) : ℝ :=
  if hy : 0 ≤ y then boundaryFlux D.a (U y hy) else 0

private theorem temporal_pairing_sub_right (D : NormalChannel) {u v w : ℝ → ℝ}
    (hu : MemLp u 2 normalRayMeasure) (hv : MemLp v 2 normalRayMeasure)
    (hw : MemLp w 2 normalRayMeasure) :
    temporalPairing D u (fun r => w r-v r) = temporalPairing D u w - temporalPairing D u v := by
  unfold temporalPairing
  have hs := integral_sub (temporal_pairing_integrable D hu hw) (temporal_pairing_integrable D hu hv)
  unfold normalRayMeasure at hs
  rw [← hs]
  exact integral_congr_ae (Eventually.of_forall fun r => by ring)

theorem transverse_flux_slope_error (D : NormalChannel) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z)
    (u : NormalTransfer D.a (D.potential y)) (v : NormalTransfer D.a (D.potential z)) :
    |temporalPairing D u.amplitude v.amplitude - temporalPairing D u.amplitude u.amplitude| ≤
      (D.parMax^2/(D.spMin*D.k^2)*rayL2Size u.amplitude^2) * |z-y| := by
  rw [← temporal_pairing_sub_right D u.amplitude_L2 u.amplitude_L2 v.amplitude_L2]
  apply (temporal_pairing_bound D u.amplitude_L2 (v.amplitude_L2.sub u.amplitude_L2)).trans
  have hC : 0 ≤ D.parMax := (D.temporal_bound 0 le_rfl).1.trans (D.temporal_bound 0 le_rfl).2
  have hp := transverse_amplitude_L2_stability D hy hz u v
  calc
    _ ≤ D.parMax * (rayL2Size u.amplitude *
        (|z-y| * D.parMax / (D.spMin*D.k^2) * rayL2Size u.amplitude)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (ray_L2_size_nonneg _)) hC
    _ = _ := by ring

theorem normal_family_flux_hasDerivWithinAt (D : NormalChannel)
    (U : ∀ y ≥ 0, NormalTransfer D.a (D.potential y)) {y : ℝ} (hy : 0 ≤ y) :
    HasDerivWithinAt (normalFamilyFlux D U)
      (temporalPairing D (U y hy).amplitude (U y hy).amplitude) (Ici 0) y := by
  let u := U y hy
  let A := temporalPairing D u.amplitude u.amplitude
  let C := D.parMax^2/(D.spMin*D.k^2)*rayL2Size u.amplitude^2
  rw [hasDerivWithinAt_iff_tendsto_slope]
  change Tendsto (slope (normalFamilyFlux D U) y) (𝓝[Ici 0 \ {y}] y) (𝓝 A)
  have hlim : Tendsto (fun z : ℝ => C*|z-y|) (𝓝[Ici 0 \ {y}] y) (𝓝 0) := by
    have hc : Continuous (fun z : ℝ => C*|z-y|) := by fun_prop
    have h : Tendsto (fun z : ℝ => C*|z-y|) (𝓝[Ici 0 \ {y}] y) (𝓝 (C*|y-y|)) :=
      hc.continuousAt.continuousWithinAt
    simpa only [sub_self,abs_zero,mul_zero] using h
  have h0 : Tendsto (fun z => slope (normalFamilyFlux D U) y z-A) (𝓝[Ici 0 \ {y}] y) (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [self_mem_nhdsWithin (s := Ici (0:ℝ) \ {y})] with z hz
    have hz₀ : 0 ≤ z := hz.1
    have hne : z-y ≠ 0 := sub_ne_zero.mpr hz.2
    rw [slope_def_field]
    simp only [normalFamilyFlux,dif_pos hz₀,dif_pos hy]
    rw [transverse_flux_difference D hy hz₀ u (U z hz₀),mul_comm (z-y),mul_div_cancel_right₀ _ hne,
      Real.norm_eq_abs]
    exact transverse_flux_slope_error D hy hz₀ u (U z hz₀)
  have h := h0.add_const A
  simpa only [sub_add_cancel,zero_add] using h

end UV.TemporalRay
