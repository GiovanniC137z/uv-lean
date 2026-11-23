import UV.ContinueTemporalDerivative
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The two-energy Wronskian and pointwise comparison for temporal normal transfer. -/

noncomputable section

namespace UV.TemporalRay

open MeasureTheory Filter Set
open scoped Topology

def normalFluxProfile (D : NormalChannel) {y : ℝ} (u : NormalTransfer D.a (D.potential y))
    (r : ℝ) : ℝ := D.a r * u.gradient r

def normalWronskian (D : NormalChannel) {y z : ℝ}
    (u : NormalTransfer D.a (D.potential y)) (v : NormalTransfer D.a (D.potential z)) (r : ℝ) : ℝ :=
  normalFluxProfile D v r * u.amplitude r - normalFluxProfile D u r * v.amplitude r

theorem normal_wronskian_hasDerivAt (D : NormalChannel) {y z : ℝ}
    (u : NormalTransfer D.a (D.potential y)) (v : NormalTransfer D.a (D.potential z))
    {r : ℝ} (hr : 0 ≤ r) :
    HasDerivAt (normalWronskian D u v)
      ((z-y) * (D.temporal r * u.amplitude r * v.amplitude r)) r := by
  have hd := ((v.flux_derivative r hr).mul (u.has_gradient r hr)).sub
    ((u.flux_derivative r hr).mul (v.has_gradient r hr))
  convert hd using 1
  unfold NormalChannel.potential modePotential
  ring

theorem normal_wronskian_eq_tail (D : NormalChannel) {y z : ℝ}
    (u : NormalTransfer D.a (D.potential y)) (v : NormalTransfer D.a (D.potential z))
    {t : ℝ} (ht : 0 ≤ t) :
    normalWronskian D u v t =
      -(z-y) * ∫ r in Ioi t, D.temporal r*u.amplitude r*v.amplitude r := by
  have hba (r : ℝ) (hr : 0 < r) := D.abs_a_bound hr.le
  have hW : IntegrableOn (normalWronskian D u v) (Ioi 0) :=
    (ray_product_integrable v.gradient_L2 u.amplitude_L2 D.continuous_a.measurable hba).sub
    (ray_product_integrable u.gradient_L2 v.amplitude_L2 D.continuous_a.measurable hba)
  have hI : IntegrableOn (fun r => (z-y) * (D.temporal r*u.amplitude r*v.amplitude r)) (Ioi 0) :=
    (temporal_pairing_integrable D u.amplitude_L2 v.amplitude_L2).const_mul _
  have h := integral_ray_derivative (a := t)
    (fun r hr => normal_wronskian_hasDerivAt D u v (ht.trans hr))
    (hW.mono_set (Ioi_subset_Ioi ht)) (hI.mono_set (Ioi_subset_Ioi ht))
  rw [integral_const_mul] at h
  linarith

theorem normal_ratio_hasDerivAt (D : NormalChannel) {y z : ℝ}
    (u : NormalTransfer D.a (D.potential y)) (v : NormalTransfer D.a (D.potential z))
    {r : ℝ} (hr : 0 ≤ r) (hu : u.amplitude r ≠ 0) :
    HasDerivAt (fun s => v.amplitude s/u.amplitude s)
      (normalWronskian D u v r / (D.a r * u.amplitude r^2)) r := by
  have hd := (v.has_gradient r hr).div (u.has_gradient r hr) hu
  convert hd using 1
  have ha : D.a r ≠ 0 := (D.aMin_pos.trans_le (D.a_bound r hr).1).ne'
  unfold normalWronskian normalFluxProfile
  field_simp

theorem normal_ratio_antitone (D : NormalChannel) {y z : ℝ} (hyz : y ≤ z)
    (u : NormalTransfer D.a (D.potential y)) (v : NormalTransfer D.a (D.potential z))
    (hu : ∀ r ≥ 0, 0 < u.amplitude r) (hv : ∀ r ≥ 0, 0 ≤ v.amplitude r) :
    AntitoneOn (fun r => v.amplitude r/u.amplitude r) (Ici 0) := by
  have hd (r : ℝ) (hr : 0 ≤ r) := normal_ratio_hasDerivAt D u v hr (hu r hr).ne'
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · exact fun r hr => (hd r hr).continuousAt.continuousWithinAt
  · intro r hr
    have h0 : 0 ≤ r := interior_subset hr
    exact (hd r h0).differentiableAt.differentiableWithinAt
  · intro r hr
    have hr₀ : 0 ≤ r := interior_subset hr
    rw [(hd r hr₀).deriv,normal_wronskian_eq_tail D u v hr₀]
    have hI : 0 ≤ ∫ s in Ioi r, D.temporal s*u.amplitude s*v.amplitude s := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi r) measurableSet_Ioi] with s hs
      have h : 0 ≤ s := hr₀.trans hs.le
      exact mul_nonneg (mul_nonneg (D.temporal_bound s h).1 (hu s h).le) (hv s h)
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) hI)
      (mul_nonneg (D.aMin_pos.le.trans (D.a_bound r hr₀).1) (sq_nonneg _))

/-- Positive transfer profiles are ordered at every retained depth. The
Wronskian comparison puts the temporal weight on the actual whole ray. -/
theorem normal_transfer_antitone (D : NormalChannel) {y z : ℝ} (hyz : y ≤ z)
    (u : NormalTransfer D.a (D.potential y)) (v : NormalTransfer D.a (D.potential z))
    (hu : ∀ r ≥ 0, 0 < u.amplitude r) (hv : ∀ r ≥ 0, 0 ≤ v.amplitude r)
    {r : ℝ} (hr : 0 ≤ r) : v.amplitude r ≤ u.amplitude r := by
  have h := normal_ratio_antitone D hyz u v hu hv (left_mem_Ici : (0:ℝ) ∈ Ici 0) hr hr
  change v.amplitude r/u.amplitude r ≤ v.amplitude 0/u.amplitude 0 at h
  rw [u.boundary_one,v.boundary_one,div_self one_ne_zero] at h
  exact (div_le_one₀ (hu r hr)).mp h

end UV.TemporalRay
