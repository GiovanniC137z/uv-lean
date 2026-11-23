import UV.ContinueTemporalGreen
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Dirichlet boundary data and the unit flux jump for the explicit
normal Green kernel. -/

noncomputable section

namespace UV.TemporalRay

open MeasureTheory Filter Set
open scoped Topology

def normalLeftPrimitive (D : NormalChannel) (u : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..r, inverseNormalWeight D u t

def normalLeftSolution (D : NormalChannel) (u : ℝ → ℝ) (r : ℝ) : ℝ :=
  u r * normalLeftPrimitive D u r

def normalLeftFlux (D : NormalChannel) {y : ℝ}
    (u : NormalTransfer D.a (D.potential y)) (r : ℝ) : ℝ :=
  normalFluxProfile D u r * normalLeftPrimitive D u.amplitude r + (u.amplitude r)⁻¹

private theorem normal_left_primitive_hasDerivAt (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (u : NormalTransfer D.a (D.potential y)) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (normalLeftPrimitive D u.amplitude) (inverseNormalWeight D u.amplitude r) r := by
  have hW := inverse_normal_weight_continuousOn D u.toNormalProfile
    (fun _ ht => normal_transfer_positive D hy u ht)
  have hI : IntervalIntegrable (inverseNormalWeight D u.amplitude) volume 0 r :=
    (hW.mono (by rw [uIcc_of_le hr.le]; exact fun _ ht => ht.1)).intervalIntegrable
  have hc := (hW r hr.le).continuousAt (Ici_mem_nhds hr)
  exact intervalIntegral.integral_hasDerivAt_right hI (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi (hW.mono Ioi_subset_Ici_self) r hr) hc

theorem normal_left_solution_hasDerivAt (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (u : NormalTransfer D.a (D.potential y)) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (normalLeftSolution D u.amplitude) (normalLeftFlux D u r/(D.a r)) r := by
  have ha : D.a r ≠ 0 := (D.aMin_pos.trans_le (D.a_bound r hr.le).1).ne'
  have hu := (normal_transfer_positive D hy u hr.le).ne'
  convert (u.has_gradient r hr.le).mul (normal_left_primitive_hasDerivAt D hy u hr) using 1
  unfold normalLeftFlux normalFluxProfile inverseNormalWeight
  field_simp

theorem normal_left_flux_hasDerivAt (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (u : NormalTransfer D.a (D.potential y)) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (normalLeftFlux D u) (D.potential y r * normalLeftSolution D u.amplitude r) r := by
  have ha : D.a r ≠ 0 := (D.aMin_pos.trans_le (D.a_bound r hr.le).1).ne'
  have hu := (normal_transfer_positive D hy u hr.le).ne'
  have hd₁ := u.flux_derivative r hr.le
  have hd₂ := normal_left_primitive_hasDerivAt D hy u hr
  have hd₃ := (hasDerivAt_inv hu).comp r (u.has_gradient r hr.le)
  convert (hd₁.mul hd₂).add hd₃ using 1
  unfold normalLeftSolution inverseNormalWeight
  field_simp
  ring

theorem normal_green_piecewise (D : NormalChannel) {y : ℝ}
    (u : NormalTransfer D.a (D.potential y)) (r s : ℝ) :
    normalGreenKernel D u.amplitude r s =
      if r ≤ s then normalLeftSolution D u.amplitude r*u.amplitude s
      else u.amplitude r*normalLeftSolution D u.amplitude s := by
  by_cases h : r ≤ s
  · rw [if_pos h,normalGreenKernel,min_eq_left h,normalLeftSolution,normalLeftPrimitive]
    ring
  · rw [if_neg h,normalGreenKernel,min_eq_right (le_of_not_ge h),normalLeftSolution,normalLeftPrimitive]
    ring

theorem normal_green_boundary_zero (D : NormalChannel) {y : ℝ}
    (u : NormalTransfer D.a (D.potential y)) {s : ℝ} (hs : 0 ≤ s) :
    normalGreenKernel D u.amplitude 0 s = 0 := by
  simp [normalGreenKernel,min_eq_left hs]

theorem normal_green_tendsto_zero (D : NormalChannel) {y : ℝ}
    (u : NormalTransfer D.a (D.potential y)) (s : ℝ) :
    Tendsto (fun r => normalGreenKernel D u.amplitude r s) atTop (𝓝 0) := by
  have h := (normal_amplitude_tendsto_zero u.toNormalProfile).mul_const
    (normalLeftSolution D u.amplitude s)
  rw [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop s] with r hr
  rw [normal_green_piecewise,if_neg (not_le_of_gt hr)]

/-- The outward-flux jump of the Dirichlet kernel is −1, the normalization
of the delta source for −∂(a∂)+p. -/
theorem normal_green_flux_jump (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (u : NormalTransfer D.a (D.potential y)) {s : ℝ} (hs : 0 < s) :
    normalFluxProfile D u s * normalLeftSolution D u.amplitude s -
      normalLeftFlux D u s * u.amplitude s = -1 := by
  have hu := (normal_transfer_positive D hy u hs.le).ne'
  unfold normalLeftFlux normalLeftSolution
  field_simp
  ring

end UV.TemporalRay
