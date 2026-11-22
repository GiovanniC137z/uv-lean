import UV.ContinueCarrierConeTensor
import UV.ContinueConeAngularSquare

/-! Uniform bounds for the actual quadratic angular channels. The scalar
resolvent evaluations are used at their original signed pole side. The result
is for the temporal and equal-coordinate spatial channels of radial tests;
no distributional theorem for an arbitrary angular test is asserted. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Set Filter
open scoped Topology Interval

theorem coneAngularFirst_eq_closed {η t : ℝ} (ht : 0 < t) (hη : η ^ 2 = 1) :
    coneAngularFirst η t = coneFirstClosed η t := by
  exact cone_angular_resolvent_cos ht hη

theorem coneAngularSecond_eq_closed {η t : ℝ} (ht : 0 < t) (hη : η ^ 2 = 1) :
    coneAngularSecond η t = coneSecondClosed η t := by
  simpa only [coneAngularSecond, coneAngularWeight, coneAngularPole, coneSecondClosed,
    Complex.ofReal_pow] using cone_angular_square_cos ht hη

theorem coneTemporalSecond_eq_closed {η t : ℝ} (ht : 0 < t) (hη : η ^ 2 = 1) :
    coneTemporalSecond η t = coneTemporalClosed η t := by
  rw [coneTemporalSecond_identity ht hη, coneAngularFirst_eq_closed ht hη,
    coneAngularSecond_eq_closed ht hη]
  rfl

theorem coneSpatialSecond_eq_closed {η t : ℝ} (ht : 0 < t) (hη : η ^ 2 = 1) :
    coneSpatialSecond η t = coneSpatialClosed η t := by
  rw [coneSpatialSecond_identity ht hη, coneAngularFirst_eq_closed ht hη,
    coneAngularSecond_eq_closed ht hη]
  rfl

/-- Uniform actual temporal angular bound at every positive pole height. -/
theorem coneTemporalSecond_norm_le {η t : ℝ} (ht : 0 < t) (hη : η ^ 2 = 1) :
    ‖coneTemporalSecond η t‖ ≤ 2 := by
  rw [coneTemporalSecond_eq_closed ht hη]
  exact coneTemporalClosed_norm_le ht.le hη

/-- Uniform actual spatial diagonal angular bound. -/
theorem coneSpatialSecond_norm_le {η t : ℝ} (ht : 0 < t) (hη : η ^ 2 = 1) :
    ‖coneSpatialSecond η t‖ ≤ 2 / 3 := by
  rw [coneSpatialSecond_eq_closed ht hη]
  exact coneSpatialClosed_norm_le ht.le hη

/-- The angular double pole with the temporal quadratic numerator has radial
majorant 2r, uniformly in the original positive pole height. -/
theorem coneTemporalSecond_radial_bound {η h r : ℝ} (hη : η ^ 2 = 1)
    (hh : 0 < h) (hr : 0 < r) :
    ‖(r : ℂ) * coneTemporalSecond η (h / r ^ 2)‖ ≤ 2 * r := by
  rw [coneTemporalSecond_eq_closed (div_pos hh (sq_pos_of_pos hr)) hη]
  exact coneTemporalClosed_radial_bound hη hh.le hr

theorem coneSpatialSecond_radial_bound {η h r : ℝ} (hη : η ^ 2 = 1)
    (hh : 0 < h) (hr : 0 < r) :
    ‖(r : ℂ) * coneSpatialSecond η (h / r ^ 2)‖ ≤ (2 / 3) * r := by
  rw [coneSpatialSecond_eq_closed (div_pos hh (sq_pos_of_pos hr)) hη]
  exact coneSpatialClosed_radial_bound hη hh.le hr

/-- Finite temporal channel through the tip for every bounded measurable
radial multiplier, retaining the pole height before integration. -/
theorem coneTemporalSecond_radial_test_integrable {η h R : ℝ} (hη : η ^ 2 = 1)
    (hh : 0 < h) {χ : ℝ → ℂ} (hχ : Measurable χ) (hB : ∃ C, ∀ r, ‖χ r‖ ≤ C) :
    IntegrableOn (fun r => χ r * ((r : ℂ) * coneTemporalSecond η (h / r ^ 2))) (Ioc 0 R) := by
  apply (coneTemporalClosed_radial_test_integrable hη hh.le hχ hB).congr_fun
    (s := Ioc 0 R) ?_ measurableSet_Ioc
  intro r hr
  dsimp only
  rw [coneTemporalSecond_eq_closed (div_pos hh (sq_pos_of_pos hr.1)) hη]

/-- Finite spatial diagonal channel under the same radial tests. -/
theorem coneSpatialSecond_radial_test_integrable {η h R : ℝ} (hη : η ^ 2 = 1)
    (hh : 0 < h) {χ : ℝ → ℂ} (hχ : Measurable χ) (hB : ∃ C, ∀ r, ‖χ r‖ ≤ C) :
    IntegrableOn (fun r => χ r * ((r : ℂ) * coneSpatialSecond η (h / r ^ 2))) (Ioc 0 R) := by
  apply (coneSpatialClosed_radial_test_integrable hη hh.le hχ hB).congr_fun
    (s := Ioc 0 R) ?_ measurableSet_Ioc
  intro r hr
  dsimp only
  rw [coneSpatialSecond_eq_closed (div_pos hh (sq_pos_of_pos hr.1)) hη]

/-- Both coefficients keep the selected sector, evolution sign, and normalized
geometric carrier. The Euclidean polar radius is not a new pole direction. -/
theorem Plane.quadratic_cone_channels {E : Type*} [NormedAddCommGroup E]
    (diamond : Plane E) (ε : Evolution) {h r : ℝ} (hh : 0 < h) (hr : 0 < r) :
    ‖diamond.Ghat.val‖ = 1 ∧
    ‖(r : ℂ) * coneTemporalSecond (diamond.eta ε) (h / r ^ 2)‖ ≤ 2 * r ∧
    ‖(r : ℂ) * coneSpatialSecond (diamond.eta ε) (h / r ^ 2)‖ ≤ (2 / 3) * r :=
  ⟨diamond.Ghat.property, coneTemporalSecond_radial_bound (diamond.eta_sq ε) hh hr,
    coneSpatialSecond_radial_bound (diamond.eta_sq ε) hh hr⟩

end UV.SectorPlane
