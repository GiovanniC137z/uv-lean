import UV.DepthAsymptotics
import UV.FinitePole

/-! Exact right-derivative and closed rate thresholds in the revised source. -/

noncomputable section

open Metric Set
open scoped Matrix.Norms.L2Operator

namespace UV

/-- The kernel's actual right derivative at zero auxiliary mass. -/
theorem kernel_right_deriv_auxMass_zero {a u : ℝ} (hu : 0 < u) :
    HasDerivWithinAt (fun M => kernel a M u) (a * kernel a 0 u) (Ici 0) 0 := by
  simpa using (kernel_hasDerivAt_auxMass a 0 hu).hasDerivWithinAt (s := Ici 0)

/-- The interior distance estimate is strict, so the approximate rate may
equal twice the radius and still certify strict positivity. -/
theorem finite_pole_positive_of_closed_margin {zX zY baseline : ℂ} {r : ℝ}
    (hclose : ‖zX - zY‖ < r) (hpos : 2 * r ≤ poleShiftRate (zY - baseline)) :
    0 < poleShiftRate (zX - baseline) := by
  have hlow := (abs_lt.mp (finite_pole_rate_enclosure (baseline := baseline) hclose)).1
  linarith

theorem revised_oqed_finite_pole_enclosure {n : Type*} [Fintype n] [DecidableEq n]
    {KX KY : ℂ → Matrix n n ℂ} {c : ℂ} {r : ℝ} {E : ℂ → ℝ} (hr : 0 < r)
    (hX : ∀ i j, AnalyticOnNhd ℂ (fun z => KX z i j) (closedBall c r))
    (hY : ∀ i j, AnalyticOnNhd ℂ (fun z => KY z i j) (closedBall c r))
    (hKY : ∀ z ∈ sphere c r, (KY z).det ≠ 0)
    (hzero : (KY c).det = 0) (hsimple : deriv (fun z => (KY z).det) c ≠ 0)
    (honly : ∀ z ∈ ball c r, (KY z).det = 0 → z = c)
    (hE : ∀ z ∈ sphere c r, ‖KX z - KY z‖ ≤ E z)
    (hmargin : ∀ z ∈ sphere c r, ‖Ring.inverse (KY z)‖ * E z < 1) :
    ∃ p ∈ ball c r, (KX p).det = 0 ∧ deriv (fun z => (KX z).det) p ≠ 0 ∧
      (∀ z ∈ ball c r, (KX z).det = 0 → z = p) ∧
      ∀ baseline : ℂ,
        |poleShiftRate (p - baseline) - poleShiftRate (c - baseline)| < 2 * r ∧
        (2 * r ≤ poleShiftRate (c - baseline) → 0 < poleShiftRate (p - baseline)) := by
  obtain ⟨p, hp, hzero, hsimple, honly, hrate⟩ :=
    oqed_finite_pole_enclosure hr hX hY hKY hzero hsimple honly hE hmargin
  refine ⟨p, hp, hzero, hsimple, honly, fun baseline => ⟨(hrate baseline).1, ?_⟩⟩
  exact finite_pole_positive_of_closed_margin
    (by simpa only [mem_ball, dist_eq_norm] using hp)

end UV
