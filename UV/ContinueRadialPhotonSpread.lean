import UV.ContinueRadialPhotonConcentration
import Mathlib.Algebra.Polynomial.Roots

/-! The genuine radial oscillator stiffness has null level sets. This
is the obstruction obtained after the separated one-frequency ground
equation in the fluctuating-depth photon calculation. -/

noncomputable section

namespace UV.RadialPhoton

open MeasureTheory Real Set Polynomial

def radialStiffness (e k r : ℝ) : ℝ := k^2*(1+e^2*(depthDifference r k)^2)

private theorem depth_difference_as_polynomial (r k : ℝ) :
    depthDifference r k = exp (-r*k/2) - exp (-r*k/2)^2 := by
  unfold depthDifference
  rw [sq,← exp_add]
  congr 2
  ring

theorem radial_stiffness_level_finite {e k : ℝ} (he : e ≠ 0) (hk : 0 < k) (c : ℝ) :
    {r | radialStiffness e k r = c}.Finite := by
  let P : Polynomial ℝ := C (k^2)*(1+C (e^2)*(X-X^2)^2)-C c
  have hEval (w : ℝ) : eval w P = k^2*(1+e^2*(w-w^2)^2)-c := by simp [P]
  have hP : P ≠ 0 := by
    intro hzero
    have h₀ := hEval 0
    have h₁ := hEval (1/2)
    rw [hzero] at h₀ h₁
    norm_num at h₀ h₁
    nlinarith only [h₀,h₁,mul_pos (sq_pos_of_pos hk) (sq_pos_of_ne_zero he)]
  let w := fun r : ℝ => exp (-r*k/2)
  have hwinj : Function.Injective w := by
    intro r s hrs
    have h := Real.exp_injective hrs
    change -r*k/2 = -s*k/2 at h
    exact sub_eq_zero.mp ((mul_eq_zero.mp (show (r-s)*k = 0 by linarith only [h])).resolve_right hk.ne')
  have hset := (Polynomial.finite_setOf_isRoot hP).preimage (f := w) hwinj.injOn
  apply hset.subset
  intro r hr
  change eval (w r) P = 0
  rw [hEval]
  rw [← show depthDifference r k = w r-w r^2 from depth_difference_as_polynomial r k]
  exact sub_eq_zero.mpr hr

theorem radial_stiffness_level_null {e k : ℝ} (he : e ≠ 0) (hk : 0 < k)
    (ρ : Measure ℝ) (hac : ρ ≪ volume) (c : ℝ) : ρ {r | radialStiffness e k r = c} = 0 :=
  hac ((radial_stiffness_level_finite he hk c).measure_zero volume)

/-- The residual radial state from a one-frequency separated oscillator
equation would be zero in the actual absolutely continuous position law. -/
theorem radial_stiffness_no_normalized_state {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {e k : ℝ} (he : e ≠ 0) (hk : 0 < k) (ρ : Measure ℝ) (hac : ρ ≪ volume)
    (ψ : ℝ → H) (freq : ℝ) (hn : (∫ r, ‖ψ r‖^2 ∂ρ) = 1) :
    ¬ ∀ᵐ r ∂ρ, (radialStiffness e k r-freq^2) • ψ r = 0 := by
  intro h
  have hne : ∀ᵐ r ∂ρ, radialStiffness e k r ≠ freq^2 :=
    ae_iff.mpr (by simpa using radial_stiffness_level_null he hk ρ hac (freq^2))
  have hzero : (fun r => ‖ψ r‖^2) =ᵐ[ρ] fun _ => (0:ℝ) := by
    filter_upwards [h,hne] with r hr hr'
    rw [(smul_eq_zero.mp hr).resolve_left (sub_ne_zero.mpr hr')]
    norm_num
  rw [integral_congr_ae hzero,integral_zero] at hn
  exact zero_ne_one hn

end UV.RadialPhoton
