import UV.PrincipalSqrt
import Mathlib.Analysis.Complex.RemovableSingularity

/-! An even analytic function of one complex variable descends through the
square map to a function analytic on the squared-radius disk. -/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology

namespace UV

theorem principalSqrt_sq (z : ℂ) : principalSqrt z ^ 2 = z := by
  exact Complex.cpow_nat_inv_pow z (by decide : (2 : ℕ) ≠ 0)

theorem principalSqrt_norm (z : ℂ) : ‖principalSqrt z‖ = Real.sqrt ‖z‖ := by
  simpa only [principalSqrt, Real.sqrt_eq_rpow, one_div] using Complex.norm_cpow_inv_nat z 2

@[simp] theorem principalSqrt_zero : principalSqrt 0 = 0 := by
  simp [principalSqrt]

theorem principalSqrt_continuousAt_zero : ContinuousAt principalSqrt 0 := by
  exact Complex.continuousAt_cpow_const_of_re_pos (Or.inl (by simp)) (by norm_num)

theorem principalSqrt_analyticOnNhd_slitPlane : AnalyticOnNhd ℂ principalSqrt Complex.slitPlane := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    exact (principalSqrt_hasDerivAt hz).differentiableAt.differentiableWithinAt
  · exact Complex.isOpen_slitPlane

def evenSquareDescent (f : ℂ → ℂ) (w : ℂ) : ℂ := f (principalSqrt w)

theorem evenSquareDescent_eq_of_sq {f : ℂ → ℂ} (heven : ∀ z, f (-z) = f z)
    {w t : ℂ} (ht : t ^ 2 = w) : evenSquareDescent f w = f t := by
  rcases eq_or_eq_neg_of_sq_eq_sq (principalSqrt w) t ((principalSqrt_sq w).trans ht.symm) with h | h
  · rw [evenSquareDescent, h]
  · rw [evenSquareDescent, h, heven]

theorem evenSquareDescent_sq {f : ℂ → ℂ} (heven : ∀ z, f (-z) = f z) (t : ℂ) :
    evenSquareDescent f (t ^ 2) = f t := evenSquareDescent_eq_of_sq heven rfl

theorem rotatedPrincipalSqrt_sq (w : ℂ) : (Complex.I * principalSqrt (-w)) ^ 2 = w := by
  rw [mul_pow, Complex.I_sq, principalSqrt_sq]
  ring

theorem rotatedPrincipalSqrt_norm (w : ℂ) :
    ‖Complex.I * principalSqrt (-w)‖ = Real.sqrt ‖w‖ := by
  rw [norm_mul, Complex.norm_I, one_mul, principalSqrt_norm, norm_neg]

theorem evenSquareDescent_rotated {f : ℂ → ℂ} (heven : ∀ z, f (-z) = f z) (w : ℂ) :
    evenSquareDescent f w = f (Complex.I * principalSqrt (-w)) :=
  evenSquareDescent_eq_of_sq heven (rotatedPrincipalSqrt_sq w)

theorem principalSqrt_mem_ball {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ∈ ball 0 (R ^ 2)) :
    principalSqrt w ∈ ball 0 R := by
  have hw' : ‖w‖ < R ^ 2 := by simpa only [mem_ball, dist_zero_right] using hw
  have hs : ‖principalSqrt w‖ < R := by
    rw [principalSqrt_norm]
    exact (Real.sqrt_lt (norm_nonneg w) hR.le).mpr hw'
  simpa only [mem_ball, dist_zero_right] using hs

theorem rotatedPrincipalSqrt_mem_ball {R : ℝ} (hR : 0 < R) {w : ℂ}
    (hw : w ∈ ball 0 (R ^ 2)) : Complex.I * principalSqrt (-w) ∈ ball 0 R := by
  have hw' : ‖w‖ < R ^ 2 := by simpa only [mem_ball, dist_zero_right] using hw
  have hs : ‖Complex.I * principalSqrt (-w)‖ < R := by
    rw [rotatedPrincipalSqrt_norm]
    exact (Real.sqrt_lt (norm_nonneg w) hR.le).mpr hw'
  simpa only [mem_ball, dist_zero_right] using hs

theorem evenSquareDescent_analyticAt_of_ne_zero {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (heven : ∀ z, f (-z) = f z)
    {w : ℂ} (hw : w ∈ ball 0 (R ^ 2)) (hw0 : w ≠ 0) :
    AnalyticAt ℂ (evenSquareDescent f) w := by
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hw0 with hs | hs
  · exact (hf _ (principalSqrt_mem_ball hR hw)).comp (principalSqrt_analyticOnNhd_slitPlane _ hs)
  · have hneg : AnalyticAt ℂ (fun z : ℂ => -z) w := analyticAt_id.neg
    have hg : AnalyticAt ℂ (fun z : ℂ => Complex.I * principalSqrt (-z)) w :=
      analyticAt_const.fun_mul ((principalSqrt_analyticOnNhd_slitPlane _ hs).comp' hneg)
    have heq : evenSquareDescent f = (fun z : ℂ => f (Complex.I * principalSqrt (-z))) :=
      funext (evenSquareDescent_rotated heven)
    rw [heq]
    exact (hf _ (rotatedPrincipalSqrt_mem_ball hR hw)).comp'
      (f := fun z : ℂ => Complex.I * principalSqrt (-z)) hg

theorem evenSquareDescent_continuousAt_zero {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) : ContinuousAt (evenSquareDescent f) 0 := by
  have hf0 : ContinuousAt f 0 := (hf 0 (by simpa only [mem_ball, dist_self] using hR)).continuousAt
  have hfr : ContinuousAt f (principalSqrt 0) := by simpa only [principalSqrt_zero] using hf0
  exact hfr.comp principalSqrt_continuousAt_zero

theorem evenSquareDescent_analyticAt_zero {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (heven : ∀ z, f (-z) = f z) :
    AnalyticAt ℂ (evenSquareDescent f) 0 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · apply eventually_nhdsWithin_iff.mpr
    filter_upwards [ball_mem_nhds (0 : ℂ) (sq_pos_of_pos hR)] with w hw hw0
    exact (evenSquareDescent_analyticAt_of_ne_zero hR hf heven hw hw0).differentiableAt
  · exact evenSquareDescent_continuousAt_zero hR hf

theorem evenSquareDescent_analyticOnNhd {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (heven : ∀ z, f (-z) = f z) :
    AnalyticOnNhd ℂ (evenSquareDescent f) (ball 0 (R ^ 2)) := by
  intro w hw
  by_cases hw0 : w = 0
  · subst w
    exact evenSquareDescent_analyticAt_zero hR hf heven
  · exact evenSquareDescent_analyticAt_of_ne_zero hR hf heven hw hw0

theorem evenSquareDescent_norm_bound {f : ℂ → ℂ} {r C : ℝ} (hr : 0 ≤ r)
    (hf : ∀ t : ℂ, ‖t‖ ≤ r → ‖f t‖ ≤ C) {w : ℂ} (hw : ‖w‖ ≤ r ^ 2) :
    ‖evenSquareDescent f w‖ ≤ C := by
  apply hf
  rw [principalSqrt_norm]
  exact (Real.sqrt_le_iff).mpr ⟨hr, hw⟩

/-- The explicit square descent, including its full squared-radius analytic disk
and transfer of every closed-disk uniform bound. -/
theorem even_analytic_square_descent {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (heven : ∀ z, f (-z) = f z) :
    ∃ b : ℂ → ℂ, AnalyticOnNhd ℂ b (ball 0 (R ^ 2)) ∧
      (∀ t : ℂ, ‖t‖ < R → b (t ^ 2) = f t) ∧
      (∀ r C : ℝ, 0 ≤ r → (∀ t : ℂ, ‖t‖ ≤ r → ‖f t‖ ≤ C) →
        ∀ w : ℂ, ‖w‖ ≤ r ^ 2 → ‖b w‖ ≤ C) := by
  exact ⟨evenSquareDescent f, evenSquareDescent_analyticOnNhd hR hf heven,
    (fun t _ => evenSquareDescent_sq heven t),
    (fun _ _ hr hb _ hw => evenSquareDescent_norm_bound hr hb hw)⟩

end UV
