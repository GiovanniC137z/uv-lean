import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic

/-! A holomorphic function of finitely many complex variables is determined
on a polydisc by its values on the corresponding open real box. -/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology

namespace UV

def complexifyRealBox {n : ℕ} (x : Fin n → ℝ) : Fin n → ℂ := fun i => (x i : ℂ)

def complexPolydisc (n : ℕ) (R : ℝ) : Set (Fin n → ℂ) := {z | ∀ i, ‖z i‖ < R}

theorem complexPolydisc_eq_ball {n : ℕ} {R : ℝ} (hR : 0 < R) :
    complexPolydisc n R = ball 0 R := by
  ext z
  simp only [complexPolydisc, mem_setOf_eq, mem_ball_zero_iff, pi_norm_lt_iff hR]

/-- The one-variable identity principle with an explicit real interval of
agreement. The interval supplies nonzero equality points accumulating at zero. -/
theorem eqOn_complex_disk_of_real_interval {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hg : DifferentiableOn ℂ g (ball 0 R))
    (hreal : ∀ x : ℝ, |x| < R → f (x : ℂ) = g (x : ℂ)) : EqOn f g (ball 0 R) := by
  apply (hf.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_mem_closure (z₀ := (0 : ℂ))
    (hg.analyticOnNhd isOpen_ball) (convex_ball (0 : ℂ) R).isPreconnected
    (by simpa only [mem_ball, dist_self] using hR)
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let x : ℝ := min R ε / 2
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hxR : x < R := by have hh := min_le_left R ε; dsimp [x]; linarith
  have hxε : x < ε := by have hh := min_le_right R ε; dsimp [x]; linarith
  refine ⟨(x : ℂ), ⟨hreal x (by rwa [abs_of_pos hx0]), ?_⟩, ?_⟩
  · simpa only [mem_singleton_iff, Complex.ofReal_eq_zero] using hx0.ne'
  · simpa only [dist_zero_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] using hxε

theorem complex_coordinate_update_differentiable {n : ℕ} (z : Fin n → ℂ) (i : Fin n) :
    Differentiable ℂ (fun t : ℂ => Function.update z i t) := by
  apply differentiable_pi.mpr
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [Function.update_self] using (differentiable_id : Differentiable ℂ (fun t : ℂ => t))
  · simpa only [Function.update_of_ne hji] using (differentiable_const (z j) :
      Differentiable ℂ (fun _ : ℂ => z j))

theorem complex_coordinate_update_norm_lt {n : ℕ} {R : ℝ} (hR : 0 < R)
    {z : Fin n → ℂ} (hz : ‖z‖ < R) (i : Fin n) {t : ℂ} (ht : ‖t‖ < R) :
    ‖Function.update z i t‖ < R := by
  apply (pi_norm_lt_iff hR).mpr
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [Function.update_self] using ht
  · simpa only [Function.update_of_ne hji] using (pi_norm_lt_iff hR).mp hz j

theorem complex_coordinate_slice_differentiableOn {n : ℕ} {R : ℝ} (hR : 0 < R)
    {F : (Fin n → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (ball 0 R))
    {z : Fin n → ℂ} (hz : ‖z‖ < R) (i : Fin n) :
    DifferentiableOn ℂ (fun t : ℂ => F (Function.update z i t)) (ball 0 R) := by
  intro t ht
  have ht' : ‖t‖ < R := by simpa only [mem_ball_zero_iff] using ht
  have hm : Function.update z i t ∈ ball 0 R := by
    simpa only [mem_ball_zero_iff] using complex_coordinate_update_norm_lt hR hz i ht'
  exact ((hF.differentiableAt (isOpen_ball.mem_nhds hm)).comp t
    (complex_coordinate_update_differentiable z i t)).differentiableWithinAt

/-- The identity principle from the real slice of a finite-dimensional complex
sup-norm ball. No equality on a complex open subset is assumed. -/
theorem eqOn_complex_ball_of_real_ball {n : ℕ} {R : ℝ} (hR : 0 < R)
    {F G : (Fin n → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 R)) (hG : DifferentiableOn ℂ G (ball 0 R))
    (hreal : ∀ x : Fin n → ℝ, ‖x‖ < R → F (complexifyRealBox x) = G (complexifyRealBox x)) :
    EqOn F G (ball 0 R) := by
  have hpartial : ∀ S : Finset (Fin n), ∀ z : Fin n → ℂ, ‖z‖ < R →
      (∀ i, i ∉ S → (z i).im = 0) → F z = G z := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        intro z hz hzero
        let x : Fin n → ℝ := fun i => (z i).re
        have hx : ‖x‖ < R := by
          apply (pi_norm_lt_iff hR).mpr
          intro i
          rw [Real.norm_eq_abs]
          exact (Complex.abs_re_le_norm (z i)).trans_lt ((pi_norm_lt_iff hR).mp hz i)
        have he : complexifyRealBox x = z := by
          funext i
          apply Complex.ext
          · rfl
          · simpa only [complexifyRealBox, Complex.ofReal_im] using (hzero i (by simp)).symm
        simpa only [he] using hreal x hx
    | @insert i S hiS ih =>
        intro z hz hzero
        have hslice : ∀ x : ℝ, |x| < R →
            F (Function.update z i (x : ℂ)) = G (Function.update z i (x : ℂ)) := by
          intro x hx
          apply ih (Function.update z i (x : ℂ))
            (complex_coordinate_update_norm_lt hR hz i (by
              simpa only [Complex.norm_real, Real.norm_eq_abs] using hx))
          intro j hj
          by_cases hji : j = i
          · subst j
            simp
          · rw [Function.update_of_ne hji]
            exact hzero j (by simp only [Finset.mem_insert, not_or]; exact ⟨hji, hj⟩)
        have heq := eqOn_complex_disk_of_real_interval hR
          (complex_coordinate_slice_differentiableOn hR hF hz i)
          (complex_coordinate_slice_differentiableOn hR hG hz i) hslice
          (by simpa only [mem_ball_zero_iff] using (pi_norm_lt_iff hR).mp hz i)
        simpa only [Function.update_eq_self] using heq
  intro z hz
  exact hpartial Finset.univ z (by simpa only [mem_ball_zero_iff] using hz)
    (fun i hi => False.elim (hi (Finset.mem_univ i)))

theorem eqOn_complex_polydisc_of_real_box {n : ℕ} {R : ℝ} (hR : 0 < R)
    {F G : (Fin n → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (complexPolydisc n R))
    (hG : DifferentiableOn ℂ G (complexPolydisc n R))
    (hreal : ∀ x : Fin n → ℝ, (∀ i, |x i| < R) →
      F (complexifyRealBox x) = G (complexifyRealBox x)) : EqOn F G (complexPolydisc n R) := by
  rw [complexPolydisc_eq_ball hR] at hF hG ⊢
  apply eqOn_complex_ball_of_real_ball hR hF hG
  intro x hx
  apply hreal x
  intro i
  simpa only [Real.norm_eq_abs] using (pi_norm_lt_iff hR).mp hx i

end UV
