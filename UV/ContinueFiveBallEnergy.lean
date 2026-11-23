import UV.ContinueFiveBallDecay
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Energy estimate for the radial Fourier equation of an n-ball.
After multiplication by x^β, the first derivative term disappears and
the remaining oscillator potential is proportional to x⁻². -/

noncomputable section

open Set
open scoped Topology

namespace UV

theorem normal_ball_oscillator_energy {β : ℝ} (hβ : 1 ≤ β) (f v a : ℝ → ℝ)
    (hf : ∀ x ≥ 1, HasDerivAt f (v x) x) (hv : ∀ x ≥ 1, HasDerivAt v (a x) x)
    (hode : ∀ x ≥ 1, x*(a x+f x)+2*β*v x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ≥ 1, |f x| ≤ C/x^β := by
  let c := β*(β-1)
  let g := fun x : ℝ => x^β*f x
  let u := fun x : ℝ => x^β*v x+β*x^(β-1)*f x
  have hc : 0 ≤ c := mul_nonneg (by linarith) (by linarith)
  have hg (x : ℝ) (hx : 1 ≤ x) : HasDerivAt g (u x) x := by
    have hx' : 0 < x := by linarith
    convert (Real.hasDerivAt_rpow_const (p := β) (Or.inl hx'.ne')).mul (hf x hx) using 1
    dsimp only [u]; ring
  have hu (x : ℝ) (hx : 1 ≤ x) : HasDerivAt u (-g x+c/x^2*g x) x := by
    have hx' : 0 < x := by linarith
    have hp := Real.hasDerivAt_rpow_const (p := β) (Or.inl hx'.ne')
    have hq := Real.hasDerivAt_rpow_const (p := β-1) (Or.inl hx'.ne')
    convert (hp.mul (hv x hx)).add ((hq.const_mul β).mul (hf x hx)) using 1
    dsimp only [g,c]
    rw [Real.rpow_sub_one hx'.ne' (β-1),Real.rpow_sub_one hx'.ne' β]
    field_simp
    linear_combination -x * (hode x hx)
  let E := fun x : ℝ => (g x^2+u x^2)*Real.exp (c/x)
  let E' := fun x : ℝ => (-(c/x^2)*(g x-u x)^2)*Real.exp (c/x)
  have hE (x : ℝ) (hx : 1 ≤ x) : HasDerivAt E (E' x) x := by
    have hx' : 0 < x := by linarith
    have ht := ((hasDerivAt_const x c).div (hasDerivAt_id x) hx'.ne').exp
    convert (((hg x hx).pow 2).add ((hu x hx).pow 2)).mul ht using 1
    dsimp [E',id]
    ring
  have anti : AntitoneOn E (Ici 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
    · exact fun x hx => (hE x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hE x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : 1 ≤ x := interior_subset hx
      rw [(hE x hx').deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg hc (sq_nonneg x)))
        (sq_nonneg _)) (Real.exp_pos _).le
  have hE1 : 0 ≤ E 1 := by dsimp [E]; positivity
  refine ⟨1+Real.sqrt (E 1),by positivity,fun x hx => ?_⟩
  have hx' : 0 < x := by linarith
  have hle : g x^2 ≤ E 1 := by
    apply le_trans _ (anti (show (1:ℝ) ∈ Ici 1 from mem_Ici.mpr le_rfl) hx hx)
    have he : 1 ≤ Real.exp (c/x) := Real.one_le_exp (div_nonneg hc hx'.le)
    exact (le_add_of_nonneg_right (sq_nonneg (u x))).trans (le_mul_of_one_le_right (by positivity) he)
  have hgabs : |g x| ≤ Real.sqrt (E 1) := by
    nlinarith [sq_abs (g x),abs_nonneg (g x),Real.sq_sqrt hE1,Real.sqrt_nonneg (E 1)]
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hx' β),mul_comm]
  rw [show |g x| = x^β*|f x| by rw [show g x=x^β*f x from rfl,abs_mul,abs_of_pos (Real.rpow_pos_of_pos hx' β)]] at hgabs
  linarith

end UV
