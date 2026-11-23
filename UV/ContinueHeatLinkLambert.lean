import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic

/-! All positive-imaginary inverse branches of w ↦ w exp w on the
positive real ray. Writing t = Re w / Im w fixes the phase and turns
the modulus into a strictly monotone real equation. -/

noncomputable section

namespace UV.HeatMaxwell

open Filter Set Real
open scoped Topology ComplexConjugate

def heatBranchHeight (n : ℕ) (t : ℝ) : ℝ :=
  Real.arctan t + (2*(n:ℝ)+3/2)*Real.pi

def heatBranchLog (n : ℕ) (t : ℝ) : ℝ :=
  Real.log (heatBranchHeight n t) + Real.log (1+t^2)/2 + t*heatBranchHeight n t

def heatBranchPoint (n : ℕ) (t : ℝ) : ℂ :=
  ⟨t*heatBranchHeight n t, heatBranchHeight n t⟩

theorem heatBranchHeight_mem (n : ℕ) (t : ℝ) :
    heatBranchHeight n t ∈ Ioo ((2*(n:ℝ)+1)*π) ((2*(n:ℝ)+2)*π) := by
  unfold heatBranchHeight
  constructor <;> linarith only [arctan_lt_pi_div_two t,neg_pi_div_two_lt_arctan t]

private theorem heat_height_large (n : ℕ) (t : ℝ) : 2 ≤ heatBranchHeight n t := by
  have h := (heatBranchHeight_mem n t).1
  nlinarith only [h,one_le_pi_div_two,mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) pi_pos.le]

private theorem heat_branch_log_derivative (n : ℕ) (t : ℝ) :
    HasDerivAt (heatBranchLog n) (heatBranchHeight n t +
      (2*t+(heatBranchHeight n t)⁻¹)/(1+t^2)) t := by
  have hb : 0 < heatBranchHeight n t := by linarith [heat_height_large n t]
  have hd : HasDerivAt (heatBranchHeight n) (1/(1+t^2)) t :=
    (hasDerivAt_arctan t).add_const _
  have hp : 0 < 1+t^2 := by positivity
  have hs := (((hasDerivAt_id t).pow 2).const_add 1).log hp.ne'
  have h := (((hd.log hb.ne').add (hs.div_const 2)).add ((hasDerivAt_id t).mul hd))
  convert h using 1
  simp only [Pi.pow_apply,id_eq]
  norm_num
  field_simp
  ring

theorem heatBranchLog_strictMono (n : ℕ) : StrictMono (heatBranchLog n) := by
  apply strictMono_of_deriv_pos
  intro t
  rw [(heat_branch_log_derivative n t).deriv]
  have hb := heat_height_large n t
  have hp : 0 < 1+t^2 := by positivity
  have hi : 0 < (heatBranchHeight n t)⁻¹ := inv_pos.mpr (by linarith only [hb])
  have h : -(1:ℝ) < (2*t+(heatBranchHeight n t)⁻¹)/(1+t^2) := by
    apply (lt_div_iff₀ hp).mpr
    nlinarith only [sq_nonneg (t+1),hi]
  linarith only [h,hb]

/-- Every real log modulus is attained exactly once on each strip. -/
theorem heatBranchLog_bijective (n : ℕ) : Function.Bijective (heatBranchLog n) := by
  refine ⟨(heatBranchLog_strictMono n).injective,?_⟩
  intro z
  let B := (2*(n:ℝ)+2)*π
  let R := |z|+|Real.log B|+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hB := (heatBranchHeight_mem n (-R)).2
  have hb := heat_height_large n (-R)
  have hb' := heat_height_large n R
  have hl : Real.log (heatBranchHeight n (-R)) ≤ Real.log B :=
    Real.log_le_log (by linarith only [hb]) hB.le
  have hr : √(1+(-R)^2) ≤ 1+R := by
    have hs := Real.sq_sqrt (show 0 ≤ 1+(-R)^2 by positivity)
    nlinarith only [hs, Real.sqrt_nonneg (1+(-R)^2),hR]
  have hlog : Real.log (1+(-R)^2)/2 ≤ R := by
    rw [← Real.log_sqrt (by positivity : 0 ≤ 1+(-R)^2)]
    exact (Real.log_le_iff_le_exp (Real.sqrt_pos.mpr (by positivity))).mpr
      (hr.trans (by linarith only [Real.add_one_le_exp R]))
  have hlo : heatBranchLog n (-R) ≤ z := by
    unfold heatBranchLog
    have h := mul_le_mul_of_nonpos_left hb (neg_nonpos.mpr hR.le)
    dsimp [R] at *
    linarith only [hl,hlog,h,neg_abs_le z,le_abs_self (Real.log B)]
  have hhi : z ≤ heatBranchLog n R := by
    have h₁ := Real.log_nonneg (show 1 ≤ heatBranchHeight n R by linarith only [hb'])
    have h₂ := Real.log_nonneg (show 1 ≤ 1+R^2 by linarith only [sq_nonneg R])
    have h₃ := mul_le_mul_of_nonneg_left hb' hR.le
    unfold heatBranchLog
    dsimp [R] at *
    linarith only [h₁,h₂,h₃,le_abs_self z,abs_nonneg z,abs_nonneg (Real.log B)]
  have hc : Continuous (heatBranchLog n) :=
    continuous_iff_continuousAt.mpr fun t => (heat_branch_log_derivative n t).continuousAt
  obtain ⟨t,_,ht⟩ := intermediate_value_Icc (show -R ≤ R by linarith only [hR]) hc.continuousOn
    (show z ∈ Icc (heatBranchLog n (-R)) (heatBranchLog n R) from ⟨hlo,hhi⟩)
  exact ⟨t,ht⟩

private theorem heat_height_sincos (n : ℕ) (t : ℝ) :
    Real.sin (heatBranchHeight n t) = -1/√(1+t^2) ∧
      Real.cos (heatBranchHeight n t) = t/√(1+t^2) := by
  have he : heatBranchHeight n t = (Real.arctan t + π/2 + π) + (n:ℝ)*(2*π) := by
    unfold heatBranchHeight
    ring
  rw [he,Real.sin_add_nat_mul_two_pi,Real.cos_add_nat_mul_two_pi,Real.sin_add_pi,
    Real.cos_add_pi,Real.sin_add_pi_div_two,Real.cos_add_pi_div_two,Real.cos_arctan,Real.sin_arctan]
  constructor <;> ring

theorem heatBranchPoint_mul_exp (n : ℕ) (t : ℝ) :
    heatBranchPoint n t * Complex.exp (heatBranchPoint n t) = (Real.exp (heatBranchLog n t) : ℂ) := by
  let b := heatBranchHeight n t
  have hb : 0 < b := by linarith only [heat_height_large n t]
  have hs : 0 < √(1+t^2) := Real.sqrt_pos.mpr (by positivity)
  have he : Real.exp (heatBranchLog n t) = b*√(1+t^2)*Real.exp (t*b) := by
    unfold heatBranchLog
    rw [Real.exp_add,Real.exp_add,← Real.log_sqrt (by positivity : 0 ≤ 1+t^2),
      Real.exp_log hs,Real.exp_log hb]
  obtain ⟨hsin,hcos⟩ := heat_height_sincos n t
  change Real.sin b = _ at hsin
  change Real.cos b = _ at hcos
  rw [he]
  apply Complex.ext
  · rw [Complex.mul_re, Complex.exp_re, Complex.exp_im, Complex.ofReal_re]
    change t*b*(Real.exp (t*b)*Real.cos b) - b*(Real.exp (t*b)*Real.sin b) = b*√(1+t^2)*Real.exp (t*b)
    rw [hsin,hcos]
    field_simp
    nlinarith only [Real.sq_sqrt (by positivity : 0 ≤ 1+t^2)]
  · rw [Complex.mul_im, Complex.exp_im, Complex.exp_re, Complex.ofReal_im]
    change t*b*(Real.exp (t*b)*Real.sin b) + b*(Real.exp (t*b)*Real.cos b) = 0
    rw [hsin,hcos]
    ring

/-- An upper-half-plane inverse value on the positive argument ray. -/
def heatLambertUpper (n : ℕ) (A : ℝ) : ℂ :=
  heatBranchPoint n (Function.surjInv (heatBranchLog_bijective n).surjective (Real.log A))

theorem heatLambertUpper_spec (n : ℕ) {A : ℝ} (hA : 0 < A) :
    heatLambertUpper n A * Complex.exp (heatLambertUpper n A) = (A:ℂ) ∧
      (heatLambertUpper n A).im ∈ Ioo ((2*(n:ℝ)+1)*π) ((2*(n:ℝ)+2)*π) := by
  refine ⟨?_,heatBranchHeight_mem n _⟩
  rw [heatLambertUpper,heatBranchPoint_mul_exp,Function.rightInverse_surjInv (heatBranchLog_bijective n).surjective (Real.log A),Real.exp_log hA]

end UV.HeatMaxwell
