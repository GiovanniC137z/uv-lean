import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

/-! The zero-free case of finite exponential type on the whole energy
plane. Cauchy's estimate applied to a normalized exponential of a logarithm
bounds its derivative uniformly. -/

noncomputable section

open Complex Set Metric
open scoped Topology

namespace UV

private theorem entire_derivative {f : ℂ → ℂ} (hf : Differentiable ℂ f) : Differentiable ℂ (deriv f) :=
  differentiableOn_univ.mp (hf.differentiableOn.deriv isOpen_univ)

private theorem entire_primitive {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    ∃ h : ℂ → ℂ, ∀ z, HasDerivAt h (f z) z := by
  use fun z => wedgeIntegral 0 z f
  intro z
  have hz : z ∈ ball (0:ℂ) (‖z‖+1) := by simp [mem_ball]
  exact (hf.differentiableOn (s := ball 0 (‖z‖+1))).isConservativeOn.hasDerivAt_wedgeIntegral
    hf.continuous.continuousOn hz

theorem entire_log_of_nonvanishing {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hn : ∀ z, f z ≠ 0) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ ∀ z, Complex.exp (h z) = f z := by
  obtain ⟨W,hW⟩ := entire_primitive ((entire_derivative hf).div hf hn)
  let v := fun z => f z * Complex.exp (-W z)
  have hv (z : ℂ) : HasDerivAt v 0 z := by
    convert (hf z).hasDerivAt.mul ((hW z).neg.cexp) using 1
    simp only [Pi.div_apply, Pi.neg_apply]
    field_simp [hn z]
    ring
  have he (z : ℂ) : v z = v 0 := is_const_of_deriv_eq_zero
    (fun w => (hv w).differentiableAt) (fun w => (hv w).deriv) z 0
  have hn0 : v 0 ≠ 0 := mul_ne_zero (hn 0) (Complex.exp_ne_zero _)
  refine ⟨fun z => W z + Complex.log (v 0), (fun z => ((hW z).add_const _).differentiableAt), ?_⟩
  intro z
  rw [Complex.exp_add,Complex.exp_log hn0,← he z]
  simp [v,Complex.exp_neg,← mul_assoc,mul_comm]

/-- An entire logarithm with linearly bounded real part is affine. The
radius is chosen separately at each center, giving a global derivative bound. -/
theorem entire_affine_of_real_part_growth {h : ℂ → ℂ} (hh : Differentiable ℂ h) {A B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ z, (h z).re ≤ A + B*‖z‖) :
    ∃ a b : ℂ, ∀ z, h z = a*z+b := by
  have bound (z : ℂ) : ‖deriv h z‖ ≤ Real.exp (1+2*B) := by
    let R := 1 + |A| + ‖z‖ + |(h z).re|
    have hR : 0 < R := by dsimp [R]; positivity
    have hzR : ‖z‖ ≤ R := by dsimp [R]; linarith [abs_nonneg A,abs_nonneg (h z).re]
    have haR : A - (h z).re ≤ R := by
      dsimp [R]
      linarith [le_abs_self A,neg_le_abs (h z).re,norm_nonneg z]
    let v := fun w => Complex.exp ((h w - h z)/(R:ℂ))
    have hv (w : ℂ) : HasDerivAt v (Complex.exp ((h w - h z)/(R:ℂ)) * (deriv h w / (R:ℂ))) w :=
      (((hh w).hasDerivAt.sub_const _).div_const _).cexp
    have hev := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := v) (c := z) hR
      (show Differentiable ℂ v from fun w => (hv w).differentiableAt).diffContOnCl (C := Real.exp (1+2*B))
    have hvc := hev (fun w hw => by
      have hd : ‖w-z‖ = R := by simpa only [mem_sphere,dist_eq_norm] using hw
      have hww : ‖w‖ ≤ 2*R := calc
        ‖w‖ ≤ ‖w-z‖+‖z‖ := norm_le_norm_sub_add _ _
        _ ≤ _ := by linarith
      rw [show ‖v w‖ = Real.exp (((h w).re-(h z).re)/R) by simp [v,Complex.norm_exp,Complex.div_ofReal_re]]
      apply Real.exp_le_exp.mpr
      apply (div_le_iff₀ hR).mpr
      nlinarith [hb w,mul_le_mul_of_nonneg_left hww hB])
    rw [(hv z).deriv] at hvc
    simpa only [sub_self,zero_div,Complex.exp_zero,one_mul,norm_div,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hR,div_le_div_iff_of_pos_right hR] using hvc
  have hbound : Bornology.IsBounded (range (deriv h)) :=
    isBounded_iff_forall_norm_le.mpr ⟨_,fun _ ⟨z,hz⟩ => hz ▸ bound z⟩
  obtain ⟨a,ha⟩ := (entire_derivative hh).exists_const_forall_eq_of_bounded hbound
  have hv (z : ℂ) : HasDerivAt (fun w => h w-a*w) 0 z := by
    simpa only [ha, mul_one, sub_self] using (hh z).hasDerivAt.sub ((hasDerivAt_id z).const_mul a)
  refine ⟨a,h 0,fun z => ?_⟩
  have he := is_const_of_deriv_eq_zero (fun w => (hv w).differentiableAt) (fun w => (hv w).deriv) z 0
  change h z - a*z = h 0 - a*0 at he
  linear_combination he

theorem zero_free_exponential_type {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hn : ∀ z, f z ≠ 0)
    {A B : ℝ} (hB : 0 ≤ B) (hb : ∀ z, ‖f z‖ ≤ Real.exp (A+B*‖z‖)) :
    ∃ a b : ℂ, ∀ z, f z = Complex.exp (a*z+b) := by
  obtain ⟨h,hh,he⟩ := entire_log_of_nonvanishing hf hn
  have hre (z : ℂ) : (h z).re ≤ A+B*‖z‖ := by
    apply Real.exp_le_exp.mp
    rw [← Complex.norm_exp,he]
    exact hb z
  obtain ⟨a,b,hab⟩ := entire_affine_of_real_part_growth hh hB hre
  exact ⟨a,b,fun z => (he z).symm.trans (congrArg Complex.exp (hab z))⟩

end UV
