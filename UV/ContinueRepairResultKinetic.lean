import UV.ContinueRepairResultDirac
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Regularity of the bare magnetic symbol l(k)=√(c(k)−m), including
its removable singularity at the origin. -/

noncomputable section
open UV.FurtherOptical Filter Set
open scoped Topology ContDiff

namespace UV

def repairKineticRoot (m τ : ℝ) (k : ChargeSpatialMomentum) : ℝ :=
  Real.sqrt (diagonal m τ k - m)

private def repairExpSlope (x : ℝ) := (dslope Complex.exp 0 (x:ℂ)).re

private theorem repair_exp_slope_contDiff : ContDiff ℝ ∞ repairExpSlope := by
  have hd : Differentiable ℂ (dslope Complex.exp 0) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope univ_mem).mpr Complex.differentiable_exp.differentiableOn)
  exact Complex.reCLM.contDiff.comp ((hd.contDiff.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff)

private theorem repair_exp_slope_mul (x : ℝ) : x * repairExpSlope x = Real.exp x - 1 := by
  have h := congrArg Complex.re (sub_smul_dslope Complex.exp 0 (x:ℂ))
  simpa only [sub_zero,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
    Complex.sub_re,Complex.exp_zero,Complex.one_re,←Complex.ofReal_exp,repairExpSlope] using h

private theorem repair_exp_slope_pos (x : ℝ) : 0 < repairExpSlope x := by
  obtain hx|rfl|hx := lt_trichotomy x 0
  · have he := Real.exp_lt_one_iff.mpr hx
    by_contra! hn
    linarith [mul_nonneg_of_nonpos_of_nonpos hx.le hn,repair_exp_slope_mul x]
  · norm_num [repairExpSlope,dslope_same,Complex.deriv_exp]
  · have he := Real.one_lt_exp_iff.mpr hx
    by_contra! hn
    linarith [mul_nonpos_of_nonneg_of_nonpos hx.le hn,repair_exp_slope_mul x]

private theorem repair_attenuation_sq (τ : ℝ) (k : ChargeSpatialMomentum) :
    attenuation τ k^2 = Real.exp (-(2*τ)*‖k‖^2) := by
  rw [attenuation,pow_two,←Real.exp_add]; congr 1; ring

private theorem repair_gap_factors {m τ : ℝ} (hτ : 0 ≤ τ) (k : ChargeSpatialMomentum) :
    (diagonal m τ k-m)*(diagonal m τ k+m) =
      (‖k‖^2)^2*(2*τ*repairExpSlope (-(2*τ)*‖k‖^2)) := by
  have hd := diagonal_sq (m := m) hτ k
  rw [energy_sq,repair_attenuation_sq] at hd
  have he := repair_exp_slope_mul (-(2*τ)*‖k‖^2)
  linear_combination (norm := ring) hd + ‖k‖^2*he

theorem repair_kinetic_square {m τ : ℝ} (hm : 0 < m) (hτ : 0 ≤ τ) (k : ChargeSpatialMomentum) :
    m + repairKineticRoot m τ k^2 = diagonal m τ k := by
  rw [repairKineticRoot,Real.sq_sqrt (sub_nonneg.mpr (repair_diagonal_lower hm hτ k))]
  ring

theorem repair_kinetic_root_contDiff {m τ : ℝ} (hm : 0 < m) (hτ : 0 < τ) :
    ContDiff ℝ ∞ (repairKineticRoot m τ) := by
  let r := fun k : ChargeSpatialMomentum => ‖k‖^2
  let V := fun k => 2*τ*repairExpSlope (-(2*τ)*r k)/(diagonal m τ k+m)
  have hr : ContDiff ℝ ∞ r := contDiff_norm_sq ℝ
  have hden k : 0 < diagonal m τ k + m := by linarith [repair_diagonal_lower hm hτ.le k]
  have hv k : 0 < V k := div_pos (mul_pos (by positivity) (repair_exp_slope_pos _)) (hden k)
  have hc : ContDiff ℝ ∞ (diagonal m τ) := by
    have he : diagonal m τ = fun k => Real.sqrt (m^2 + r k - r k*Real.exp (-(2*τ)*r k)) := by
      funext k; rw [FurtherOptical.diagonal,energy_sq,repair_attenuation_sq]
    rw [he]
    refine ((contDiff_const.add hr).sub (hr.mul ((contDiff_const.mul hr).exp))).sqrt (fun k => ?_)
    have hh := diagonal_sq (m := m) hτ.le k
    rw [energy_sq,repair_attenuation_sq] at hh
    exact hh ▸ (sq_pos_of_pos (hm.trans_le (repair_diagonal_lower hm hτ.le k))).ne'
  have hV : ContDiff ℝ ∞ V :=
    (contDiff_const.mul (repair_exp_slope_contDiff.comp (contDiff_const.mul hr))).div
      (hc.add contDiff_const) (fun k => (hden k).ne')
  have he (k) : repairKineticRoot m τ k = r k * Real.sqrt (V k) := by
    have h := repair_gap_factors (m := m) hτ.le k
    have hx : diagonal m τ k-m = (r k)^2 * V k := by
      dsimp [V,r]
      rw [←mul_div_assoc,eq_div_iff (hden k).ne']; exact h
    rw [repairKineticRoot,hx,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (sq_nonneg _)]
  rw [funext he]
  exact hr.mul (hV.sqrt (fun k => (hv k).ne'))

/-- Quantified fourth-order mass-slot correction and cubic spatial hop
error, for all carrier momenta on the locked plane. -/
theorem repair_low_momentum {m τ : ℝ} (hm : 0 < m) (hτ : 0 ≤ τ) (k : ChargeSpatialMomentum) :
    0 ≤ diagonal m τ k-m ∧ diagonal m τ k-m ≤ (τ/m)*‖k‖^4 ∧
    ‖attenuation τ k • k - k‖ ≤ τ*‖k‖^3 := by
  let r := ‖k‖^2
  have hgap := repair_diagonal_lower hm hτ k
  have ha : attenuation τ k ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hτ) (sq_nonneg _))
  have hd := diagonal_sq (m := m) hτ k
  rw [energy_sq,repair_attenuation_sq] at hd
  have hlin := Real.add_one_le_exp (-(2*τ)*r)
  have hupper : (diagonal m τ k-m)*(diagonal m τ k+m) ≤ (2*τ)*r^2 := by
    dsimp only [r] at hlin ⊢
    nlinarith [mul_le_mul_of_nonneg_right hlin (sq_nonneg ‖k‖)]
  refine ⟨sub_nonneg.mpr hgap,?_,?_⟩
  · rw [div_mul_eq_mul_div,le_div_iff₀ hm]
    dsimp only [r] at hupper
    nlinarith [sq_nonneg (diagonal m τ k-m)]
  · rw [show attenuation τ k • k-k = (attenuation τ k-1) • k by rw [sub_smul,one_smul],norm_smul,
      Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr ha)]
    have hlin' := Real.add_one_le_exp (-τ*‖k‖^2)
    change -(Real.exp (-τ*‖k‖^2)-1)*‖k‖ ≤ _
    nlinarith [mul_le_mul_of_nonneg_right hlin' (norm_nonneg k)]

end UV
