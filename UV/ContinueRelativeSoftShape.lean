import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The dimensionless transverse soft Hessian of the relative Wilson
chord after the four-dimensional radial substitution. -/

noncomputable section

namespace UV.RelativeSoft

open MeasureTheory Filter Set Real
open scoped Topology

/-- Tangential eigenvalue of the derivative of the Gaussian chord. -/
def tangentialChord (y : ℝ) : ℝ := exp (-y)

/-- Radial eigenvalue in the norm-one radial direction. -/
def radialChord (y : ℝ) : ℝ := (1 - 2*y) * exp (-y)

def tangentialDifference (y : ℝ) : ℝ := tangentialChord y ^ 2 - tangentialChord y

def radialDifference (y : ℝ) : ℝ := radialChord y ^ 2 - radialChord y

def expMonomial (c : ℝ) (n : ℕ) (y : ℝ) := y^n * exp (-(c*y))

theorem exp_monomial_integrable {c : ℝ} (hc : 0 < c) (n : ℕ) :
    IntegrableOn (expMonomial c n) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n:ℝ)) (b := c)
    (by linarith only [Nat.cast_nonneg (α := ℝ) n]) le_rfl hc
  simpa only [expMonomial,Real.rpow_one,Real.rpow_natCast,neg_mul] using h

theorem exp_monomial_integral {c : ℝ} (hc : 0 < c) (n : ℕ) :
    (∫ y in Ioi (0:ℝ), expMonomial c n y) = (n.factorial : ℝ) / c^(n+1) := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := (n:ℝ)+1) (by positivity) hc
  rw [add_sub_cancel_right,Real.Gamma_nat_eq_factorial,← Nat.cast_succ,Real.rpow_natCast,
    one_div,inv_pow,mul_comm,← div_eq_mul_inv] at h
  simpa only [expMonomial,Real.rpow_natCast,Nat.succ_eq_add_one] using h

private theorem tangential_monomial_expansion (n : ℕ) (y : ℝ) :
    y^n * tangentialDifference y = expMonomial 2 n y - expMonomial 1 n y := by
  simp only [tangentialDifference,tangentialChord,expMonomial,one_mul,pow_two,← Real.exp_add]
  rw [show -y + -y = -(2*y) by ring]
  ring

private theorem radial_monomial_expansion (n : ℕ) (y : ℝ) :
    y^n * radialDifference y =
      (expMonomial 2 n y - 4 * expMonomial 2 (n+1) y + 4 * expMonomial 2 (n+2) y) -
        expMonomial 1 n y + 2 * expMonomial 1 (n+1) y := by
  simp only [radialDifference,radialChord,expMonomial,one_mul,pow_add,pow_one]
  rw [mul_pow,pow_two (exp (-y)),← Real.exp_add,show -y + -y = -(2*y) by ring]
  ring

theorem tangential_moment_integrable (n : ℕ) :
    IntegrableOn (fun y => y^n * tangentialDifference y) (Ioi 0) := by
  simp_rw [tangential_monomial_expansion]
  exact (exp_monomial_integrable two_pos n).sub (exp_monomial_integrable one_pos n)

theorem radial_moment_integrable (n : ℕ) :
    IntegrableOn (fun y => y^n * radialDifference y) (Ioi 0) := by
  simp_rw [radial_monomial_expansion]
  exact ((((exp_monomial_integrable two_pos n).sub
    ((exp_monomial_integrable two_pos (n+1)).const_mul 4)).add
    ((exp_monomial_integrable two_pos (n+2)).const_mul 4)).sub
    (exp_monomial_integrable one_pos n)).add ((exp_monomial_integrable one_pos (n+1)).const_mul 2)

theorem tangential_moment_exact (n : ℕ) :
    (∫ y in Ioi (0:ℝ), y^n * tangentialDifference y) =
      (n.factorial : ℝ) / 2^(n+1) - (n.factorial : ℝ) := by
  simp_rw [tangential_monomial_expansion]
  rw [integral_sub (exp_monomial_integrable two_pos n) (exp_monomial_integrable one_pos n),
    exp_monomial_integral two_pos,exp_monomial_integral one_pos,one_pow,div_one]

theorem radial_moment_exact (n : ℕ) :
    (∫ y in Ioi (0:ℝ), y^n * radialDifference y) =
      (n.factorial : ℝ) / 2^(n+1) - 4 * ((n+1).factorial : ℝ) / 2^(n+2) +
        4 * ((n+2).factorial : ℝ) / 2^(n+3) - (n.factorial : ℝ) + 2 * ((n+1).factorial : ℝ) := by
  let A := expMonomial 2 n
  let B (y : ℝ) := 4 * expMonomial 2 (n+1) y
  let C (y : ℝ) := 4 * expMonomial 2 (n+2) y
  let D := expMonomial 1 n
  let J (y : ℝ) := 2 * expMonomial 1 (n+1) y
  have hA : IntegrableOn A (Ioi (0:ℝ)) := exp_monomial_integrable two_pos n
  have hB : IntegrableOn B (Ioi (0:ℝ)) := (exp_monomial_integrable two_pos (n+1)).const_mul _
  have hC : IntegrableOn C (Ioi (0:ℝ)) := (exp_monomial_integrable two_pos (n+2)).const_mul _
  have hD : IntegrableOn D (Ioi (0:ℝ)) := exp_monomial_integrable one_pos n
  have hJ : IntegrableOn J (Ioi (0:ℝ)) := (exp_monomial_integrable one_pos (n+1)).const_mul _
  simp_rw [radial_monomial_expansion]
  change (∫ y in Ioi (0:ℝ), A y - B y + C y - D y + J y) = _
  have h₁ := integral_add (((hA.sub hB).add hC).sub hD) hJ
  have h₂ := integral_sub ((hA.sub hB).add hC) hD
  have h₃ := integral_add (hA.sub hB) hC
  have h₄ := integral_sub hA hB
  simp only [Pi.add_apply,Pi.sub_apply] at h₁ h₂ h₃ h₄
  rw [h₁,h₂,h₃,h₄]
  simp only [A,B,C,D,J,integral_const_mul,exp_monomial_integral two_pos,
    exp_monomial_integral one_pos,one_pow,div_one]
  ring

/-- The radial integrand in the squared radius variable y = σ²‖k‖².
The dimensionless mass is s = mσ. -/
def softShapeIntegrand (s y : ℝ) : ℝ :=
  (y/(s^2+y)) * (3*tangentialDifference y + ((s^2-y)/(s^2+y))*radialDifference y)

def relativeSoftShape (s : ℝ) : ℝ := ∫ y in Ioi (0:ℝ), softShapeIntegrand s y

private def momentBound (n : ℕ) (y : ℝ) :=
  3 * ‖y^n * tangentialDifference y‖ + ‖y^n * radialDifference y‖

private theorem moment_bound_integrable (n : ℕ) : IntegrableOn (momentBound n) (Ioi (0:ℝ)) :=
  (((tangential_moment_integrable n).norm).const_mul 3).add (radial_moment_integrable n).norm

private theorem soft_shape_ratio_bounds (s : ℝ) {y : ℝ} (hy : 0 < y) :
    0 ≤ y/(s^2+y) ∧ y/(s^2+y) ≤ 1 ∧ |(s^2-y)/(s^2+y)| ≤ 1 := by
  have hp : 0 < s^2+y := add_pos_of_nonneg_of_pos (sq_nonneg s) hy
  refine ⟨div_nonneg hy.le hp.le,(div_le_one₀ hp).mpr (by linarith [sq_nonneg s]),?_⟩
  rw [abs_div,abs_of_pos hp,div_le_one₀ hp,abs_le]
  constructor <;> linarith [sq_nonneg s,hy.le]

private theorem soft_shape_unweighted_bound (s : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖softShapeIntegrand s y‖ ≤ momentBound 0 y := by
  obtain ⟨h₀,hA,hB⟩ := soft_shape_ratio_bounds s hy
  unfold softShapeIntegrand momentBound
  rw [norm_mul,Real.norm_of_nonneg h₀,pow_zero,one_mul,one_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) hA).trans
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]
  exact add_le_add_left (mul_le_of_le_one_left (norm_nonneg _) (by rwa [Real.norm_eq_abs])) _

private theorem soft_shape_mass_weighted_bound (s : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖s^2 * softShapeIntegrand s y‖ ≤ momentBound 1 y := by
  obtain ⟨_,_,hB⟩ := soft_shape_ratio_bounds s hy
  let A := s^2 * (y/(s^2+y))
  have hA₀ : 0 ≤ A := by dsimp [A]; positivity
  have hA : A ≤ y := by
    dsimp only [A]
    rw [← mul_div_assoc,div_le_iff₀ (by positivity)]
    nlinarith only [sq_nonneg y]
  unfold softShapeIntegrand momentBound
  rw [← mul_assoc,norm_mul,show s^2*(y/(s^2+y)) = A from rfl,Real.norm_of_nonneg hA₀]
  apply (mul_le_mul_of_nonneg_right hA (norm_nonneg _)).trans
  apply (mul_le_mul_of_nonneg_left (norm_add_le _ _) hy.le).trans
  simp only [pow_one,norm_mul,Real.norm_of_nonneg hy.le,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]
  calc
    _ ≤ y * (3 * ‖tangentialDifference y‖ + ‖radialDifference y‖) := by
      apply mul_le_mul_of_nonneg_left _ hy.le
      exact add_le_add_left (mul_le_of_le_one_left (norm_nonneg _) (by rwa [Real.norm_eq_abs])) _
    _ = _ := by ring

private theorem soft_shape_integrand_measurable (s : ℝ) : Measurable (softShapeIntegrand s) := by
  unfold softShapeIntegrand tangentialDifference radialDifference tangentialChord radialChord
  fun_prop

theorem soft_shape_integrable (s : ℝ) : IntegrableOn (softShapeIntegrand s) (Ioi 0) :=
  (moment_bound_integrable 0).mono' (soft_shape_integrand_measurable s).aestronglyMeasurable
    ((ae_restrict_mem measurableSet_Ioi).mono fun _ hy => soft_shape_unweighted_bound s hy)

theorem relative_soft_shape_continuous : Continuous relativeSoftShape := by
  apply continuous_iff_continuousAt.mpr
  intro s
  unfold ContinuousAt relativeSoftShape
  apply tendsto_integral_filter_of_dominated_convergence (momentBound 0)
    (Eventually.of_forall fun t => (soft_shape_integrand_measurable t).aestronglyMeasurable)
    (Eventually.of_forall fun t => (ae_restrict_mem measurableSet_Ioi).mono fun y hy =>
      soft_shape_unweighted_bound t hy) (moment_bound_integrable 0)
  apply (ae_restrict_mem measurableSet_Ioi).mono
  intro y hy
  have hp (t : ℝ) : t^2+y ≠ 0 := (add_pos_of_nonneg_of_pos (sq_nonneg t) hy).ne'
  apply Continuous.continuousAt
  have hd : Continuous (fun t : ℝ => t^2 + y) := by fun_prop
  change Continuous (fun t : ℝ =>
    (y/(t^2+y)) * (3*tangentialDifference y + ((t^2-y)/(t^2+y))*radialDifference y))
  exact (continuous_const.div hd hp).mul
    (continuous_const.add (((continuous_pow 2 |>.sub continuous_const).div hd hp).mul continuous_const))

theorem relative_soft_shape_zero : relativeSoftShape 0 = -3 := by
  unfold relativeSoftShape
  have he : (∫ y in Ioi (0:ℝ), softShapeIntegrand 0 y) =
      ∫ y in Ioi (0:ℝ), 3*tangentialDifference y - radialDifference y := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have hy' : y ≠ 0 := ne_of_gt hy
    simp only [softShapeIntegrand,zero_pow (by decide : (2:ℕ) ≠ 0),zero_add,
      neg_div,div_self hy',one_mul,neg_one_mul,sub_eq_add_neg]
  rw [he]
  have ht : IntegrableOn tangentialDifference (Ioi (0:ℝ)) := by
    simpa only [pow_zero,one_mul] using tangential_moment_integrable 0
  have hr : IntegrableOn radialDifference (Ioi (0:ℝ)) := by
    simpa only [pow_zero,one_mul] using radial_moment_integrable 0
  rw [integral_sub (ht.const_mul 3) hr,integral_const_mul]
  have ht' := tangential_moment_exact 0
  have hr' := radial_moment_exact 0
  norm_num [Nat.factorial_succ] at ht' hr'
  rw [ht',hr']
  norm_num

private theorem soft_shape_mass_pointwise {y : ℝ} (hy : 0 < y) :
    Tendsto (fun s : ℝ => s^2 * softShapeIntegrand s y) atTop
      (𝓝 (y * (3*tangentialDifference y + radialDifference y))) := by
  have hi : Tendsto (fun s : ℝ => (s^2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0))
  have hY := hi.const_mul y
  have hD : Tendsto (fun s : ℝ => 1 + y * (s^2)⁻¹) atTop (𝓝 1) := by
    simpa only [mul_zero,add_zero] using hY.const_add 1
  have hA : Tendsto (fun s : ℝ => y / (1+y*(s^2)⁻¹)) atTop (𝓝 y) := by
    simpa only [div_one] using tendsto_const_nhds.div hD one_ne_zero
  have hB : Tendsto (fun s : ℝ => (1-y*(s^2)⁻¹)/(1+y*(s^2)⁻¹)) atTop (𝓝 1) := by
    simpa only [mul_zero,sub_zero,div_one] using (tendsto_const_nhds.sub hY).div hD one_ne_zero
  have h := hA.mul ((hB.mul_const (radialDifference y)).const_add (3*tangentialDifference y))
  simp only [one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
  unfold softShapeIntegrand
  have hsq : s^2 ≠ 0 := pow_ne_zero _ hs.ne'
  field_simp [hsq,(add_pos_of_nonneg_of_pos (sq_nonneg s) hy).ne']

theorem relative_soft_shape_mass_atTop :
    Tendsto (fun s : ℝ => s^2 * relativeSoftShape s) atTop (𝓝 (3/2)) := by
  have h : Tendsto (fun s : ℝ => ∫ y in Ioi (0:ℝ), s^2 * softShapeIntegrand s y) atTop
      (𝓝 (∫ y in Ioi (0:ℝ), y * (3*tangentialDifference y + radialDifference y))) :=
    tendsto_integral_filter_of_dominated_convergence (momentBound 1)
      (Eventually.of_forall fun s => ((measurable_const.mul (soft_shape_integrand_measurable s))).aestronglyMeasurable)
      (Eventually.of_forall fun s => (ae_restrict_mem measurableSet_Ioi).mono fun y hy =>
        soft_shape_mass_weighted_bound s hy) (moment_bound_integrable 1)
      ((ae_restrict_mem measurableSet_Ioi).mono fun _ hy => soft_shape_mass_pointwise hy)
  simp_rw [integral_const_mul] at h
  have ht : IntegrableOn (fun y => y*tangentialDifference y) (Ioi (0:ℝ)) := by
    simpa only [pow_one] using tangential_moment_integrable 1
  have hr : IntegrableOn (fun y => y*radialDifference y) (Ioi (0:ℝ)) := by
    simpa only [pow_one] using radial_moment_integrable 1
  have he : (∫ y in Ioi (0:ℝ), y * (3*tangentialDifference y + radialDifference y)) =
      3 * (∫ y in Ioi (0:ℝ), y*tangentialDifference y) +
        ∫ y in Ioi (0:ℝ), y*radialDifference y := by
    calc
      _ = ∫ y in Ioi (0:ℝ), 3 * (y*tangentialDifference y) + y*radialDifference y := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y _
        ring
      _ = _ := by
        rw [integral_add (ht.const_mul 3) hr,integral_const_mul]
  rw [he] at h
  have ha := tangential_moment_exact 1
  have hb := radial_moment_exact 1
  norm_num [Nat.factorial_succ] at ha hb
  rw [ha,hb] at h
  norm_num at h ⊢
  simpa only [relativeSoftShape] using h

theorem relative_soft_shape_bounds :
    ∃ M₀ M₂ : ℝ, 0 ≤ M₀ ∧ 0 ≤ M₂ ∧ ∀ s : ℝ,
      ‖relativeSoftShape s‖ ≤ M₀ ∧ ‖s^2 * relativeSoftShape s‖ ≤ M₂ := by
  refine ⟨∫ y in Ioi (0:ℝ), momentBound 0 y,∫ y in Ioi (0:ℝ), momentBound 1 y,?_,?_,?_⟩
  · exact integral_nonneg (fun y => by unfold momentBound; positivity)
  · exact integral_nonneg (fun y => by unfold momentBound; positivity)
  · intro s
    constructor
    · exact norm_integral_le_of_norm_le (moment_bound_integrable 0)
        ((ae_restrict_mem measurableSet_Ioi).mono fun y hy => soft_shape_unweighted_bound s hy)
    · rw [relativeSoftShape,← integral_const_mul]
      exact norm_integral_le_of_norm_le (moment_bound_integrable 1)
        ((ae_restrict_mem measurableSet_Ioi).mono fun y hy => soft_shape_mass_weighted_bound s hy)

end UV.RelativeSoft
