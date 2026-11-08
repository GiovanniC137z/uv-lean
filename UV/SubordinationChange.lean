import UV.KernelMeasure
import Mathlib.MeasureTheory.Function.JacobianOneDim

noncomputable section
open MeasureTheory Set Real

namespace UV

def subordinateShift (b x : ℝ) : ℝ := x - b / x

theorem subordinateShift_strictMono {b : ℝ} (hb : 0 < b) :
    StrictMonoOn (subordinateShift b) (Ioi 0) := by
  intro x hx y hy hxy
  have hh : b / y < b / x := div_lt_div_of_pos_left hb hx hxy
  unfold subordinateShift
  linarith

theorem subordinateShift_image {b : ℝ} (hb : 0 < b) :
    subordinateShift b '' Ioi 0 = univ := by
  apply eq_univ_of_forall
  intro y
  let x : ℝ := (y + Real.sqrt (y ^ 2 + 4 * b)) / 2
  have hs : Real.sqrt (y ^ 2 + 4 * b) ^ 2 = y ^ 2 + 4 * b :=
    Real.sq_sqrt (by positivity)
  have hlt : -y < Real.sqrt (y ^ 2 + 4 * b) :=
    Real.lt_sqrt_of_sq_lt (by nlinarith)
  have hx : 0 < x := by dsimp [x]; linarith
  refine ⟨x, hx, ?_⟩
  unfold subordinateShift
  field_simp [ne_of_gt hx]
  dsimp [x]
  nlinarith

theorem subordinateShift_hasDerivAt (b : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (subordinateShift b) (1 + b / x ^ 2) x := by
  unfold subordinateShift
  have hh := (hasDerivAt_id x).sub ((hasDerivAt_const x b).div (hasDerivAt_id x) hx.ne')
  convert hh using 1
  simp
  field_simp
  ring

theorem subordinateShift_deriv_nonneg {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    0 ≤ 1 + b / x ^ 2 := by positivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem subordinateShift_integral {b : ℝ} (hb : 0 < b) (f : ℝ → E) :
    (∫ x : ℝ in Ioi 0, (1 + b / x ^ 2) • f (subordinateShift b x)) = ∫ y : ℝ, f y := by
  have hh := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun x hx => (subordinateShift_hasDerivAt b hx).hasDerivWithinAt)
    (subordinateShift_strictMono hb).injOn f
  rw [subordinateShift_image hb, setIntegral_univ] at hh
  rw [hh]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [abs_of_nonneg (subordinateShift_deriv_nonneg hb hx)]

theorem subordinateShift_integrable_iff {b : ℝ} (hb : 0 < b) (f : ℝ → E) :
    Integrable f ↔
      IntegrableOn (fun x : ℝ => (1 + b / x ^ 2) • f (subordinateShift b x)) (Ioi 0) := by
  have hh := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun x hx => (subordinateShift_hasDerivAt b hx).hasDerivWithinAt)
    (subordinateShift_strictMono hb).injOn f
  rw [subordinateShift_image hb, integrableOn_univ] at hh
  refine hh.trans (integrable_congr ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [abs_of_nonneg (subordinateShift_deriv_nonneg hb hx)]

theorem subordinateShift_gaussian_integrable {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => (1 + b / x ^ 2) *
      Real.exp (-(subordinateShift b x) ^ 2)) (Ioi 0) := by
  have hg : Integrable (fun y : ℝ => Real.exp (-(y ^ 2))) := by
    simpa only [neg_one_mul] using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  have hh := (subordinateShift_integrable_iff hb
    (fun y : ℝ => Real.exp (-(y ^ 2)))).mp hg
  simpa only [one_mul, smul_eq_mul] using hh

theorem subordinateShift_gaussian_integral {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ in Ioi 0, (1 + b / x ^ 2) *
      Real.exp (-(subordinateShift b x) ^ 2)) = Real.sqrt Real.pi := by
  have hh := subordinateShift_integral hb (fun y : ℝ => Real.exp (-(y ^ 2)))
  have hg : (∫ y : ℝ, Real.exp (-(y ^ 2))) = Real.sqrt Real.pi := by
    simpa only [neg_one_mul, div_one] using integral_gaussian 1
  simpa only [smul_eq_mul, hg] using hh

end UV
