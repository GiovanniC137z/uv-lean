import UV.ContinueHeatMaxwellSignAngular
import UV.ContinueHeatMaxwellSignIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! The endpoint term in the heat-link angular reduction. -/

noncomputable section

namespace UV.HeatMaxwell

open MeasureTheory Set Filter
open scoped Topology

def heatNormalizedRadius (x u : ℝ) : ℝ := heatRadius u / (x + heatRadius u)

def heatNormalizedGaussian (x u : ℝ) : ℝ := Real.exp (-2 * u) / (x + heatRadius u)

theorem heatNormalizedGaussian_eq {u : ℝ} (hu : 0 < u) (x : ℝ) :
    heatNormalizedGaussian x u = heatNormalizedRadius x u / u := by
  unfold heatNormalizedGaussian heatNormalizedRadius heatRadius
  field_simp [hu.ne']

theorem heatNormalizedRadius_hasDerivAt {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    HasDerivAt (heatNormalizedRadius x)
      (heatNormalizedRadius x u * (1 - heatNormalizedRadius x u) * (1 / u - 2)) u := by
  have hd : 0 < x + heatRadius u := add_pos hx (heatRadius_pos hu)
  have hy := heatRadius_hasDerivAt u
  have h := hy.div (hy.const_add x) hd.ne'
  convert h using 1
  unfold heatNormalizedRadius
  generalize he : Real.exp (-2 * u) = z
  unfold heatRadius at *
  rw [he] at hd
  rw [he]
  field_simp [hu.ne']

theorem heatRadialPrimitive_hasDerivAt {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    HasDerivAt (fun v => heatRadialPrimitive v (heatNormalizedRadius x v))
      (heatRadialPrimitiveDerivative u (heatNormalizedRadius x u)) u := by
  have hi := hasDerivAt_id u
  have hz := heatNormalizedRadius_hasDerivAt hx hu
  have hf₁ := (hi.mul ((((hi.pow 2).const_mul 2).sub (hi.const_mul 9)).add_const 3)).div_const 36
  have hf₂ := ((((hi.const_mul 2).sub_const 1).neg).mul
    ((((hi.pow 2).const_mul 2).sub (hi.const_mul 6)).add_const 5)).div_const 24
  have hf₃ := (((hi.const_mul 2).sub_const 1).pow 3).div_const 36
  convert ((hf₁.mul hz).add (hf₂.mul (hz.pow 2))).add (hf₃.mul (hz.pow 3)) using 1
  simp [heatRadialPrimitiveDerivative, heatRadialPrimitive₁, heatRadialPrimitive₂,
    heatRadialPrimitive₃]
  ring

private theorem heatNormalizedRadius_nonneg {x u : ℝ} (hx : 0 < x) (hu : 0 ≤ u) :
    0 ≤ heatNormalizedRadius x u := by
  have hy : 0 ≤ heatRadius u := mul_nonneg hu (Real.exp_pos _).le
  exact div_nonneg hy (add_nonneg hx.le hy)

private theorem heatNormalizedRadius_le {x u : ℝ} (hx : 0 < x) (hu : 0 ≤ u) :
    heatNormalizedRadius x u ≤ x⁻¹ * (u * Real.exp (-2 * u)) := by
  have hy : 0 ≤ heatRadius u := mul_nonneg hu (Real.exp_pos _).le
  unfold heatNormalizedRadius
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hx (le_add_of_nonneg_right hy)) hy

private theorem heat_monomialNormalizedRadius_tendsto {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Tendsto (fun u : ℝ => u ^ n * heatNormalizedRadius x u) atTop (𝓝 0) := by
  have hE : Tendsto (fun u : ℝ => x⁻¹ * (u ^ (n + 1) * Real.exp (-2 * u))) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((n + 1 : ℕ) : ℝ) 2 (by norm_num)).const_mul x⁻¹
  refine squeeze_zero' ?_ ?_ hE
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    exact mul_nonneg (pow_nonneg hu _) (heatNormalizedRadius_nonneg hx hu)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    calc
      _ ≤ u ^ n * (x⁻¹ * (u * Real.exp (-2 * u))) :=
        mul_le_mul_of_nonneg_left (heatNormalizedRadius_le hx hu) (pow_nonneg hu _)
      _ = _ := by rw [pow_succ]; ring

private theorem heat_monomialNormalizedRadius_pow_tendsto {x : ℝ} (hx : 0 < x)
    (n j : ℕ) : Tendsto (fun u : ℝ => u ^ n * heatNormalizedRadius x u ^ (j + 1)) atTop (𝓝 0) := by
  have hZ : Tendsto (heatNormalizedRadius x) atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul] using heat_monomialNormalizedRadius_tendsto hx 0
  have h := (heat_monomialNormalizedRadius_tendsto hx n).mul (hZ.pow j)
  rw [zero_mul] at h
  apply h.congr'
  exact Eventually.of_forall fun u => by
    change u ^ n * heatNormalizedRadius x u * heatNormalizedRadius x u ^ j =
      u ^ n * heatNormalizedRadius x u ^ (j + 1)
    rw [pow_succ]
    ring

theorem heatRadialPrimitive_atTop {x : ℝ} (hx : 0 < x) :
    Tendsto (fun u => heatRadialPrimitive u (heatNormalizedRadius x u)) atTop (𝓝 0) := by
  have hp (n j : ℕ) (c : ℝ) :
      Tendsto (fun u => c * (u ^ n * heatNormalizedRadius x u ^ (j + 1))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (heat_monomialNormalizedRadius_pow_tendsto hx n j).const_mul c
  have h₁ := ((hp 3 0 (1/18)).add (hp 2 0 (-1/4))).add (hp 1 0 (1/12))
  have h₂ := (((hp 3 1 (-1/6)).add (hp 2 1 (7/12))).add (hp 1 1 (-2/3))).add (hp 0 1 (5/24))
  have h₃ := (((hp 3 2 (2/9)).add (hp 2 2 (-1/3))).add (hp 1 2 (1/6))).add (hp 0 2 (-1/36))
  have h := (h₁.add h₂).add h₃
  simp only [add_zero] at h
  apply h.congr'
  exact Eventually.of_forall fun u => by
    simp [heatRadialPrimitive, heatRadialPrimitive₁, heatRadialPrimitive₂, heatRadialPrimitive₃]
    ring

private theorem heatGaussian_power_monomial_integrable {x : ℝ} (hx : 0 < x) (n j : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ n * heatNormalizedGaussian x u ^ (j + 1)) (Ioi 0) := by
  have hg : IntegrableOn (fun u : ℝ => u ^ n * Real.exp (-2 * u)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := 2)
      (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by norm_num) (by norm_num)
    simpa [Real.rpow_natCast, Real.rpow_one] using h
  have hm : Measurable (fun u : ℝ => u ^ n * heatNormalizedGaussian x u ^ (j + 1)) := by
    unfold heatNormalizedGaussian heatRadius
    fun_prop
  apply (hg.const_mul (x⁻¹ ^ (j + 1))).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with u hu
  have hu' : 0 < u := hu
  have hy := heatRadius_pos hu'
  have hq0 : 0 ≤ heatNormalizedGaussian x u := by
    unfold heatNormalizedGaussian
    exact div_nonneg (Real.exp_pos _).le (add_pos hx hy).le
  have hq1 : heatNormalizedGaussian x u ≤ x⁻¹ * Real.exp (-2 * u) := by
    unfold heatNormalizedGaussian
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hx (le_add_of_nonneg_right hy.le))
      (Real.exp_pos _).le
  have hq2 : heatNormalizedGaussian x u ≤ x⁻¹ :=
    hq1.trans (mul_le_of_le_one_right (inv_nonneg.mpr hx.le)
      (Real.exp_le_one_iff.mpr (by linarith)))
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hu'.le _) (pow_nonneg hq0 _))]
  calc
    _ = u ^ n * (heatNormalizedGaussian x u ^ j * heatNormalizedGaussian x u) := by rw [pow_succ]
    _ ≤ u ^ n * (x⁻¹ ^ j * (x⁻¹ * Real.exp (-2 * u))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (pow_le_pow_left₀ hq0 hq2 j) hq1 hq0 (by positivity)) (pow_nonneg hu'.le _)
    _ = _ := by rw [pow_succ]; ring

private theorem heatGaussian_power_polynomial_integrable {x : ℝ} (hx : 0 < x)
    (p : Polynomial ℝ) (j : ℕ) :
    IntegrableOn (fun u : ℝ => p.eval u * heatNormalizedGaussian x u ^ (j + 1)) (Ioi 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    apply (hp.add hq).congr
    exact Eventually.of_forall fun u => by simp only [Pi.add_apply, Polynomial.eval_add, add_mul]
  | monomial n a =>
    apply ((heatGaussian_power_monomial_integrable hx n j).const_mul a).congr
    exact Eventually.of_forall fun u => by simp only [Polynomial.eval_monomial, mul_assoc]

/-- Gaussian domination of the exact angular mean for every positive mass. -/
theorem heatAngularMean_radial_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u => u * heatAngularMean u (heatNormalizedGaussian x u)) (Ioi 0) := by
  let X : Polynomial ℝ := Polynomial.X
  let C := Polynomial.C (R := ℝ)
  let p₁ := C (-1/9) * X ^ 4 + C (13/18) * X ^ 3 + C (-11/12) * X ^ 2 + C (1/6) * X
  let p₂ := C (7/9) * X ^ 5 + C (-61/18) * X ^ 4 + C (17/4) * X ^ 3 +
    C (-31/12) * X ^ 2 + C (3/4) * X
  let p₃ := C (-1/2) * X ^ 2 * (X - 1) ^ 2 * (C 2 * X - 1) ^ 2
  let p₄ := C (1/12) * X ^ 3 * (C 2 * X - 1) ^ 4
  have h := (((heatGaussian_power_polynomial_integrable hx p₁ 0).add
    (heatGaussian_power_polynomial_integrable hx p₂ 1)).add
    (heatGaussian_power_polynomial_integrable hx p₃ 2)).add
    (heatGaussian_power_polynomial_integrable hx p₄ 3)
  apply h.congr
  exact Eventually.of_forall fun u => by
    simp only [Pi.add_apply, p₁, p₂, p₃, p₄, C, X, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one,
      zero_add, pow_one]
    unfold heatAngularMean heatAngle00 heatAngle10 heatAngle01 heatAngle11
    ring

theorem heatRadialPrimitive_deriv_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u => heatRadialPrimitiveDerivative u (heatNormalizedRadius x u)) (Ioi 0) := by
  apply ((heatAngularMean_radial_integrable hx).sub
    ((heatRadialIntegrand_integrable hx).mul_const (6⁻¹ : ℝ))).congr
  refine (ae_restrict_mem measurableSet_Ioi).mono fun u hu => ?_
  simp only [Pi.sub_apply]
  rw [heatNormalizedGaussian_eq hu, heatAngularMean_reduction hu.ne']
  unfold heatRadialIntegrand heatNormalizedRadius
  ring

private theorem heatRadialPrimitive_continuousAt_zero {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun u => heatRadialPrimitive u (heatNormalizedRadius x u)) 0 := by
  have hden : x + heatRadius 0 ≠ 0 := by simpa [heatRadius] using hx.ne'
  have hz : ContinuousAt (heatNormalizedRadius x) 0 :=
    heatRadius_continuous.continuousAt.div
      (continuousAt_const.add heatRadius_continuous.continuousAt) hden
  unfold heatRadialPrimitive heatRadialPrimitive₁ heatRadialPrimitive₂ heatRadialPrimitive₃
  fun_prop

private theorem heatRadialPrimitive_at_zero (x : ℝ) :
    heatRadialPrimitive 0 (heatNormalizedRadius x 0) = 0 := by
  simp [heatNormalizedRadius, heatRadius, heatRadialPrimitive]

/-- Both endpoints of the analytic primitive have zero contribution. -/
theorem heatRadialPrimitive_integral_zero {x : ℝ} (hx : 0 < x)
    (hi : IntegrableOn (fun u => heatRadialPrimitiveDerivative u (heatNormalizedRadius x u))
      (Ioi 0)) :
    (∫ u in Ioi 0, heatRadialPrimitiveDerivative u (heatNormalizedRadius x u)) = 0 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (heatRadialPrimitive_continuousAt_zero hx).continuousWithinAt
    (fun _ hu => heatRadialPrimitive_hasDerivAt hx hu) hi (heatRadialPrimitive_atTop hx)
  rw [heatRadialPrimitive_at_zero, sub_zero] at h
  exact h

/-- The unit-width angular quadratic response before removal of the total derivative. -/
def heatAngularCoefficient (x : ℝ) : ℝ :=
  (4 * Real.pi ^ 2)⁻¹ * ∫ u in Ioi 0, u * heatAngularMean u (heatNormalizedGaussian x u)

/-- The radial primitive does not contribute to the angularly reduced soft response. -/
theorem heatAngularCoefficient_eq_radial {x : ℝ} (hx : 0 < x) :
    heatAngularCoefficient x = heatMaxwellCoefficient x := by
  have hi := heatRadialPrimitive_deriv_integrable hx
  unfold heatAngularCoefficient heatMaxwellCoefficient
  have hI := (heatRadialIntegrand_integrable hx).mul_const (6⁻¹ : ℝ)
  have hEq : (∫ u in Ioi (0 : ℝ), u * heatAngularMean u (heatNormalizedGaussian x u)) =
      ∫ u in Ioi (0 : ℝ), heatRadialIntegrand x u * (6⁻¹ : ℝ) +
        heatRadialPrimitiveDerivative u (heatNormalizedRadius x u) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    rw [heatNormalizedGaussian_eq hu, heatAngularMean_reduction hu.ne']
    unfold heatRadialIntegrand heatNormalizedRadius
    ring
  rw [hEq, integral_add hI hi, heatRadialPrimitive_integral_zero hx hi, add_zero,
    integral_mul_const]
  field_simp
  ring

theorem heatAngularCoefficient_pos {x : ℝ} (hx : 0 < x) :
    0 < heatAngularCoefficient x :=
  heatAngularCoefficient_eq_radial hx ▸ heatMaxwellCoefficient_pos hx

end UV.HeatMaxwell
