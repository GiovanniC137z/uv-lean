import UV.ContinueRelativeChargeNormalization
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The radial integration by parts that identifies the single-contact
term in the relative Wilson Hessian with the manuscript's B integral. -/

noncomputable section

open Filter MeasureTheory Set Real
open scoped Topology

namespace UV.SectorPlane

def chordLinearIntegrand (x y : ℝ) : ℝ :=
  exp (-y) * (y / (x + y)) * (3 + ((x - y) / (x + y)) * (1 - 2 * y))

private theorem chord_radial_ratios {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    0 ≤ y / (x + y) ∧ y / (x + y) ≤ 1 ∧ |(x-y)/(x+y)| ≤ 1 := by
  have hs : 0 < x+y := by positivity
  refine ⟨div_nonneg hy hs.le, (div_le_one₀ hs).mpr (by linarith), ?_⟩
  rw [abs_div, abs_of_pos hs, div_le_one₀ hs, abs_le]
  constructor <;> linarith

private theorem chord_linear_norm_le {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    ‖chordLinearIntegrand x y‖ ≤
      4 * UV.RelativeSoft.expMonomial 1 0 y + 2 * UV.RelativeSoft.expMonomial 1 1 y := by
  obtain ⟨h₀, h₁, h₂⟩ := chord_radial_ratios hx hy
  have h₃ : ‖3 + (x-y)/(x+y) * (1-2*y)‖ ≤ 4 + 2*y := by
    apply (norm_add_le _ _).trans
    rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    have h' : ‖1-2*y‖ ≤ 1 + 2*y := by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    calc
      _ ≤ 3 + ‖1-2*y‖ := add_le_add_left
        (mul_le_of_le_one_left (norm_nonneg _) (by rwa [Real.norm_eq_abs])) _
      _ ≤ _ := by linarith
  rw [chordLinearIntegrand, norm_mul, norm_mul, Real.norm_of_nonneg (exp_pos _).le,
    Real.norm_of_nonneg h₀]
  calc
    _ ≤ (exp (-y) * (y/(x+y))) * (4+2*y) :=
      mul_le_mul_of_nonneg_left h₃ (by positivity)
    _ ≤ exp (-y) * (4+2*y) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (by positivity) h₁) (exp_pos _).le
    _ = _ := by simp only [UV.RelativeSoft.expMonomial, one_mul, pow_zero, pow_one]; ring

theorem chord_linear_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (chordLinearIntegrand x) (Ioi 0) := by
  have h := ((UV.RelativeSoft.exp_monomial_integrable one_pos 0).const_mul 4).add
    ((UV.RelativeSoft.exp_monomial_integrable one_pos 1).const_mul 2)
  refine h.mono' (by unfold chordLinearIntegrand; fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact chord_linear_norm_le hx hy.le

private def chordContactPrimitive (x y : ℝ) : ℝ :=
  2 * (y^2 * (x-y)/(x+y)^2) * exp (-y)

private theorem chord_contact_primitive_deriv {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    HasDerivAt (chordContactPrimitive x) (chordLinearIntegrand x y - chordBIntegrand x y) y := by
  have hp : 0 < x+y := by positivity
  let hy₀ := hasDerivAt_id y
  have h₁ := (hy₀.pow 2).mul ((hasDerivAt_const y x).sub hy₀)
  have h₂ := ((hasDerivAt_const y x).add hy₀).pow 2
  have h₃ := (h₁.div h₂ (pow_ne_zero _ hp.ne')).const_mul 2
  have h₄ := hy₀.neg.exp
  convert h₃.mul h₄ using 1
  norm_num [chordLinearIntegrand, chordBIntegrand, id_eq, Pi.pow_apply, Pi.sub_apply,
    Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.neg_apply]
  field_simp
  ring

private theorem chord_contact_primitive_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (chordContactPrimitive x) atTop (𝓝 0) := by
  have hlim := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul (2 : ℝ)
  rw [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  obtain ⟨h₀, h₁, h₂⟩ := chord_radial_ratios hx hy
  have heq : chordContactPrimitive x y =
      (2 * y * exp (-y)) * (y/(x+y)) * ((x-y)/(x+y)) := by
    unfold chordContactPrimitive
    field_simp
  rw [heq, norm_mul, norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * y * exp (-y)),
    Real.norm_of_nonneg h₀, Real.norm_eq_abs, pow_one]
  apply (mul_le_of_le_one_right (by positivity) h₂).trans
  rw [← mul_assoc]
  exact mul_le_of_le_one_right (by positivity) h₁

/-- The two boundary terms vanish at \(y=0\) and at infinity. -/
theorem chord_b_eq_integral_linear {x : ℝ} (hx : 0 < x) :
    chordB x = ∫ y in Ioi (0 : ℝ), chordLinearIntegrand x y := by
  have hi := (chord_linear_integrable hx).sub (chord_b_integrable hx)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun y hy => chord_contact_primitive_deriv hx (show 0 ≤ y from hy))
    hi (chord_contact_primitive_tendsto hx)
  rw [integral_sub (chord_linear_integrable hx) (chord_b_integrable hx)] at h
  simp [chordContactPrimitive] at h
  exact (sub_eq_zero.mp h).symm

/-- The radial Hessian keeps the entire interaction multiplier on each
induced vertex. In particular, a single two-mark contact carries one c. -/
def chordNormalizedRadialIntegrand (x c y : ℝ) : ℝ :=
  let a := UV.RelativeSoft.tangentialChord y
  let b := UV.RelativeSoft.radialChord y
  y / (x + y) * (3 * ((c*a)^2 - c*a) + (x-y)/(x+y) * ((c*b)^2 - c*b))

theorem chord_normalized_radial_integrand_split {x c y : ℝ} (hxy : x+y ≠ 0) :
    chordNormalizedRadialIntegrand x c y =
      c^2 * chordAIntegrand x y - c * chordLinearIntegrand x y := by
  unfold chordNormalizedRadialIntegrand chordAIntegrand chordLinearIntegrand
    UV.RelativeSoft.tangentialChord UV.RelativeSoft.radialChord
  rw [show exp (-(2*y)) = exp (-y)^2 by rw [pow_two, ← exp_add]; congr 1; ring]
  field_simp
  ring

theorem chord_normalized_radial_integral {x : ℝ} (hx : 0 < x) (c : ℝ) :
    (∫ y in Ioi (0 : ℝ), chordNormalizedRadialIntegrand x c y) =
      c^2 * chordA x - c * chordB x := by
  have heq : chordNormalizedRadialIntegrand x c =ᵐ[volume.restrict (Ioi 0)]
      fun y => c^2 * chordAIntegrand x y - c * chordLinearIntegrand x y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy' := show 0 < y from hy
    exact chord_normalized_radial_integrand_split (by positivity)
  rw [integral_congr_ae heq, integral_sub ((chord_a_integrable hx).const_mul _)
    ((chord_linear_integrable hx).const_mul _), integral_const_mul, integral_const_mul,
    chord_b_eq_integral_linear hx, chordA]

theorem chord_relative_shape_eq (s : ℝ) :
    chordNormalizedRadialIntegrand (s^2) 1 = UV.RelativeSoft.softShapeIntegrand s := by
  funext y
  simp [chordNormalizedRadialIntegrand, UV.RelativeSoft.softShapeIntegrand,
    UV.RelativeSoft.tangentialDifference, UV.RelativeSoft.radialDifference]

theorem chord_outside_response_eq_radial {m σ : ℝ} (hm : 0 < m) (hσ : 0 < σ) (e c : ℝ) :
    chordOutsideResponse e m σ c = e^2 / (16 * π^2 * σ^2) *
      (∫ y in Ioi (0 : ℝ), chordNormalizedRadialIntegrand (m^2 * σ^2) c y) := by
  rw [chord_normalized_radial_integral (by positivity)]
  unfold chordOutsideResponse
  ring

theorem chord_outside_response_one_eq_soft_shape {m σ : ℝ} (hm : 0 < m) (hσ : 0 < σ) (e : ℝ) :
    chordOutsideResponse e m σ 1 = e^2 / (16 * π^2 * σ^2) * UV.RelativeSoft.relativeSoftShape (m*σ) := by
  rw [chord_outside_response_eq_radial hm hσ, ← mul_pow]
  simp_rw [chord_relative_shape_eq]
  rfl

/-- Angular trace of the differentiated chord in the two-mark contact. -/
def chordContactTraceIntegrand (x y : ℝ) : ℝ :=
  exp (-y) * y^2 * (4*y - 12) / (x+y)

theorem chord_contact_trace_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (chordContactTraceIntegrand x) (Ioi 0) := by
  have hi := ((UV.RelativeSoft.exp_monomial_integrable one_pos 2).const_mul 4).add
    ((UV.RelativeSoft.exp_monomial_integrable one_pos 1).const_mul 12)
  have hmeas : Measurable (chordContactTraceIntegrand x) := by
    unfold chordContactTraceIntegrand
    fun_prop
  refine hi.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with y hy
  have hy' : 0 ≤ y := hy.le
  obtain ⟨h₀, h₁, _⟩ := chord_radial_ratios hx hy'
  have he : chordContactTraceIntegrand x y = (y/(x+y)) * (exp (-y) * y * (4*y-12)) := by
    unfold chordContactTraceIntegrand
    ring
  rw [he, norm_mul, Real.norm_of_nonneg h₀]
  calc
    _ ≤ ‖exp (-y) * y * (4*y-12)‖ := mul_le_of_le_one_left (norm_nonneg _) h₁
    _ ≤ exp (-y) * y * (4*y+12) := by
      rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ exp (-y) * y), Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [abs_le]
      constructor <;> linarith
    _ = _ := by simp only [Pi.add_apply, UV.RelativeSoft.expMonomial, one_mul, pow_one]; ring

private def chordContactTracePrimitive (x y : ℝ) : ℝ :=
  (-(4*y^3/(x+y)) + 4*y^3/(x+y)^2) * exp (-y)

private theorem chord_contact_trace_primitive_deriv {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    HasDerivAt (chordContactTracePrimitive x) (chordContactTraceIntegrand x y + chordBIntegrand x y) y := by
  have hs : 0 < x+y := by positivity
  let hk := hasDerivAt_id y
  have hp := (hasDerivAt_const y x).add hk
  have h₁ := ((hk.pow 3).div hp hs.ne').const_mul 4
  have h₂ := ((hk.pow 3).div (hp.pow 2) (pow_ne_zero _ hs.ne')).const_mul 4
  convert (h₁.neg.add h₂).mul hk.neg.exp using 1
  · funext z
    simp only [chordContactTracePrimitive, Pi.pow_apply, Pi.mul_apply, Pi.div_apply,
      Pi.add_apply, Pi.neg_apply, id_eq]
    ring
  · norm_num [chordContactTraceIntegrand, chordBIntegrand, id_eq, Pi.pow_apply, Pi.sub_apply,
      Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.neg_apply]
    field_simp
    ring

private theorem chord_contact_trace_primitive_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (chordContactTracePrimitive x) atTop (𝓝 0) := by
  have h₂ := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul (4 : ℝ)
  have h₁ := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul (4 : ℝ)
  rw [mul_zero] at h₂ h₁
  have hlim := h₂.add h₁
  rw [add_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  obtain ⟨hv₀, hv₁, _⟩ := chord_radial_ratios hx hy
  let v := y/(x+y)
  have he : chordContactTracePrimitive x y =
    -(4 * (y^2 * exp (-y)) * v) + 4 * (y * exp (-y)) * v^2 := by
    unfold chordContactTracePrimitive v
    field_simp
  rw [he, pow_one]
  apply (norm_add_le _ _).trans
  rw [norm_neg, norm_mul (4 * (y^2 * exp (-y))), norm_mul (4 * (y * exp (-y))),
    Real.norm_of_nonneg (by positivity : 0 ≤ 4 * (y^2 * exp (-y))),
    Real.norm_of_nonneg (by positivity : 0 ≤ 4 * (y * exp (-y))),
    Real.norm_of_nonneg hv₀, Real.norm_of_nonneg (sq_nonneg v)]
  exact add_le_add (mul_le_of_le_one_right (by positivity) hv₁)
    (mul_le_of_le_one_right (by positivity) ((sq_le_sq₀ hv₀ zero_le_one).mpr hv₁ |>.trans_eq (one_pow 2)))

/-- The angular contact trace integrates to the signed linear coefficient. -/
theorem chord_contact_trace_integral {x : ℝ} (hx : 0 < x) :
    (∫ y in Ioi (0 : ℝ), chordContactTraceIntegrand x y) = -chordB x := by
  have hi := (chord_contact_trace_integrable hx).add (chord_b_integrable hx)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun y hy => chord_contact_trace_primitive_deriv hx (show 0 ≤ y from hy))
    hi (chord_contact_trace_primitive_tendsto hx)
  rw [integral_add (chord_contact_trace_integrable hx) (chord_b_integrable hx)] at h
  simp [chordContactTracePrimitive] at h
  exact eq_neg_of_add_eq_zero_left h

end UV.SectorPlane
