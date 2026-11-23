import UV.ContinueRelativeCharge
import UV.ContinueRelativeSoftShape
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Charge normalization of the literal relative Wilson source.
Outside the phase a two-mark contact is linear in the interaction
multiplier, whereas the two one-mark vertices are quadratic. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Set Real

def chordAIntegrand (x y : ℝ) : ℝ :=
  y * exp (-(2 * y)) * (3 / (x + y) + (x - y) * (1 - 2 * y)^2 / (x + y)^2)

def chordBIntegrand (x y : ℝ) : ℝ :=
  4 * exp (-y) * (y^2 * (3 * x + y) / (x + y)^3)

def chordA (x : ℝ) := ∫ y in Ioi (0 : ℝ), chordAIntegrand x y

def chordB (x : ℝ) := ∫ y in Ioi (0 : ℝ), chordBIntegrand x y

private def chordAMajorant (y : ℝ) : ℝ :=
  exp (-(2 * y)) * (3 + (1 - 2 * y)^2)

private theorem chord_a_majorant_eq (y : ℝ) :
    chordAMajorant y = 4 * UV.RelativeSoft.expMonomial 2 0 y -
      4 * UV.RelativeSoft.expMonomial 2 1 y + 4 * UV.RelativeSoft.expMonomial 2 2 y := by
  simp only [chordAMajorant, UV.RelativeSoft.expMonomial, pow_zero, one_mul, pow_one]
  ring

private theorem chord_a_majorant_integrable : IntegrableOn chordAMajorant (Ioi (0 : ℝ)) := by
  rw [show chordAMajorant = _ from funext chord_a_majorant_eq]
  exact (((UV.RelativeSoft.exp_monomial_integrable two_pos 0).const_mul 4).sub
    ((UV.RelativeSoft.exp_monomial_integrable two_pos 1).const_mul 4)).add
    ((UV.RelativeSoft.exp_monomial_integrable two_pos 2).const_mul 4)

private theorem chord_a_majorant_integral : (∫ y in Ioi (0 : ℝ), chordAMajorant y) = 2 := by
  let f (n : ℕ) (y : ℝ) := 4 * UV.RelativeSoft.expMonomial 2 n y
  have h (n : ℕ) : IntegrableOn (f n) (Ioi (0 : ℝ)) :=
    (UV.RelativeSoft.exp_monomial_integrable two_pos n).const_mul 4
  rw [show chordAMajorant = _ from funext chord_a_majorant_eq]
  change (∫ y in Ioi (0 : ℝ), (f 0 - f 1) y + f 2 y) = 2
  rw [integral_add ((h 0).sub (h 1)) (h 2)]
  simp only [Pi.sub_apply, integral_sub (h 0) (h 1)]
  norm_num [f, integral_const_mul, UV.RelativeSoft.exp_monomial_integral two_pos]

private theorem chord_a_integrand_norm_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ‖chordAIntegrand x y‖ ≤ chordAMajorant y := by
  have hs : 0 < x + y := by positivity
  have h₁ : y / (x + y) ≤ 1 := (div_le_one₀ hs).mpr (by linarith)
  have h₂ : |(x - y) / (x + y)| ≤ 1 := by
    rw [abs_div, abs_of_pos hs, div_le_one₀ hs, abs_le]
    constructor <;> linarith
  have heq : chordAIntegrand x y = exp (-(2 * y)) * (y / (x + y)) *
      (3 + ((x - y) / (x + y)) * (1 - 2 * y)^2) := by
    unfold chordAIntegrand
    field_simp
  rw [heq, norm_mul, norm_mul, Real.norm_of_nonneg (exp_pos _).le,
    Real.norm_of_nonneg (div_nonneg hy.le hs.le), chordAMajorant]
  have h₃ : ‖3 + (x - y) / (x + y) * (1 - 2 * y)^2‖ ≤ 3 + (1 - 2 * y)^2 := by
    apply (norm_add_le _ _).trans
    rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
      Real.norm_of_nonneg (sq_nonneg _)]
    exact add_le_add_left (mul_le_of_le_one_left (sq_nonneg _) (by rwa [Real.norm_eq_abs])) _
  calc
    _ ≤ (exp (-(2 * y)) * (y / (x + y))) * (3 + (1 - 2 * y)^2) :=
      mul_le_mul_of_nonneg_left h₃ (by positivity)
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (by positivity) h₁) (exp_pos _).le

theorem chord_a_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (chordAIntegrand x) (Ioi 0) := by
  refine chord_a_majorant_integrable.mono' (by unfold chordAIntegrand; fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact chord_a_integrand_norm_le hx hy

theorem chord_a_le_two {x : ℝ} (hx : 0 < x) : chordA x ≤ 2 := by
  rw [← chord_a_majorant_integral]
  refine integral_mono_ae (chord_a_integrable hx) chord_a_majorant_integrable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact (le_norm_self _).trans (chord_a_integrand_norm_le hx hy)

theorem chord_a_norm_le_two {x : ℝ} (hx : 0 < x) : ‖chordA x‖ ≤ 2 := by
  rw [← chord_a_majorant_integral]
  refine (norm_integral_le_integral_norm _).trans
    (integral_mono_ae (chord_a_integrable hx).norm chord_a_majorant_integrable ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact chord_a_integrand_norm_le hx hy

private theorem chord_b_integrand_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    let v := y / (x + y)
    chordBIntegrand x y = 4 * exp (-y) * (v^2 * (3 - 2 * v)) := by
  have hs : 0 < x + y := by positivity
  dsimp [chordBIntegrand]
  field_simp
  ring

private theorem chord_b_integrand_nonneg_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 ≤ chordBIntegrand x y ∧ chordBIntegrand x y ≤ 4 * exp (-y) := by
  let v := y / (x + y)
  have hs : 0 < x + y := by positivity
  have hv₀ : 0 ≤ v := div_nonneg hy.le hs.le
  have hv₁ : v ≤ 1 := (div_le_one₀ hs).mpr (by linarith)
  rw [chord_b_integrand_eq hx hy]
  change 0 ≤ 4 * exp (-y) * (v^2 * (3 - 2*v)) ∧
    4 * exp (-y) * (v^2 * (3 - 2*v)) ≤ 4 * exp (-y)
  have hpos : 0 ≤ 3 - 2*v := by linarith
  refine ⟨by positivity, mul_le_of_le_one_right (by positivity) ?_⟩
  have h := mul_nonneg (sq_nonneg (1-v)) (show 0 ≤ 1+2*v by positivity)
  nlinarith only [h]

theorem chord_b_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (chordBIntegrand x) (Ioi 0) := by
  refine ((integrableOn_exp_neg_Ioi 0).const_mul 4).mono'
    (by unfold chordBIntegrand; fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  obtain ⟨h₀, h₁⟩ := chord_b_integrand_nonneg_le hx hy
  simpa only [Real.norm_of_nonneg h₀] using h₁

theorem chord_b_norm_le_four {x : ℝ} (hx : 0 < x) : ‖chordB x‖ ≤ 4 := by
  have h := (integrableOn_exp_neg_Ioi 0).const_mul 4
  have he : (∫ y in Ioi (0 : ℝ), 4 * exp (-y)) = 4 := by
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  rw [← he]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_ae (chord_b_integrable hx).norm h ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  obtain ⟨h₀, h₁⟩ := chord_b_integrand_nonneg_le hx hy
  simpa only [Real.norm_of_nonneg h₀] using h₁

theorem two_exp_neg_le_chord_b {x : ℝ} (hx : 0 < x) : 2 * exp (-x) ≤ chordB x := by
  have hsub : Ioi x ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi hx.le
  have hb := chord_b_integrable hx
  rw [← integral_exp_neg_Ioi x, ← integral_const_mul]
  refine le_trans (integral_mono_ae ((integrableOn_exp_neg_Ioi x).const_mul 2)
    (hb.mono_set hsub) ?_) (setIntegral_mono_set hb ?_ (Filter.Eventually.of_forall (fun _ hy => hsub hy)))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy' : 0 < y := hsub hy
    rw [chord_b_integrand_eq hx hy']
    let v := y / (x + y)
    have hs : 0 < x + y := by positivity
    have hv₀ : 1 / 2 ≤ v := (le_div_iff₀ hs).mpr (by linarith [show x < y from hy])
    have hv₁ : v ≤ 1 := (div_le_one₀ hs).mpr (by linarith)
    have h₀ : 0 ≤ 2 * v * (1-v) :=
      mul_nonneg (mul_nonneg zero_le_two (by linarith)) (sub_nonneg.mpr hv₁)
    have h := mul_nonneg (sub_nonneg.mpr hv₀) (show 0 ≤ 1 + 2*v*(1-v) by linarith)
    have h₁ : 1 / 2 ≤ v^2*(3-2*v) := by nlinarith only [h]
    calc
      _ = (4 * exp (-y)) * (1 / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h₁ (by positivity)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (chord_b_integrand_nonneg_le hx hy).1

def chordOutsideScale (x : ℝ) : ℝ := (chordChargeFactor x)⁻¹

theorem chord_outside_scale_pos {x : ℝ} (hx : 0 ≤ x) : 0 < chordOutsideScale x :=
  inv_pos.mpr (chord_charge_factor_pos hx)

theorem chord_outside_scale_lt_exp_neg {x : ℝ} (hx : 0 < x) :
    chordOutsideScale x < exp (-x) := by
  rw [chordOutsideScale, exp_neg, chordChargeFactor]
  have h : 1 < 1 + 2 * x := by linarith
  exact (inv_lt_inv₀ (by positivity) (exp_pos _)).mpr (lt_mul_of_one_lt_right (exp_pos _) h)

theorem chord_outside_normalized_charge (e x : ℝ) (hx : 0 ≤ x) :
    e * chordOutsideScale x * chordChargeFactor x = e := by
  rw [mul_assoc, chordOutsideScale, inv_mul_cancel₀ (chord_charge_factor_pos hx).ne', mul_one]

def chordOutsideResponse (e m σ c : ℝ) : ℝ :=
  let x := m ^ 2 * σ ^ 2
  e^2 * c / (16 * π^2 * σ^2) * (c * chordA x - chordB x)

theorem chord_outside_normalized_response_neg {e m σ : ℝ}
    (he : e ≠ 0) (hm : 0 < m) (hσ : 0 < σ) :
    chordOutsideResponse e m σ (chordOutsideScale (m ^ 2 * σ ^ 2)) < 0 := by
  let x := m^2 * σ^2
  have hx : 0 < x := by dsimp [x]; positivity
  have hc := chord_outside_scale_pos hx.le
  have hA := mul_le_mul_of_nonneg_left (chord_a_le_two hx) hc.le
  have hB := two_exp_neg_le_chord_b hx
  have hlt := chord_outside_scale_lt_exp_neg hx
  have hp : 0 < e^2 * chordOutsideScale x / (16 * π^2 * σ^2) := by positivity
  exact mul_neg_of_pos_of_neg hp (by linarith)

/-- Using one multiplier in the phase rescales both terms equally. -/
theorem chord_phase_response_scale (e m σ z : ℝ) :
    chordOutsideResponse (e * z) m σ 1 = z ^ 2 * chordOutsideResponse e m σ 1 := by
  unfold chordOutsideResponse
  ring

section DepthLaw

variable {D : Type*} [MeasurableSpace D]

theorem chord_outside_normalized_average_neg (ν : Measure D) [IsProbabilityMeasure ν]
    (σ : D → ℝ) (m e : ℝ) (hm : 0 < m) (he : e ≠ 0) (hσ : ∀ᵐ r ∂ν, 0 < σ r)
    (hi : Integrable
      (fun r => chordOutsideResponse e m (σ r) (chordOutsideScale (m ^ 2 * σ r ^ 2))) ν) :
    (∫ r, chordOutsideResponse e m (σ r) (chordOutsideScale (m ^ 2 * σ r ^ 2)) ∂ν) < 0 := by
  let R (r : D) := chordOutsideResponse e m (σ r) (chordOutsideScale (m ^ 2 * σ r ^ 2))
  have hneg : ∀ᵐ r ∂ν, R r < 0 := by
    filter_upwards [hσ] with r hr
    exact chord_outside_normalized_response_neg he hm hr
  have hs : Function.support (fun r => -R r) =ᵐ[ν] (Set.univ : Set D) := by
    filter_upwards [hneg] with r hr
    apply propext
    change -(R r) ≠ 0 ↔ True
    exact iff_true_intro (neg_ne_zero.mpr hr.ne)
  have hn : 0 ≤ᵐ[ν] fun r => -R r := hneg.mono (fun _ hr => neg_nonneg.mpr hr.le)
  have hp := (integral_pos_iff_support_of_nonneg_ae hn hi.neg).mpr
    (show 0 < ν (Function.support fun r => -R r) by rw [measure_congr hs, measure_univ]; exact zero_lt_one)
  rw [integral_neg] at hp
  exact neg_pos.mp hp

/-- The common depth average with one shared free rest projector. -/
def chordDepthChargeFactor (ν : Measure D) (σ : D → ℝ) (m : ℝ) : ℝ :=
  ∫ r, chordChargeFactor (m ^ 2 * σ r ^ 2) ∂ν

def chordInsidePhaseScale (ν : Measure D) (σ : D → ℝ) (m : ℝ) : ℝ :=
  (chordDepthChargeFactor ν σ m)⁻¹

theorem chord_charge_factor_mono_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    chordChargeFactor x ≤ chordChargeFactor y := by
  unfold chordChargeFactor
  exact mul_le_mul (exp_le_exp.mpr hxy) (by linarith) (by positivity) (exp_pos _).le

theorem chord_depth_charge_integrable (ν : Measure D) [IsFiniteMeasure ν]
    (σ : D → ℝ) (m M : ℝ) (hσ : AEMeasurable σ ν) (hM : ∀ᵐ r ∂ν, |σ r| ≤ M) :
    Integrable (fun r => chordChargeFactor (m ^ 2 * σ r ^ 2)) ν := by
  refine (integrable_const (chordChargeFactor (m ^ 2 * M ^ 2))).mono' ?_ ?_
  · have hc : Continuous chordChargeFactor := by
      unfold chordChargeFactor
      fun_prop
    have hwidth : AEMeasurable (fun r => m ^ 2 * σ r ^ 2) ν :=
      aemeasurable_const.mul (hσ.pow_const 2)
    exact (hc.measurable.comp_aemeasurable hwidth).aestronglyMeasurable
  · filter_upwards [hM] with r hr
    have h₀ : 0 ≤ m ^ 2 * σ r ^ 2 := by positivity
    rw [Real.norm_of_nonneg (chord_charge_factor_pos h₀).le]
    apply chord_charge_factor_mono_nonneg h₀
    exact mul_le_mul_of_nonneg_left (sq_le_sq.mpr (hr.trans (le_abs_self M))) (sq_nonneg m)

theorem chord_depth_charge_factor_one_le (ν : Measure D) [IsProbabilityMeasure ν]
    (σ : D → ℝ) (m : ℝ) (hi : Integrable (fun r => chordChargeFactor (m ^ 2 * σ r ^ 2)) ν) :
    1 ≤ chordDepthChargeFactor ν σ m := by
  calc
    1 = ∫ _ : D, (1 : ℝ) ∂ν := by simp
    _ ≤ _ := integral_mono (integrable_const _) hi fun r => by
      simpa [chordChargeFactor] using
        (chord_charge_factor_mono_nonneg (x := 0) (y := m ^ 2 * σ r ^ 2) le_rfl (by positivity))

theorem chord_inside_phase_scale_pos (ν : Measure D) [IsProbabilityMeasure ν]
    (σ : D → ℝ) (m : ℝ) (hi : Integrable (fun r => chordChargeFactor (m ^ 2 * σ r ^ 2)) ν) :
    0 < chordInsidePhaseScale ν σ m :=
  inv_pos.mpr (zero_lt_one.trans_le (chord_depth_charge_factor_one_le ν σ m hi))

/-- The transverse phase uses e·z_m. The one-mark response averages
linearly at the common unperturbed charged pole. -/
theorem chord_inside_phase_normalized_charge (ν : Measure D) [IsProbabilityMeasure ν]
    (σ : D → ℝ) (m e : ℝ) (hi : Integrable (fun r => chordChargeFactor (m ^ 2 * σ r ^ 2)) ν) :
    (∫ r, (e * chordInsidePhaseScale ν σ m) * chordChargeFactor (m ^ 2 * σ r ^ 2) ∂ν) = e := by
  have hpos := zero_lt_one.trans_le (chord_depth_charge_factor_one_le ν σ m hi)
  rw [integral_const_mul]
  change (e * (chordDepthChargeFactor ν σ m)⁻¹) * chordDepthChargeFactor ν σ m = e
  rw [mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one]

/-- Both quadratic terms scale as z_m² when the scalar is inside the
transverse phase. This preserves precisely the averaged matching roots. -/
theorem chord_inside_phase_matching_iff (ν : Measure D) [IsProbabilityMeasure ν]
    (σ : D → ℝ) (m : ℝ) (hi : Integrable (fun r => chordChargeFactor (m ^ 2 * σ r ^ 2)) ν)
    (H : D → ℝ) :
    (∫ r, chordInsidePhaseScale ν σ m ^ 2 * H r ∂ν) = 0 ↔ (∫ r, H r ∂ν) = 0 := by
  rw [integral_const_mul]
  have hz := pow_ne_zero 2 (chord_inside_phase_scale_pos ν σ m hi).ne'
  exact ⟨fun h => (mul_eq_zero.mp h).resolve_left hz, fun h => by rw [h, mul_zero]⟩

end DepthLaw

end UV.SectorPlane
