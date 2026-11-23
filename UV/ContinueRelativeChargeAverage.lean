import UV.ContinueRelativeChargeNormalization
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-! A single outside interaction multiplier chosen to normalize the
depth-averaged tree charge still gives a negative soft Hessian. -/

noncomputable section

open Filter MeasureTheory Set Real

namespace UV.SectorPlane

section DepthLaw

variable {D : Type*} [MeasurableSpace D] (ν : Measure D) [IsProbabilityMeasure ν]

private theorem integral_pos_of_ae_pos {f : D → ℝ} (hi : Integrable f ν)
    (h : ∀ᵐ r ∂ν, 0 < f r) : 0 < ∫ r, f r ∂ν := by
  have he : Function.support f =ᵐ[ν] (univ : Set D) := by
    filter_upwards [h] with r hr
    apply propext
    change f r ≠ 0 ↔ True
    exact iff_true_intro hr.ne'
  exact (integral_pos_iff_support_of_nonneg_ae (h.mono fun _ hr => hr.le) hi).mpr
    (by rw [measure_congr he, measure_univ]; exact zero_lt_one)

/-- Product-law covariance of functions whose differences have the same sign. -/
private theorem integral_product_le_of_same_order {w f : D → ℝ}
    (hw : Integrable w ν) (hf : Integrable f ν)
    (hprod : Integrable (fun r => w r * f r) ν)
    (h : ∀ᵐ p ∂ν.prod ν, 0 ≤ (w p.1 - w p.2) * (f p.1 - f p.2)) :
    (∫ r, w r ∂ν) * (∫ r, f r ∂ν) ≤ ∫ r, w r * f r ∂ν := by
  let L (p : D × D) := w p.1 * f p.2 + f p.1 * w p.2
  let R (p : D × D) := w p.1 * f p.1 + w p.2 * f p.2
  have hL : Integrable L (ν.prod ν) := (hw.mul_prod hf).add (hf.mul_prod hw)
  have hR₁ := hprod.comp_fst ν
  have hR₂ := hprod.comp_snd ν
  have hR : Integrable R (ν.prod ν) := hR₁.add hR₂
  have hle := integral_mono_ae hL hR (h.mono fun p hp => by
    dsimp [L, R]
    nlinarith only [hp])
  rw [show (∫ p, L p ∂(ν.prod ν)) =
    (∫ r, w r ∂ν) * (∫ r, f r ∂ν) + (∫ r, f r ∂ν) * (∫ r, w r ∂ν) by
      unfold L
      rw [integral_add (hw.mul_prod hf) (hf.mul_prod hw), integral_prod_mul, integral_prod_mul]] at hle
  rw [show (∫ p, R p ∂(ν.prod ν)) = 2 * (∫ r, w r * f r ∂ν) by
      unfold R
      rw [integral_add hR₁ hR₂, integral_prod _ hR₁, integral_prod _ hR₂]
      simp [two_mul]] at hle
  rw [mul_comm (∫ r, f r ∂ν), ← two_mul] at hle
  linarith

private theorem width_covariance {σ : D → ℝ} {m : ℝ}
    (hσ : ∀ᵐ r ∂ν, 0 < σ r)
    (hw : Integrable (fun r => (σ r ^ 2)⁻¹) ν)
    (hf : Integrable (fun r => exp (-(m ^ 2 * σ r ^ 2))) ν)
    (hprod : Integrable (fun r => (σ r ^ 2)⁻¹ * exp (-(m ^ 2 * σ r ^ 2))) ν) :
    (∫ r, (σ r ^ 2)⁻¹ ∂ν) * (∫ r, exp (-(m ^ 2 * σ r ^ 2)) ∂ν) ≤
      ∫ r, (σ r ^ 2)⁻¹ * exp (-(m ^ 2 * σ r ^ 2)) ∂ν := by
  refine integral_product_le_of_same_order ν hw hf hprod ?_
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := ν) (ν := ν)).ae hσ,
    (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := ν)).ae hσ] with p hp hq
  have hpair {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
      (b ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ ∧ exp (-(m ^ 2 * b ^ 2)) ≤ exp (-(m ^ 2 * a ^ 2)) := by
    have hs := (sq_le_sq₀ ha.le (ha.le.trans hab)).mpr hab
    exact ⟨inv_anti₀ (sq_pos_of_pos ha) hs,
      exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hs (sq_nonneg m)))⟩
  rcases le_total (σ p.1) (σ p.2) with h | h
  · obtain ⟨h₁, h₂⟩ := hpair hp h
    exact mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr h₂)
  · obtain ⟨h₁, h₂⟩ := hpair hq h
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h₁) (sub_nonpos.mpr h₂)

private theorem width_linear_forms {σ : D → ℝ} {m : ℝ}
    (hm : 0 < m) (hσ : AEMeasurable σ ν) (hpositive : ∀ᵐ r ∂ν, 0 < σ r)
    (hg : Integrable (fun r => chordChargeFactor (m ^ 2 * σ r ^ 2)) ν) :
    Integrable (fun r => exp (-(m ^ 2 * σ r ^ 2))) ν ∧
      chordInsidePhaseScale ν σ m < ∫ r, exp (-(m ^ 2 * σ r ^ 2)) ∂ν := by
  let x (r : D) := m ^ 2 * σ r ^ 2
  have hx : AEMeasurable x ν := aemeasurable_const.mul (hσ.pow_const 2)
  have hx₀ (r : D) : 0 ≤ x r := by dsimp [x]; positivity
  have hxp : ∀ᵐ r ∂ν, 0 < x r := by
    filter_upwards [hpositive] with r hr
    dsimp [x]
    positivity
  have hge (r : D) : exp (x r) ≤ chordChargeFactor (x r) := by
    rw [chordChargeFactor]
    exact le_mul_of_one_le_right (exp_pos _).le (by linarith [hx₀ r])
  have hplus : Integrable (fun r => exp (x r)) ν := by
    refine hg.mono' (continuous_exp.measurable.comp_aemeasurable hx).aestronglyMeasurable ?_
    exact Eventually.of_forall fun r => by
      simpa only [Real.norm_of_nonneg (exp_pos _).le] using hge r
  have hminus : Integrable (fun r => exp (-x r)) ν := by
    refine (integrable_const (1 : ℝ)).mono'
      (continuous_exp.measurable.comp_aemeasurable hx.neg).aestronglyMeasurable ?_
    exact Eventually.of_forall fun r => by
      rw [Real.norm_of_nonneg (exp_pos _).le]
      exact exp_le_one_iff.mpr (neg_nonpos.mpr (hx₀ r))
  have hxi : Integrable x ν := by
    refine hplus.mono' hx.aestronglyMeasurable (Eventually.of_forall fun r => ?_)
    rw [Real.norm_of_nonneg (hx₀ r)]
    linarith [add_one_le_exp (x r)]
  have hp := convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall fun _ => mem_univ _) hxi hplus
  have hn := convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall fun _ => mem_univ _) hxi.neg hminus
  change exp (∫ r, -x r ∂ν) ≤ ∫ r, exp (-x r) ∂ν at hn
  rw [integral_neg] at hn
  have hbound := mul_le_mul hn hp (exp_pos _).le
    ((exp_pos _).le.trans hn)
  rw [← exp_add, neg_add_cancel, exp_zero] at hbound
  have hstrict : (∫ r, exp (x r) ∂ν) < chordDepthChargeFactor ν σ m := by
    have hd := integral_pos_of_ae_pos ν (hg.sub hplus) (by
      filter_upwards [hxp] with r hr
      change 0 < chordChargeFactor (x r) - exp (x r)
      unfold chordChargeFactor
      exact sub_pos.mpr (lt_mul_of_one_lt_right (exp_pos _) (by linarith)))
    change 0 < ∫ r, chordChargeFactor (m ^ 2 * σ r ^ 2) - exp (x r) ∂ν at hd
    rwa [integral_sub hg hplus, sub_pos] at hd
  have hne := integral_pos_of_ae_pos ν hminus (Eventually.of_forall fun _ => exp_pos _)
  have hE := zero_lt_one.trans_le (chord_depth_charge_factor_one_le ν σ m hg)
  refine ⟨hminus, ?_⟩
  rw [chordInsidePhaseScale, ← one_div, div_lt_iff₀ hE]
  exact hbound.trans_lt (mul_lt_mul_of_pos_left hstrict hne)

private theorem measurable_chord_a : Measurable chordA := by
  have hm : Measurable (fun p : ℝ × ℝ => chordAIntegrand p.1 p.2) := by
    unfold chordAIntegrand
    fun_prop
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi 0))).measurable

private theorem measurable_chord_b : Measurable chordB := by
  have hm : Measurable (fun p : ℝ × ℝ => chordBIntegrand p.1 p.2) := by
    unfold chordBIntegrand
    fun_prop
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi 0))).measurable

/-- A single multiplier outside the interaction fixes the averaged
tree charge and still forces a strictly negative averaged response. -/
theorem chord_single_outside_average_neg (σ : D → ℝ) (m e M : ℝ)
    (hm : 0 < m) (he : e ≠ 0) (hσ : AEMeasurable σ ν) (hpositive : ∀ᵐ r ∂ν, 0 < σ r)
    (hM : ∀ᵐ r ∂ν, |σ r| ≤ M) (hw : Integrable (fun r => (σ r ^ 2)⁻¹) ν) :
    (∫ r, chordOutsideResponse e m (σ r) (chordInsidePhaseScale ν σ m) ∂ν) < 0 := by
  let x (r : D) := m ^ 2 * σ r ^ 2
  let w (r : D) := (σ r ^ 2)⁻¹
  let f (r : D) := exp (-x r)
  let c := chordInsidePhaseScale ν σ m
  have hx : AEMeasurable x ν := aemeasurable_const.mul (hσ.pow_const 2)
  have hx₀ (r : D) : 0 ≤ x r := by dsimp [x]; positivity
  have hxp : ∀ᵐ r ∂ν, 0 < x r := by
    filter_upwards [hpositive] with r hr
    dsimp [x]
    positivity
  have hw₀ (r : D) : 0 ≤ w r := by dsimp [w]; positivity
  have hg := chord_depth_charge_integrable ν σ m M hσ hM
  have hc := chord_inside_phase_scale_pos ν σ m hg
  obtain ⟨hf, hcf⟩ := width_linear_forms ν hm hσ hpositive hg
  have huw : Integrable (fun r => w r * f r) ν := by
    refine hw.mono' (hw.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
    exact Eventually.of_forall fun r => by
      rw [Real.norm_of_nonneg (mul_nonneg (hw₀ r) (exp_pos _).le)]
      exact mul_le_of_le_one_right (hw₀ r) (exp_le_one_iff.mpr (neg_nonpos.mpr (hx₀ r)))
  have hWA : Integrable (fun r => w r * chordA (x r)) ν := by
    refine (hw.const_mul 2).mono'
      (hw.aestronglyMeasurable.mul (measurable_chord_a.comp_aemeasurable hx).aestronglyMeasurable) ?_
    filter_upwards [hxp] with r hr
    rw [norm_mul, Real.norm_of_nonneg (hw₀ r), mul_comm (2 : ℝ)]
    exact mul_le_mul_of_nonneg_left (chord_a_norm_le_two hr) (hw₀ r)
  have hWB : Integrable (fun r => w r * chordB (x r)) ν := by
    refine (hw.const_mul 4).mono'
      (hw.aestronglyMeasurable.mul (measurable_chord_b.comp_aemeasurable hx).aestronglyMeasurable) ?_
    filter_upwards [hxp] with r hr
    rw [norm_mul, Real.norm_of_nonneg (hw₀ r), mul_comm (4 : ℝ)]
    exact mul_le_mul_of_nonneg_left (chord_b_norm_le_four hr) (hw₀ r)
  have hE : 0 < ∫ r, w r ∂ν := by
    refine integral_pos_of_ae_pos ν hw ?_
    filter_upwards [hpositive] with r hr
    dsimp [w]
    positivity
  have hB : 2 * (∫ r, w r * f r ∂ν) ≤ ∫ r, w r * chordB (x r) ∂ν := by
    rw [← integral_const_mul]
    refine integral_mono_ae (huw.const_mul 2) hWB ?_
    filter_upwards [hxp] with r hr
    have h := mul_le_mul_of_nonneg_left (two_exp_neg_le_chord_b hr) (hw₀ r)
    dsimp only [f]
    linarith
  have hA : (∫ r, w r * chordA (x r) ∂ν) ≤ 2 * (∫ r, w r ∂ν) := by
    rw [← integral_const_mul]
    refine integral_mono_ae hWA (hw.const_mul 2) ?_
    filter_upwards [hxp] with r hr
    rw [mul_comm (2 : ℝ)]
    exact mul_le_mul_of_nonneg_left (chord_a_le_two hr) (hw₀ r)
  have hcov := width_covariance ν hpositive hw hf huw
  have hstrict : c * (∫ r, w r * chordA (x r) ∂ν) < ∫ r, w r * chordB (x r) ∂ν := by
    calc
      _ ≤ c * (2 * (∫ r, w r ∂ν)) := mul_le_mul_of_nonneg_left hA hc.le
      _ = 2 * ((∫ r, w r ∂ν) * c) := by ring
      _ < 2 * ((∫ r, w r ∂ν) * (∫ r, f r ∂ν)) := by
        exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hcf hE) two_pos
      _ ≤ 2 * (∫ r, w r * f r ∂ν) := mul_le_mul_of_nonneg_left hcov two_pos.le
      _ ≤ _ := hB
  have heq : (fun r => chordOutsideResponse e m (σ r) c) =
      fun r => (e ^ 2 * c / (16 * π ^ 2)) *
        (c * (w r * chordA (x r)) - w r * chordB (x r)) := by
    funext r
    unfold chordOutsideResponse w x
    ring
  rw [heq, integral_const_mul, integral_sub (hWA.const_mul c) hWB, integral_const_mul]
  exact mul_neg_of_pos_of_neg (by positivity) (sub_neg.mpr hstrict)

end DepthLaw

end UV.SectorPlane
