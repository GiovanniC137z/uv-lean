import UV.ContinueChargedWindingTime
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The zero winding controls the short-time magnetic coefficient on
the same oriented normal circle at every real holonomy. -/

noncomputable section
open Real MeasureTheory Set Filter
open scoped ENNReal
namespace UV.ExtendNativeHolonomy

variable {E : Type} [NormedAddCommGroup E]

private theorem winding_short_bound (C : NormalCircle E) {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1)
    (θ : ℝ) {w : ℤ} (hw : w ≠ 0) :
    ‖windingHeatReal C t θ w‖ ≤ (t/(C.length^2/8)) * exp (-(C.length^2/8)*(w:ℝ)^2) := by
  let a := C.length^2/8
  have ha : 0 < a := div_pos (sq_pos_of_pos C.length_pos) (by norm_num)
  have hw₁ : (1:ℝ) ≤ |(w:ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast (Int.add_one_le_iff.mpr (abs_pos.mpr hw) : (0:ℤ) + 1 ≤ |w|)
  have hw₂ : (1:ℝ) ≤ (w:ℝ)^2 := by rw [← sq_abs]; nlinarith
  have h₁ : a/t ≤ a*(w:ℝ)^2/t := by
    apply div_le_div_of_nonneg_right _ ht.le
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hw₂ ha.le
  have h₂ : a*(w:ℝ)^2 ≤ a*(w:ℝ)^2/t := by
    exact (le_div_iff₀ ht).2 (by nlinarith [mul_nonneg (mul_nonneg ha.le (sq_nonneg (w:ℝ))) (sub_nonneg.mpr ht₁)])
  have he : -(w:ℝ)^2*C.length^2/(4*t) ≤ -(a/t) + -a*(w:ℝ)^2 := by
    have hid : -(w:ℝ)^2*C.length^2/(4*t) = -2*(a*(w:ℝ)^2/t) := by dsimp [a]; ring
    rw [hid, neg_mul]
    linarith
  have hexp : exp (-(a/t)) ≤ t/a := by
    rw [exp_neg]
    apply (inv_le_iff_one_le_mul₀ (exp_pos _)).2
    have hx : a/t ≤ exp (a/t) := by linarith [add_one_le_exp (a/t)]
    calc
      1 = (t/a)*(a/t) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hx (div_nonneg ht.le ha.le)
  unfold windingHeatReal
  rw [norm_mul, Real.norm_of_nonneg (exp_nonneg _)]
  calc
    _ ≤ exp (-(w:ℝ)^2*C.length^2/(4*t)) * 1 :=
      mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact abs_cos_le_one _) (exp_nonneg _)
    _ ≤ _ := by
      rw [mul_one]
      apply (exp_le_exp.2 he).trans
      rw [exp_add]
      exact mul_le_mul_of_nonneg_right hexp (exp_nonneg _)

/-- The nonzero windings are uniformly small at short proper time, so
even destructive interference at a fixed holonomy leaves at least
one half of the zero-winding heat coefficient. -/
theorem normal_heatTrace_short_lower (C : NormalCircle E) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ θ t, 0 < t → t ≤ δ →
      C.length / (2 * sqrt (4*π*t)) ≤ normalHeatTrace C t θ := by
  let a := C.length^2/8
  have ha : 0 < a := by unfold a; exact div_pos (sq_pos_of_pos C.length_pos) (by norm_num)
  let g (w : ℤ) := exp (-(a*(w:ℝ)^2))
  have hg : Summable g := normalWinding_gaussian_summable ha
  have hn : ∀ w, 0 ≤ g w := fun _ => exp_nonneg _
  let K := (∑' w, g w) + 1
  have hK : 0 < K := by
    dsimp only [K]
    have h : (0:ℝ) ≤ ∑' w, g w := tsum_nonneg hn
    linarith
  refine ⟨min 1 (a/(2*K)),lt_min zero_lt_one (div_pos ha (by positivity)),min_le_left _ _,?_⟩
  intro θ t ht htδ
  let f (w : ℤ) := if w = 0 then 0 else windingHeatReal C t θ w
  have hfbound (w : ℤ) : ‖f w‖ ≤ (t/a)*g w := by
    by_cases hw : w = 0
    · simp only [f,hw,if_true,norm_zero]
      exact mul_nonneg (div_nonneg ht.le ha.le) (hn _)
    · simpa only [f,if_neg hw,g,neg_mul] using winding_short_bound C ht (htδ.trans (min_le_left _ _)) θ hw
  have hgs := hg.mul_left (t/a)
  have hf : Summable f := hgs.of_norm_bounded hfbound
  have habs : |∑' w, f w| ≤ (t/a)*K := by
    rw [← Real.norm_eq_abs]
    apply (norm_tsum_le_tsum_norm hf.norm).trans
    apply (hf.norm.tsum_le_tsum hfbound hgs).trans
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (div_nonneg ht.le ha.le)
  have hs : (t/a)*K ≤ 1/2 := by
    have ht' := (le_div_iff₀ (show 0 < 2*K by positivity)).1 (htδ.trans (min_le_right _ _))
    have h0 := (div_le_iff₀ ha).mpr (show t*K ≤ (1/2)*a by nlinarith)
    simpa only [mul_comm (t/a), ← mul_div_assoc, mul_comm K t] using h0
  have hsplit (w : ℤ) : windingHeatReal C t θ w = (if w = 0 then 1 else 0) + f w := by
    by_cases hw : w = 0 <;> simp [f,hw,windingHeatReal]
  rw [normal_heatTrace_real C ht θ]
  have h₀ : HasSum (fun w : ℤ => if w = 0 then (1:ℝ) else 0) 1 := hasSum_ite_eq 0 1
  simp_rw [hsplit]
  rw [h₀.summable.tsum_add hf, h₀.tsum_eq]
  have hhalf : (1/2:ℝ) ≤ 1 + ∑' w, f w := by
    have h := (abs_le.mp (habs.trans hs)).1
    linarith
  calc
    _ = (C.length / sqrt (4*π*t)) * (1/2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hhalf (div_nonneg C.length_pos.le (sqrt_nonneg _))

def chargedMagneticProperDensity (C : NormalCircle E) (θ t : ℝ) : ℝ :=
  (1 / (24*π^2)) * exp (-(C.mass^2*t)) * normalHeatTrace C t θ / t

/-- The literal magnetic-coefficient density of the periodic comparison
fails absolute integration at the UV endpoint for every holonomy. -/
theorem charged_magnetic_proper_diverges (C : NormalCircle E) (θ : ℝ) {T : ℝ} (hT : 0 < T) :
    ¬ IntegrableOn (chargedMagneticProperDensity C θ) (Ioo 0 T) := by
  obtain ⟨δ,hδ,hδ₁,hbound⟩ := normal_heatTrace_short_lower C
  let A := (1/(24*π^2)) * exp (-C.mass^2) * C.length / (2*sqrt (4*π))
  have hA : 0 < A := by
    dsimp [A]
    exact div_pos (mul_pos (mul_pos (by positivity) (exp_pos _)) C.length_pos) (by positivity)
  let b := min T δ
  have hb : 0 < b := lt_min hT hδ
  have hdom (t : ℝ) (ht : t ∈ Ioo (0:ℝ) b) : A*t^(-3/2:ℝ) ≤ chargedMagneticProperDensity C θ t := by
    have htδ : t ≤ δ := ht.2.le.trans (min_le_right _ _)
    have hm : exp (-C.mass^2) ≤ exp (-(C.mass^2*t)) :=
      exp_le_exp.2 (by nlinarith [mul_nonneg (sq_nonneg C.mass) (sub_nonneg.mpr (htδ.trans hδ₁))])
    have hconst : 0 ≤ (1/(24*π^2):ℝ) := by positivity
    have hp : 0 ≤ C.length/(2*sqrt (4*π*t)) := div_nonneg C.length_pos.le (by positivity)
    unfold chargedMagneticProperDensity
    calc
      _ = (1/(24*π^2)) * exp (-C.mass^2) * (C.length/(2*sqrt (4*π*t)))/t := by
        dsimp only [A]
        have he : t^(-3/2:ℝ) = (sqrt t)⁻¹*t⁻¹ := by
          rw [show (-3/2:ℝ) = -(1/2) + -1 by ring,rpow_add ht.1,rpow_neg ht.1.le,
            ← sqrt_eq_rpow,rpow_neg_one]
        rw [he,sqrt_mul (show (0:ℝ) ≤ 4*π by positivity)]
        ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left hm hconst) (hbound θ t ht.1 htδ) hp
          (mul_nonneg hconst (exp_nonneg _))) ht.1.le
  intro H
  have hh : IntegrableOn (fun t : ℝ => A*t^(-3/2:ℝ)) (Ioo 0 b) := by
    apply (H.mono_set (Ioo_subset_Ioo_right (min_le_left _ _))).mono'
      (measurable_const.mul (measurable_id.pow_const _)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    change ‖A * t^(-3/2:ℝ)‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg hA.le (rpow_nonneg ht.1.le _))]
    exact hdom t ht
  have h : IntegrableOn (fun t : ℝ => t^(-3/2:ℝ)) (Ioo 0 b) := by
    refine IntegrableOn.congr_fun (hh.const_mul A⁻¹) (fun t _ => ?_) measurableSet_Ioo
    rw [← mul_assoc, inv_mul_cancel₀ hA.ne', one_mul]
  have h' := (intervalIntegral.integrableOn_Ioo_rpow_iff hb).mp h
  norm_num at h'

end UV.ExtendNativeHolonomy
