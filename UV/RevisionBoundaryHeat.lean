import UV.ExponentialIntegral
import Mathlib.MeasureTheory.Measure.Prod

/-! The positive marked normal return of the revised manuscript. -/

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal Topology

namespace UV.RevisionBoundary

def returnIntegrand (y t : ℝ) : ℝ :=
  Real.exp (-(y ^ 2) / t) / t ^ 2

private theorem return_integrand_derivative {y t : ℝ} (hy : y ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ => Real.exp (-(y ^ 2) / u) / y ^ 2)
      (returnIntegrand y t) t := by
  have h := (((hasDerivAt_const t (-(y ^ 2))).div (hasDerivAt_id t) ht).exp).div_const (y ^ 2)
  convert h using 1
  simp only [Pi.div_apply, id_eq, returnIntegrand, zero_mul, mul_one, zero_sub, neg_neg]
  field_simp

private theorem return_primitive_tendsto {y : ℝ} (hy : y ≠ 0) :
    Tendsto (fun t : ℝ => Real.exp (-(y ^ 2) / t) / y ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg
    (show -(y ^ 2) < 0 by exact neg_neg_of_pos (sq_pos_of_ne_zero hy))
  have he := Real.tendsto_exp_atBot.comp h
  simpa only [Function.comp_def, ← div_eq_mul_inv, zero_div] using he.div_const (y ^ 2)

theorem return_integral_exact {T y : ℝ} (hT : 0 < T) (hy : y ≠ 0) :
    IntegrableOn (returnIntegrand y) (Ioc 0 T) ∧
      (∫ t in Ioc 0 T, returnIntegrand y t) = Real.exp (-(y ^ 2) / T) / y ^ 2 := by
  let F : ℝ → ℝ := fun t => if t = 0 then 0 else Real.exp (-(y ^ 2) / t) / y ^ 2
  have hF : ContinuousOn F (Icc 0 T) := by
    intro t ht
    by_cases hz : t = 0
    · subst t
      have hIoi : ContinuousWithinAt F (Ioi 0) 0 := by
        unfold ContinuousWithinAt
        rw [show F 0 = 0 by simp [F]]
        apply (return_primitive_tendsto hy).congr'
        filter_upwards [self_mem_nhdsWithin] with t ht
        simp [F, (show 0 < t from ht).ne']
      exact (continuousWithinAt_insert_self.mpr hIoi).mono (by
        intro t ht
        rcases eq_or_lt_of_le ht.1 with he | hl
        · simp [← he]
        · exact mem_insert_of_mem _ hl)
    · apply ContinuousAt.continuousWithinAt
      apply ((return_integrand_derivative hy hz).congr_of_eventuallyEq ?_).continuousAt
      filter_upwards [isOpen_ne.mem_nhds hz] with u hu
      simp [F, hu]
  have hder : ∀ t ∈ Ioo 0 T, HasDerivAt F (returnIntegrand y t) t := by
    intro t ht
    apply (return_integrand_derivative hy ht.1.ne').congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds ht.1.ne'] with u hu
    simp [F, hu]
  have hi := intervalIntegral.integrableOn_deriv_of_nonneg hF hder
      (fun t _ => div_nonneg (Real.exp_nonneg _) (sq_nonneg t))
  refine ⟨hi, ?_⟩
  rw [← intervalIntegral.integral_of_le hT.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le hF hder
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr hi)]
  simp [F, hT.ne']

theorem return_integral_zero_diverges {T : ℝ} (hT : 0 < T) :
    ¬ IntegrableOn (returnIntegrand 0) (Ioc 0 T) := by
  intro h
  have h' := h.mono_set (Ioo_subset_Ioc_self : Ioo (0 : ℝ) T ⊆ Ioc 0 T)
  have hh : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Ioo 0 T) := by
    apply h'.congr_fun
    · intro t ht
      have ht' := ht.1.le
      simp [returnIntegrand, Real.rpow_neg ht', one_div]
    · exact measurableSet_Ioo
  exact (by norm_num : ¬ (-1 : ℝ) < -2)
    ((intervalIntegral.integrableOn_Ioo_rpow_iff hT).mp hh)

def integratedNormalReturn (T : ℝ) (μ : Measure ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) *
    ∫⁻ t in Ioc 0 T, ∫⁻ y, ENNReal.ofReal (returnIntegrand y t) ∂μ

def returnCost (T y : ℝ) : ℝ≥0∞ :=
  if y = 0 then ∞ else ENNReal.ofReal (Real.exp (-(y ^ 2) / T) / y ^ 2)

theorem integratedNormalReturn_eq {T : ℝ} (hT : 0 < T)
    (μ : Measure ℝ) [SFinite μ] :
    integratedNormalReturn T μ =
      ENNReal.ofReal (1 / (2 * Real.pi)) * ∫⁻ y, returnCost T y ∂μ := by
  unfold integratedNormalReturn
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (returnIntegrand p.2 p.1)) := by
    unfold returnIntegrand
    fun_prop
  rw [lintegral_lintegral_swap hm.aemeasurable]
  congr 1
  apply lintegral_congr
  intro y
  by_cases hy : y = 0
  · subst y
    rw [returnCost, if_pos rfl]
    by_contra h
    have hh : IntegrableOn (returnIntegrand 0) (Ioc 0 T) := by
      constructor
      · exact (by unfold returnIntegrand; fun_prop : Measurable (returnIntegrand 0)).aestronglyMeasurable
      · apply lt_top_iff_ne_top.mpr
        convert h using 2
        funext t
        rw [← ofReal_norm, Real.norm_of_nonneg (show 0 ≤ returnIntegrand 0 t from
          div_nonneg (Real.exp_nonneg _) (sq_nonneg t))]
    exact return_integral_zero_diverges hT hh
  · rw [returnCost, if_neg hy, ← (return_integral_exact hT hy).2,
      ofReal_integral_eq_lintegral_ofReal (return_integral_exact hT hy).1]
    exact Eventually.of_forall fun t => div_nonneg (Real.exp_nonneg _) (sq_nonneg t)

def massWeightedNormalReturn (m T : ℝ) (μ : Measure ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) *
    ∫⁻ t in Ioc 0 T, ENNReal.ofReal (Real.exp (-(m ^ 2) * t)) *
      ∫⁻ y, ENNReal.ofReal (returnIntegrand y t) ∂μ

/-- The actual mass factor preserves finiteness and only decreases the
upper bound on the absolute ultraviolet cost. -/
theorem mass_weighted_return_comparison (m T : ℝ) (μ : Measure ℝ) [SFinite μ] :
    ENNReal.ofReal (Real.exp (-(m ^ 2) * T)) * integratedNormalReturn T μ ≤
      massWeightedNormalReturn m T μ ∧
    massWeightedNormalReturn m T μ ≤ integratedNormalReturn T μ := by
  let g : ℝ → ℝ≥0∞ := fun t => ∫⁻ y, ENNReal.ofReal (returnIntegrand y t) ∂μ
  have hg : Measurable g := by
    apply Measurable.lintegral_prod_right (f := fun t y => ENNReal.ofReal (returnIntegrand y t))
    unfold Function.uncurry returnIntegrand
    fun_prop
  constructor
  · have h :
        (∫⁻ t in Ioc 0 T, ENNReal.ofReal (Real.exp (-(m ^ 2) * T)) * g t) ≤
           ∫⁻ t in Ioc 0 T, ENNReal.ofReal (Real.exp (-(m ^ 2) * t)) * g t := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left ht.2 (neg_nonpos.mpr (sq_nonneg _))))) _
    rw [lintegral_const_mul _ hg] at h
    unfold integratedNormalReturn massWeightedNormalReturn
    exact (mul_left_comm _ _ _).le.trans (mul_le_mul_left' h _)
  · unfold massWeightedNormalReturn integratedNormalReturn
    apply mul_le_mul_left'
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    nth_rw 2 [← one_mul (∫⁻ y, ENNReal.ofReal (returnIntegrand y t) ∂μ)]
    apply mul_le_mul_right'
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) ht.1.le))

theorem mass_weighted_return_finiteness (m T : ℝ) (μ : Measure ℝ) [SFinite μ] :
    massWeightedNormalReturn m T μ ≠ ∞ ↔ integratedNormalReturn T μ ≠ ∞ := by
  obtain ⟨hlo, hhi⟩ := mass_weighted_return_comparison m T μ
  refine ⟨fun hm h => hm ?_, fun h => ne_top_of_le_ne_top h hhi⟩
  rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'] at hlo
  exact top_le_iff.mp hlo


/-- For a finite normal midpoint law, the exact ultraviolet test is
absence of a zero-displacement atom and the local inverse-square moment. -/
theorem marked_return_finiteness_iff {T : ℝ} (hT : 0 < T) (μ : Measure ℝ)
    [IsFiniteMeasure μ] :
    integratedNormalReturn T μ ≠ ∞ ↔ μ ({0} : Set ℝ) = 0 ∧
      IntegrableOn (fun x : ℝ => 1 / x ^ 2) (Icc (-1) 1) μ := by
  let f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2) / T) / x ^ 2
  let u : ℝ → ℝ := fun x => 1 / x ^ 2
  have hff : Measurable f := by unfold f; fun_prop
  have hmm : Measurable (returnCost T) := by
    unfold returnCost
    exact Measurable.ite (measurableSet_singleton _) measurable_const hff.ennreal_ofReal
  have hu : Measurable u := by unfold u; fun_prop
  have hf0 : ∀ x, 0 ≤ f x := fun _ => div_nonneg (Real.exp_nonneg _) (sq_nonneg _)
  have hcpos : ENNReal.ofReal (1 / (2 * Real.pi)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have htop : {x | returnCost T x = ∞} = ({0} : Set ℝ) := by
    ext x
    by_cases h : x = 0 <;> simp [h, returnCost, ENNReal.ofReal_ne_top]
  have heq (hn : μ ({0} : Set ℝ) = 0) : (∫⁻ x, returnCost T x ∂μ) =
      ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
    apply lintegral_congr_ae
    have hne : ∀ᵐ x ∂μ, x ≠ (0 : ℝ) := by simpa [ae_iff] using hn
    filter_upwards [hne] with x hx
    exact if_neg hx
  have hle (x : ℝ) : f x ≤ u x :=
    div_le_div_of_nonneg_right (Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) hT.le)) (sq_nonneg _)
  rw [integratedNormalReturn_eq hT]
  constructor
  · intro h
    have hi : (∫⁻ x, returnCost T x ∂μ) ≠ ∞ := by
      intro ht
      exact h (by rw [ht, ENNReal.mul_top hcpos])
    have hn : μ ({0} : Set ℝ) = 0 := by
      simpa only [htop] using measure_eq_top_of_lintegral_ne_top hmm.aemeasurable hi
    rw [heq hn] at hi
    have hfint : Integrable f μ := (lintegral_ofReal_ne_top_iff_integrable
      hff.aestronglyMeasurable (Eventually.of_forall hf0)).mp hi
    refine ⟨hn, ?_⟩
    let c := Real.exp (-1 / T)
    have hc : 0 < c := Real.exp_pos _
    refine ((hfint.const_mul c⁻¹).restrict (s := Icc (-1) 1)).mono'
      hu.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    change ‖1 / x ^ 2‖ ≤ c⁻¹ * f x
    rw [Real.norm_of_nonneg (div_nonneg zero_le_one (sq_nonneg _)),
      ← div_eq_inv_mul, le_div_iff₀ hc]
    unfold c f
    rw [div_mul_eq_mul_div, one_mul]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ hT.le
    have hx2 : x ^ 2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (show 0 ≤ x + 1 by linarith [hx.1])]
    linarith
  · rintro ⟨hn, huI⟩
    have huC : IntegrableOn u (Icc (-1) 1)ᶜ μ := by
      apply (integrableOn_const (C := (1 : ℝ))).mono' hu.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with x hx
      change ‖1 / x ^ 2‖ ≤ 1
      rw [Real.norm_of_nonneg (div_nonneg zero_le_one (sq_nonneg _))]
      have hx2 : 1 ≤ x ^ 2 := by
        simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · nlinarith [mul_nonneg (show 0 ≤ -x - 1 by linarith) (show 0 ≤ -x + 1 by linarith)]
        · nlinarith [mul_nonneg (show 0 ≤ x - 1 by linarith) (show 0 ≤ x + 1 by linarith)]
      exact div_le_one_of_le₀ hx2 (sq_nonneg _)
    have hui : Integrable u μ := integrableOn_univ.mp (by
      simpa only [union_compl_self] using huI.union huC)
    have hfi := hui.mono' hff.aestronglyMeasurable <| Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (hf0 x)]
      exact hle x
    rw [heq hn]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ((lintegral_ofReal_ne_top_iff_integrable hff.aestronglyMeasurable
        (Eventually.of_forall hf0)).mpr hfi)


def zeroVisitCost (m T : ℝ) (c₀ : ℝ≥0∞) : ℝ≥0∞ :=
  c₀ * ∫⁻ t in Ioc 0 T, ENNReal.ofReal (Real.exp (-(m ^ 2) * t) / t)

private theorem zero_visit_inner_diverges (m : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫⁻ t in Ioc 0 T, ENNReal.ofReal (Real.exp (-(m ^ 2) * t) / t)) = ∞ := by
  by_contra h
  have hfi : IntegrableOn (fun t : ℝ => Real.exp (-(m ^ 2) * t) / t) (Ioc 0 T) :=
    (lintegral_ofReal_ne_top_iff_integrable
      (by fun_prop : Measurable fun t : ℝ => Real.exp (-(m ^ 2) * t) / t).aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Ioc).mono fun _ ht => div_nonneg (Real.exp_nonneg _) ht.1.le)).mp h
  let c := Real.exp (-(m ^ 2) * T)
  have hc : 0 < c := Real.exp_pos _
  have hr : IntegrableOn (fun t : ℝ => t ^ (-1 : ℝ)) (Ioo 0 T) := by
    refine ((hfi.mono_set Ioo_subset_Ioc_self).const_mul c⁻¹).mono'
      (measurable_id.pow_const _).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _), Real.rpow_neg_one,
      ← div_eq_inv_mul, le_div_iff₀ hc, mul_comm t⁻¹ c, ← div_eq_mul_inv]
    apply div_le_div_of_nonneg_right _ ht.1.le
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left ht.2.le (neg_nonpos.mpr (sq_nonneg _))
  exact lt_irrefl (-1 : ℝ) ((intervalIntegral.integrableOn_Ioo_rpow_iff hT).mp hr)

/-- The direct-sum zero-visit term retains the entire logarithmic ultraviolet
divergence. For a finite marked law, the combined magnetic cost is finite
exactly for zero unvisited weight, no atom at the seam, and an inverse-square
moment at the seam. -/
theorem marked_and_zero_visit_finiteness (m : ℝ) {T : ℝ} (hT : 0 < T)
    (c₀ : ℝ≥0∞) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    zeroVisitCost m T c₀ + massWeightedNormalReturn m T μ ≠ ∞ ↔
      c₀ = 0 ∧ μ ({0} : Set ℝ) = 0 ∧
        IntegrableOn (fun x : ℝ => 1 / x ^ 2) (Icc (-1) 1) μ := by
  rw [ENNReal.add_ne_top, mass_weighted_return_finiteness, marked_return_finiteness_iff hT]
  unfold zeroVisitCost
  rw [zero_visit_inner_diverges m hT]
  by_cases hc : c₀ = 0
  · simp [hc]
  · simp [hc, ENNReal.mul_top hc]


end UV.RevisionBoundary
