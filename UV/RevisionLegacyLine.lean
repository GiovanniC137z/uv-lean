import UV.GlobalConvergence
import UV.WardCommonCutoff

/-! The complete selected-line threshold includes massive denominators
and a possible atom at depth zero. -/

noncomputable section
open MeasureTheory Set Real Filter
open scoped ENNReal

namespace UV

private def fullSelectedLine (ρ : Measure ℝ) (a m d : ℝ) (q : LoopMomentum) : ℝ :=
  ‖q‖ ^ d * laplace ρ (a ^ 2 * ‖q‖ ^ 2) / (‖q‖ ^ 2 + m ^ 2)

private theorem fullSelectedLine_measurable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) (a m d : ℝ) : Measurable (fullSelectedLine ρ a m d) := by
  unfold fullSelectedLine
  simp_rw [← wardLaplaceKernel_eq ρ a (sq_nonneg _)]
  have hm : Measurable (fun q : LoopMomentum => wardLaplaceKernel ρ a (‖q‖ ^ 2)) :=
    (wardLaplaceKernel_continuous ρ hp a).measurable.comp (by fun_prop)
  fun_prop

private theorem fullSelectedLine_nonneg (ρ : Measure ℝ) (a m d : ℝ) (q : LoopMomentum) :
    0 ≤ fullSelectedLine ρ a m d q := by
  unfold fullSelectedLine
  exact div_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
    (integral_nonneg fun _ => Real.exp_nonneg _)) (by positivity)

private theorem fullSelectedLine_zero_integrable_of_massive
    (ρ : Measure ℝ) [IsFiniteMeasure ρ] (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ)
    {a d m : ℝ} (hd : 0 ≤ d) (hm : 0 ≤ m)
    (h : Integrable (fullSelectedLine ρ a m d)) :
    Integrable (fullSelectedLine ρ a 0 d) := by
  let D := {q : LoopMomentum | ‖q‖ < m}
  have hD : MeasurableSet D := measurableSet_lt continuous_norm.measurable measurable_const
  have hsmall : IntegrableOn (fullSelectedLine ρ a 0 d) D := by
    have hgauss := ((massless_gaussian_integrable hd zero_lt_one).const_mul
      ((ρ Set.univ).toReal * Real.exp (m ^ 2))).integrableOn (s := D)
    apply hgauss.mono' (fullSelectedLine_measurable ρ hp a 0 d).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hD] with q hq
    change ‖q‖ < m at hq
    rw [Real.norm_of_nonneg (fullSelectedLine_nonneg ρ a 0 d q)]
    by_cases hz : q = 0
    · simp only [hz, fullSelectedLine, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
        add_zero, div_zero]
      positivity
    have hn : 0 < ‖q‖ := norm_pos_iff.mpr hz
    have hl : laplace ρ (a ^ 2 * ‖q‖ ^ 2) ≤ (ρ Set.univ).toReal := by
      have hh := nonnegative_laplace_antitone ρ hp (le_refl 0)
        (show 0 ≤ a ^ 2 * ‖q‖ ^ 2 by positivity)
      simpa [laplace, measureReal_def] using hh
    have hl' : laplace ρ (a ^ 2 * ‖q‖ ^ 2) ≤
        (ρ Set.univ).toReal * Real.exp (m ^ 2 - ‖q‖ ^ 2) := by
      refine hl.trans ?_
      apply le_mul_of_one_le_right ENNReal.toReal_nonneg
      exact Real.one_le_exp (sub_nonneg.mpr (pow_le_pow_left₀ hn.le hq.le 2))
    unfold fullSelectedLine
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, neg_mul, one_mul]
    rw [mul_div_right_comm, ← Real.rpow_two ‖q‖, ← Real.rpow_sub hn]
    simp only [Real.rpow_two]
    have hpos := Real.rpow_nonneg (norm_nonneg q) (d - 2)
    calc
      _ ≤ ‖q‖ ^ (d - 2) * ((ρ Set.univ).toReal * Real.exp (m ^ 2 - ‖q‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hl' hpos
      _ = _ := by simp only [sub_eq_add_neg, Real.exp_add]; ring
  have hlarge : IntegrableOn (fullSelectedLine ρ a 0 d) Dᶜ := by
    apply (h.const_mul (2 : ℝ)).integrableOn.mono'
      (fullSelectedLine_measurable ρ hp a 0 d).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hD.compl] with q hq
    change ¬ ‖q‖ < m at hq
    have hmq : m ≤ ‖q‖ := le_of_not_gt hq
    rw [Real.norm_of_nonneg (fullSelectedLine_nonneg ρ a 0 d q)]
    by_cases hz : q = 0
    · have hm0 : m = 0 := le_antisymm (by simpa [hz] using hmq) hm
      simp [hz, hm0, fullSelectedLine]
    have hn : 0 < ‖q‖ := norm_pos_iff.mpr hz
    have hden : 0 < ‖q‖ ^ 2 + m ^ 2 := by positivity
    have hcomp : ‖q‖ ^ 2 + m ^ 2 ≤ 2 * ‖q‖ ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hmq) (add_nonneg hn.le hm)]
    unfold fullSelectedLine
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (sq_pos_of_pos hn) hden).mpr
    have ht : 0 ≤ ‖q‖ ^ d * laplace ρ (a ^ 2 * ‖q‖ ^ 2) :=
      mul_nonneg (Real.rpow_nonneg hn.le _) (integral_nonneg fun _ => Real.exp_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left hcomp ht]
  simpa only [union_compl_self, integrableOn_univ] using hsmall.union hlarge

private theorem fullSelectedLine_atom_zero
    (ρ : Measure ℝ) [IsFiniteMeasure ρ] (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ)
    {a d : ℝ} (h : Integrable (fullSelectedLine ρ a 0 d)) :
    ρ {0} = 0 := by
  by_contra hzero
  have hpos : 0 < (ρ {0}).toReal := ENNReal.toReal_pos hzero (measure_ne_top _ _)
  have hnint : ¬ Integrable (fun q : LoopMomentum => ‖q‖ ^ (d - 2)) := by
    rw [show (fun q : LoopMomentum => ‖q‖ ^ (d - 2)) =
      (fun r : ℝ => r ^ (d - 2)) ∘ norm by rfl]
    intro hi
    have hrad := (integrable_fun_norm_addHaar (E := LoopMomentum) volume
      (f := fun r : ℝ => r ^ (d - 2))).mp hi
    apply not_integrableOn_Ioi_rpow (d + 1)
    apply hrad.congr_fun _ measurableSet_Ioi
    intro r hr
    simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
    rw [← Real.rpow_natCast r 3, ← Real.rpow_add hr]
    congr 1
    norm_num
    ring
  apply hnint
  have hsm : Measurable (fun q : LoopMomentum => ‖q‖ ^ (d - 2)) := by fun_prop
  apply (h.const_mul ((ρ {0}).toReal)⁻¹).mono' hsm.aestronglyMeasurable
  have hq : ∀ᵐ q : LoopMomentum, q ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [hq] with q hq
  have hn : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hl : (ρ {0}).toReal ≤ laplace ρ (a ^ 2 * ‖q‖ ^ 2) := by
    have hL := integral_mono_measure (Measure.restrict_le_self (s := {0}) (μ := ρ))
      (Eventually.of_forall fun τ => Real.exp_nonneg (-τ * (a ^ 2 * ‖q‖ ^ 2)))
      (nonnegative_laplace_integrable ρ hp (show 0 ≤ a ^ 2 * ‖q‖ ^ 2 by positivity))
    simpa [laplace, integral_singleton, measureReal_def] using hL
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hn.le _)]
  unfold fullSelectedLine
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
  rw [mul_div_right_comm, ← Real.rpow_two ‖q‖, ← Real.rpow_sub hn]
  simp only [Real.rpow_two]
  calc
    ‖q‖ ^ (d - 2) = ((ρ {0}).toReal)⁻¹ * (‖q‖ ^ (d - 2) * (ρ {0}).toReal) := by
      field_simp
    _ ≤ _ := by gcongr

/-- At each fixed nonnegative mass the literal full Laplace line is absolutely
integrable exactly when there is no atom at zero and the required inverse
moment is finite. -/
theorem full_selected_line_integrable_iff
    (ρ : Measure ℝ) [IsFiniteMeasure ρ] (hneg : ρ (Iio 0) = 0)
    {a d m : ℝ} (ha : 0 < a) (hd : 0 ≤ d) (hm : 0 ≤ m) :
    Integrable (fun q : LoopMomentum =>
      ‖q‖ ^ d * laplace ρ (a ^ 2 * ‖q‖ ^ 2) / (‖q‖ ^ 2 + m ^ 2)) ↔
      ρ {0} = 0 ∧ inverseMoment ρ (1 + d / 2) < ⊤ := by
  have hp : ∀ᵐ τ ∂ρ, 0 ≤ τ := by simpa only [ae_iff, not_le] using hneg
  constructor
  · intro hi
    have hmassless := fullSelectedLine_zero_integrable_of_massive ρ hp hd hm hi
    have hzero := fullSelectedLine_atom_zero ρ hp hmassless
    refine ⟨hzero, (actual_massless_selected_line_integrable_iff ρ hneg hzero ha hd).mp ?_⟩
    unfold fullSelectedLine at hmassless
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using hmassless
  · rintro ⟨hzero, hM⟩
    exact actual_selected_line_integrable ρ hneg hzero ha hd hM m

end UV
