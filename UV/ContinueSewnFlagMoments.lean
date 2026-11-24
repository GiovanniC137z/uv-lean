import UV.ContinueSewnFlagEndpoint
import UV.ContinueNetworkTonelli

/-! Duration integration against a joint displacement measure. The
displacement coordinates can be correlated, even when the ratio
parameters have independent Lebesgue measures. -/

noncomputable section
open Real MeasureTheory Filter Set
open scoped ENNReal BigOperators
namespace UV.SewnFlags

def ratioCostConstant (a c : ℝ) : ℝ :=
  if 0 < a then 1/a else if a = 0 then 2 + max 0 (log (1/c)) else c^a * Gamma (-a)

theorem ratioCostConstant_pos (a : ℝ) {c : ℝ} (hc : 0 < c) :
    0 < ratioCostConstant a c := by
  unfold ratioCostConstant
  split_ifs with ha hzero
  · positivity
  · have := le_max_left 0 (log (1/c))
    linarith
  · have hn : 0 < -a := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt ha) hzero)
    exact mul_pos (rpow_pos_of_pos hc _) (Gamma_pos_of_pos hn)

theorem measurable_displacementCost (a : ℝ) : Measurable (displacementCost a) := by
  unfold displacementCost
  split_ifs with ha ha'
  · exact measurable_const
  · exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)
  · exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

/-- All three signs of the excess degree, with its stipulated infinite
cost when a nonpositive face loses the projected displacement. -/
theorem ratioCost_le_displacement (a : ℝ) {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    ratioCost a (c*x^2) ≤ ENNReal.ofReal (ratioCostConstant a c) * displacementCost a x := by
  by_cases ha : 0 < a
  · rw [ratioCostConstant,if_pos ha,displacementCost,if_pos ha,mul_one]
    calc
      _ ≤ directionalEndpointMass a 1 := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        apply ENNReal.ofReal_le_ofReal
        unfold ratioHeat
        exact mul_le_of_le_one_right (rpow_nonneg hr.1.le _)
          (exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr (mul_nonneg hc.le (sq_nonneg x))) hr.1.le))
      _ = _ := by rw [directionalEndpointMass_eq zero_lt_one,if_pos ha,one_rpow]
  by_cases hx₀ : x = 0
  · rw [displacementCost,if_neg ha,if_pos hx₀,ENNReal.mul_top (by
      exact ENNReal.ofReal_ne_zero_iff.mpr (ratioCostConstant_pos a hc))]
    exact le_top
  have hx' : 0 < x := lt_of_le_of_ne hx (Ne.symm hx₀)
  have hl : 0 < c*x^2 := by positivity
  by_cases hz : a = 0
  · subst a
    rw [ratioCostConstant,if_neg (lt_irrefl _),if_pos rfl,displacementCost,if_neg (lt_irrefl _),
      if_neg hx₀,if_pos rfl,← ENNReal.ofReal_mul (by linarith [le_max_left 0 (log (1/c))])]
    apply (ratioCost_log hl).trans
    apply ENNReal.ofReal_le_ofReal
    have he : log (1/(c*x^2)) = log (1/c) + 2*log (1/x) := by
      rw [one_div,log_inv,log_mul hc.ne' (pow_ne_zero _ hx₀),log_pow,one_div,one_div,log_inv,log_inv]
      norm_num
      ring
    let A := max 0 (log (1/c))
    let B := max 0 (log (1/x))
    have hA : 0 ≤ A := le_max_left _ _
    have hB : 0 ≤ B := le_max_left _ _
    have hlog : max 0 (log (1/(c*x^2))) ≤ A+2*B := by
      rw [he]
      exact max_le (by positivity) (add_le_add (le_max_right _ _) (by gcongr; exact le_max_right _ _))
    change 1 + _ ≤ (2+A)*(1+B)
    nlinarith [mul_nonneg hA hB]
  have han : a < 0 := lt_of_le_of_ne (le_of_not_gt ha) hz
  have hC : 0 ≤ c^a * Gamma (-a) := mul_nonneg (rpow_nonneg hc.le _) (Gamma_pos_of_pos (neg_pos.mpr han)).le
  rw [ratioCostConstant,if_neg ha,if_neg hz,displacementCost,if_neg ha,if_neg hx₀,if_neg hz,
    ← ENNReal.ofReal_mul hC]
  have h := ratioHeat_negative han hl
  calc
    _ ≤ ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (ratioHeat a (c*x^2) r) :=
      lintegral_mono_set Ioo_subset_Ioi_self
    _ = ENNReal.ofReal ((c*x^2)^a * Gamma (-a)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal h.1
        ((ae_restrict_mem measurableSet_Ioi).mono fun r hr => by
          unfold ratioHeat
          exact mul_nonneg (rpow_nonneg hr.le _) (exp_pos _).le),h.2]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [mul_rpow hc.le (sq_nonneg x), ← rpow_natCast, ← rpow_mul hx]
      push_cast
      nlinarith

/-- The product of the ratio integrals is controlled by one joint
moment of the full displacement law. No independence of the projections
is used, and the statement holds for arbitrary finite flag length. -/
theorem joint_displacement_ratios {ι D : Type*} [Fintype ι] [MeasurableSpace D]
    (μ : Measure D) (a c : ι → ℝ) (x : ι → D → ℝ)
    (hc : ∀ i, 0 < c i) (hx : ∀ i d, 0 ≤ x i d) (hxm : ∀ i, Measurable (x i))
    (hJoint : (∫⁻ d, ∏ i, displacementCost (a i) (x i d) ∂μ) < ⊤) :
    (∫⁻ d, ∫⁻ r : ι → ℝ, ∏ i, ENNReal.ofReal (ratioHeat (a i) (c i*(x i d)^2) (r i))
          ∂Measure.pi (fun _ : ι => volume.restrict (Ioo (0:ℝ) 1)) ∂μ) < ⊤ := by
  let K := ∏ i, ENNReal.ofReal (ratioCostConstant (a i) (c i))
  have hK : K ≠ ⊤ := ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)
  have hmeas : Measurable fun d => ∏ i, displacementCost (a i) (x i d) :=
    Finset.measurable_prod _ (fun i _ => (measurable_displacementCost (a i)).comp (hxm i))
  refine lt_of_le_of_lt (lintegral_mono (g := fun d => K * ∏ i, displacementCost (a i) (x i d)) ?_) ?_
  · intro d
    dsimp only
    rw [UV.network_lintegral_fintype_prod _ (fun i r => ENNReal.ofReal (ratioHeat (a i) (c i*(x i d)^2) r))
      (fun i => by unfold ratioHeat; fun_prop), ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod' (fun i _ => ratioCost_le_displacement (a i) (hc i) (hx i d))
  · rw [lintegral_const_mul _ hmeas]
    exact ENNReal.mul_lt_top hK.lt_top hJoint

/-- Finitely many marginal moments of degree equal to the number of
faces imply the joint product moment under any correlations. -/
theorem joint_cost_finite_of_marginals {ι D : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace D]
    (μ : Measure D) (cost : ι → D → ℝ≥0∞) (hc : ∀ i, Measurable (cost i))
    (hm : ∀ i, (∫⁻ d, cost i d ^ Fintype.card ι ∂μ) < ⊤) :
    (∫⁻ d, ∏ i, cost i d ∂μ) < ⊤ := by
  have h (d : D) : (∏ i, cost i d) ≤ ∑ i, cost i d ^ Fintype.card ι := by
    let s := (Finset.univ : Finset ι).sup (fun i => cost i d)
    obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun i => cost i d)
    calc
      _ ≤ ∏ _i : ι, s := Finset.prod_le_prod' (fun i hi => Finset.le_sup (f := fun i => cost i d) hi)
      _ = cost j d ^ Fintype.card ι := by rw [Finset.prod_const,Finset.card_univ,show s = cost j d from he]
      _ ≤ _ := Finset.single_le_sum (fun i _ => zero_le (cost i d ^ Fintype.card ι)) hj
  apply (lintegral_mono h).trans_lt
  rw [lintegral_finset_sum Finset.univ (fun i _ => (hc i).pow_const _)]
  exact ENNReal.sum_lt_top.mpr (fun i _ => hm i)

end UV.SewnFlags
