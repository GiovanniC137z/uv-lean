import UV.ContinueVisitCutoffLimit

/-! The cutoff variance of the shared visit law has a finite limit
exactly under the local inverse-fourth moment condition, when the
first uncut moment is finite. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace UV.ContinueVisitVarianceLimit

open UV.RevisionBoundary UV.VerifyVisitConnectedJet UV.ContinueVisitCutoffLimit

private def inverseFourth (x : ℝ) : ℝ := 1 / x ^ (4 : ℕ)

private def uncutVisitSquaredProfile (T x : ℝ) : ℝ :=
  ((1 / (2 * Real.pi)) * (Real.exp (-(x ^ (2 : ℕ)) / T) / x ^ (2 : ℕ))) ^ (2 : ℕ)

private theorem inverse_fourth_measurable : Measurable inverseFourth := by
  unfold inverseFourth
  fun_prop

private theorem inverse_fourth_nonneg (x : ℝ) : 0 ≤ inverseFourth x := by
  unfold inverseFourth
  positivity

private theorem uncut_visit_squared_atom (T : ℝ) :
    {x | uncutVisit T x ^ (2 : ℕ) = ⊤} = ({0} : Set ℝ) := by
  have hc : ENNReal.ofReal (1 / (2 * Real.pi)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  ext x
  by_cases hx : x = 0
  · simp only [mem_setOf_eq, mem_singleton_iff, hx, uncutVisit, returnCost,
      if_pos, ENNReal.mul_top hc, ENNReal.top_pow (by decide : (2 : ℕ) ≠ 0)]
  · simp only [mem_setOf_eq, mem_singleton_iff, hx, iff_false, uncutVisit, returnCost]
    exact ENNReal.pow_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

private theorem uncut_visit_squared_off_atom (T : ℝ) {x : ℝ} (hx : x ≠ 0) :
    uncutVisit T x ^ (2 : ℕ) = ENNReal.ofReal (uncutVisitSquaredProfile T x) := by
  unfold uncutVisit uncutVisitSquaredProfile returnCost
  rw [if_neg hx, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity)]

private theorem uncut_visit_squared_factor (T x : ℝ) :
    uncutVisitSquaredProfile T x =
      ((1 / (2 * Real.pi)) ^ (2 : ℕ)) * Real.exp (-(x ^ (2 : ℕ)) / T) ^ (2 : ℕ) *
        inverseFourth x := by
  unfold uncutVisitSquaredProfile inverseFourth
  simp only [mul_pow, div_pow, ← pow_mul]
  ring

private theorem inverse_fourth_integrable_off_unit_interval (μ : Measure ℝ)
    [IsFiniteMeasure μ] :
    IntegrableOn inverseFourth (Icc (-1) 1)ᶜ μ := by
  apply (integrableOn_const (C := (1 : ℝ))).mono' inverse_fourth_measurable.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with x hx
  rw [Real.norm_of_nonneg (inverse_fourth_nonneg x)]
  have ha : 1 ≤ |x| := by
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · simpa only [neg_neg] using (neg_le_neg hx.le).trans (neg_le_abs x)
    · exact hx.le.trans (le_abs_self x)
  have hx4 : 1 ≤ x ^ (4 : ℕ) := by
    calc
      1 ≤ |x| ^ (4 : ℕ) := one_le_pow₀ ha
      _ = _ := by rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ x ^ (4 : ℕ))]
  exact div_le_one_of_le₀ hx4 (by positivity)

private theorem uncut_visit_squared_local_lower {T : ℝ} (hT : 0 < T) {x : ℝ}
    (hx : x ∈ Icc (-1) 1) :
    ((1 / (2 * Real.pi)) ^ (2 : ℕ) * Real.exp (-1 / T) ^ (2 : ℕ)) * inverseFourth x ≤
      uncutVisitSquaredProfile T x := by
  have hx2 : x ^ (2 : ℕ) ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (show 0 ≤ x + 1 by linarith [hx.1])]
  have he : Real.exp (-1 / T) ≤ Real.exp (-(x ^ (2 : ℕ)) / T) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg hx2) hT.le)
  rw [uncut_visit_squared_factor]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_nonneg _) he 2) (by positivity))
    (inverse_fourth_nonneg x)

private theorem uncut_visit_squared_upper {T : ℝ} (hT : 0 < T) (x : ℝ) :
    uncutVisitSquaredProfile T x ≤ (1 / (2 * Real.pi)) ^ (2 : ℕ) * inverseFourth x := by
  have he : Real.exp (-(x ^ (2 : ℕ)) / T) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) hT.le)
  rw [uncut_visit_squared_factor]
  apply mul_le_mul_of_nonneg_right _ (inverse_fourth_nonneg x)
  exact mul_le_of_le_one_right (by positivity)
    (by simpa using pow_le_pow_left₀ (Real.exp_nonneg _) he 2)

/-- This test includes the singular atom separately from the local
integral, since real inverse powers are totalized at zero in Lean. -/
theorem uncut_visit_second_moment_iff {T : ℝ} (hT : 0 < T)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (∫⁻ x, uncutVisit T x ^ (2 : ℕ) ∂μ) ≠ ⊤ ↔
      μ ({0} : Set ℝ) = 0 ∧ IntegrableOn (fun x : ℝ => 1 / x ^ (4 : ℕ)) (Icc (-1) 1) μ := by
  have hm : Measurable (uncutVisitSquaredProfile T) := by
    unfold uncutVisitSquaredProfile
    fun_prop
  have hp : ∀ x, 0 ≤ uncutVisitSquaredProfile T x := fun x => by
    unfold uncutVisitSquaredProfile
    positivity
  have heq (ha : μ ({0} : Set ℝ) = 0) :
      (∫⁻ x, uncutVisit T x ^ (2 : ℕ) ∂μ) =
        ∫⁻ x, ENNReal.ofReal (uncutVisitSquaredProfile T x) ∂μ := by
    have hn : ∀ᵐ x ∂μ, x ≠ (0 : ℝ) := by simpa [ae_iff] using ha
    exact lintegral_congr_ae (hn.mono (fun _ => uncut_visit_squared_off_atom T))
  have hiff := lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Eventually.of_forall hp : ∀ᵐ x ∂μ, 0 ≤ uncutVisitSquaredProfile T x)
  constructor
  · intro hf
    have ha : μ ({0} : Set ℝ) = 0 := by
      simpa only [uncut_visit_squared_atom] using
        measure_eq_top_of_lintegral_ne_top ((uncut_visit_measurable T).pow_const 2).aemeasurable hf
    refine ⟨ha, ?_⟩
    rw [heq ha] at hf
    let k := (1 / (2 * Real.pi)) ^ (2 : ℕ) * Real.exp (-1 / T) ^ (2 : ℕ)
    have hk : 0 < k := by unfold k; positivity
    apply (((hiff.mp hf).const_mul k⁻¹).restrict (s := Icc (-1) 1)).mono'
      inverse_fourth_measurable.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_of_nonneg (inverse_fourth_nonneg x), ← div_eq_inv_mul, le_div_iff₀ hk,
      mul_comm (inverseFourth x)]
    exact uncut_visit_squared_local_lower hT hx
  · rintro ⟨ha, hlocal⟩
    have hi : Integrable inverseFourth μ := by
      apply integrableOn_univ.mp
      simpa only [union_compl_self] using hlocal.union
        (inverse_fourth_integrable_off_unit_interval μ)
    rw [heq ha]
    apply hiff.mpr
    apply (hi.const_mul ((1 / (2 * Real.pi)) ^ (2 : ℕ))).mono' hm.aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (hp x)]
      exact uncut_visit_squared_upper hT x

private theorem visit_cutoff_memLp (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ T : ℝ} (hδ : 0 < δ) (hδT : δ ≤ T) :
    MemLp (visitCutoff δ T) 2 μ :=
  memLp_of_bounded (Eventually.of_forall (visit_cutoff_bounds hδ hδT))
    (visit_cutoff_measurable δ T).aestronglyMeasurable 2

private theorem cutoff_variance_as_moments (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ T : ℝ} (hδ : 0 < δ) (hδT : δ ≤ T) :
    ENNReal.ofReal (ProbabilityTheory.variance (visitCutoff δ T) μ) =
      (∫⁻ x, ENNReal.ofReal (visitCutoff δ T x) ^ (2 : ℕ) ∂μ) -
        (∫⁻ x, ENNReal.ofReal (visitCutoff δ T x) ∂μ) ^ (2 : ℕ) := by
  have hL := visit_cutoff_memLp μ hδ hδT
  have hi : Integrable (visitCutoff δ T) μ := hL.integrable (by norm_num)
  have hi2 : Integrable (fun x => visitCutoff δ T x ^ (2 : ℕ)) μ := hL.integrable_sq
  have hp : ∀ x, 0 ≤ visitCutoff δ T x := fun x => (visit_cutoff_bounds hδ hδT x).1
  simp_rw [← ENNReal.ofReal_pow (hp _)]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hp),
    ← ofReal_integral_eq_lintegral_ofReal hi2 (Eventually.of_forall fun _ => sq_nonneg _),
    ← ENNReal.ofReal_pow (integral_nonneg hp), ProbabilityTheory.variance_eq_sub hL,
    ENNReal.ofReal_sub _ (sq_nonneg _)]
  rfl

/-- With a finite first uncut moment, the limit of cutoff variances
is the extended second moment minus the square of the first moment. -/
theorem connected_visit_variance_tendsto {T : ℝ} (hT : 0 < T) {δ : ℕ → ℝ}
    (hδ : ∀ n, 0 < δ n) (hδT : ∀ n, δ n ≤ T) (hmono : Antitone δ)
    (hlim : Tendsto δ atTop (𝓝 0)) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmean : integratedNormalReturn T μ ≠ ⊤) :
    Tendsto (fun n => ENNReal.ofReal (ProbabilityTheory.variance (visitCutoff (δ n) T) μ))
      atTop (𝓝 ((∫⁻ x, uncutVisit T x ^ (2 : ℕ) ∂μ) -
        (integratedNormalReturn T μ) ^ (2 : ℕ))) := by
  simp_rw [cutoff_variance_as_moments μ (hδ _) (hδT _)]
  have h1 := cutoff_visit_moment_tendsto hT hδ hδT hmono hlim μ 1
  have h2 := cutoff_visit_moment_tendsto hT hδ hδT hmono hlim μ 2
  simp_rw [pow_one] at h1
  rw [uncut_visit_first_moment hT] at h1
  exact ENNReal.Tendsto.sub h2 (((ENNReal.continuous_pow 2).tendsto _).comp h1)
    (Or.inr (ENNReal.pow_ne_top hmean))

theorem connected_visit_variance_limit_finite_iff {T : ℝ} (hT : 0 < T)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hmean : integratedNormalReturn T μ ≠ ⊤) :
    ((∫⁻ x, uncutVisit T x ^ (2 : ℕ) ∂μ) -
        (integratedNormalReturn T μ) ^ (2 : ℕ)) ≠ ⊤ ↔
      μ ({0} : Set ℝ) = 0 ∧ IntegrableOn (fun x : ℝ => 1 / x ^ (4 : ℕ)) (Icc (-1) 1) μ := by
  rw [← uncut_visit_second_moment_iff hT]
  refine ⟨fun h htop => h ?_, fun h => ne_top_of_le_ne_top h tsub_le_self⟩
  rw [htop, ENNReal.top_sub (ENNReal.pow_ne_top hmean)]

theorem connected_visit_variance_tendsto_right {T : ℝ} (hT : 0 < T)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hmean : integratedNormalReturn T μ ≠ ⊤) :
    Tendsto (fun δ => ENNReal.ofReal (ProbabilityTheory.variance (visitCutoff δ T) μ))
      (𝓝[>] 0) (𝓝 ((∫⁻ x, uncutVisit T x ^ (2 : ℕ) ∂μ) -
        (integratedNormalReturn T μ) ^ (2 : ℕ))) := by
  have h1 := cutoff_visit_moment_tendsto_right hT μ 1
  have h2 := cutoff_visit_moment_tendsto_right hT μ 2
  simp_rw [pow_one] at h1
  rw [uncut_visit_first_moment hT] at h1
  refine (ENNReal.Tendsto.sub h2 (((ENNReal.continuous_pow 2).tendsto _).comp h1)
    (Or.inr (ENNReal.pow_ne_top hmean))).congr' ?_
  filter_upwards [eventually_positive_visit_cutoff hT] with δ hδ
  exact (cutoff_variance_as_moments μ hδ.1 hδ.2).symm

/-- The literal double-tag coefficient has a right cutoff limit, and
for nonzero magnetic coefficient it is finite under exactly the same
inverse-fourth condition as the variance. -/
theorem connected_double_visit_coefficient_cutoff_limit {T : ℝ} (hT : 0 < T)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hmean : integratedNormalReturn T μ ≠ ⊤)
    {c : ℝ} (hc : c ≠ 0) (fourth : ℝ → ℝ) :
    let L := ENNReal.ofReal (c ^ (2 : ℕ) / 2) *
      ((∫⁻ x, uncutVisit T x ^ (2 : ℕ) ∂μ) - (integratedNormalReturn T μ) ^ (2 : ℕ))
    Tendsto (fun δ => ENNReal.ofReal (MvPolynomial.coeff (visitJetIndex 2 4)
      (connectedVisitJet (averagedVisitJet μ (fun x => c * visitCutoff δ T x) fourth))))
      (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
      (L ≠ ⊤ ↔ μ ({0} : Set ℝ) = 0 ∧
        IntegrableOn (fun x : ℝ => 1 / x ^ (4 : ℕ)) (Icc (-1) 1) μ) := by
  dsimp only
  constructor
  · refine (ENNReal.Tendsto.const_mul (connected_visit_variance_tendsto_right hT μ hmean)
      (Or.inr ENNReal.ofReal_ne_top)).congr' ?_
    filter_upwards [eventually_positive_visit_cutoff hT] with δ hδ
    rw [connected_marked_visit_variance μ hδ.1 hδ.2, ENNReal.ofReal_mul (by positivity)]
  · rw [← connected_visit_variance_limit_finite_iff hT μ hmean]
    have hk : ENNReal.ofReal (c ^ (2 : ℕ) / 2) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (div_pos (sq_pos_of_ne_zero hc) two_pos)).ne'
    exact ⟨fun hL h => hL (by rw [h, ENNReal.mul_top hk]),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top⟩

end UV.ContinueVisitVarianceLimit
