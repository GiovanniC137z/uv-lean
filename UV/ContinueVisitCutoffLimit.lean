import UV.VerifyVisitConnectedJet
import UV.VerifyVisitGamma

/-! Removal of the positive proper-time cutoff for a common normal
displacement, and the resulting local fourth-inverse-moment test. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace UV.ContinueVisitCutoffLimit

open UV.RevisionBoundary UV.VerifyVisitConnectedJet

def uncutVisit (T x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) * returnCost T x

theorem uncut_visit_measurable (T : ℝ) : Measurable (uncutVisit T) := by
  unfold uncutVisit returnCost
  exact measurable_const.mul <|
    Measurable.ite (measurableSet_singleton _) measurable_const (by fun_prop)

private theorem uncut_visit_time {T : ℝ} (hT : 0 < T) (x : ℝ) :
    uncutVisit T x = ENNReal.ofReal (1 / (2 * Real.pi)) *
      ∫⁻ t in Ioc 0 T, ENNReal.ofReal (returnIntegrand x t) := by
  unfold uncutVisit
  congr 1
  by_cases hx : x = 0
  · subst x
    rw [returnCost, if_pos rfl]
    symm
    simpa [returnIntegrand, UV.VerifyVisitGamma.normalTimeIntegrand] using
      UV.VerifyVisitGamma.normal_time_zero_cost 0 hT
  · rw [returnCost, if_neg hx, ← (return_integral_exact hT hx).2,
      ofReal_integral_eq_lintegral_ofReal (return_integral_exact hT hx).1]
    exact Eventually.of_forall fun t => div_nonneg (Real.exp_nonneg _) (sq_nonneg t)

private theorem cutoff_visit_time {δ T : ℝ} (hδ : 0 < δ) (hδT : δ ≤ T) (x : ℝ) :
    ENNReal.ofReal (visitCutoff δ T x) = ENNReal.ofReal (1 / (2 * Real.pi)) *
      ∫⁻ t in Ioc δ T, ENNReal.ofReal (returnIntegrand x t) := by
  obtain ⟨hi, hv⟩ := visit_cutoff_exact hδ hδT x
  rw [hv, ENNReal.ofReal_mul (by positivity), ofReal_integral_eq_lintegral_ofReal hi]
  exact Eventually.of_forall fun t => div_nonneg (Real.exp_nonneg _) (sq_nonneg t)

theorem cutoff_visit_antitone {δ η T : ℝ} (hδ : 0 < δ) (hδη : δ ≤ η) (hη : η ≤ T)
    (x : ℝ) : ENNReal.ofReal (visitCutoff η T x) ≤ ENNReal.ofReal (visitCutoff δ T x) := by
  rw [cutoff_visit_time (hδ.trans_le hδη) hη, cutoff_visit_time hδ (hδη.trans hη)]
  exact mul_le_mul_left' (lintegral_mono' (Measure.restrict_mono (Ioc_subset_Ioc_left hδη)
    le_rfl) le_rfl) _

theorem cutoff_visit_le_uncut {T δ : ℝ} (hδ : 0 < δ) (hδT : δ ≤ T) (x : ℝ) :
    ENNReal.ofReal (visitCutoff δ T x) ≤ uncutVisit T x := by
  rw [cutoff_visit_time hδ hδT, uncut_visit_time (hδ.trans_le hδT)]
  exact mul_le_mul_left' (lintegral_mono' (Measure.restrict_mono (Ioc_subset_Ioc_left hδ.le)
    le_rfl) le_rfl) _

/-- Every decreasing positive cutoff exhaustion recovers the full
proper-time cost, including the infinite coincident value. -/
theorem cutoff_visit_isup {T : ℝ} (hT : 0 < T) {δ : ℕ → ℝ}
    (hδ : ∀ n, 0 < δ n) (hδT : ∀ n, δ n ≤ T) (hmono : Antitone δ)
    (hlim : Tendsto δ atTop (𝓝 0)) (x : ℝ) :
    Monotone (fun n => ENNReal.ofReal (visitCutoff (δ n) T x)) ∧
      (⨆ n, ENNReal.ofReal (visitCutoff (δ n) T x)) = uncutVisit T x := by
  let g := fun t => ENNReal.ofReal (returnIntegrand x t)
  let f := fun n : ℕ => (Ioc (δ n) T).indicator g
  let c := ENNReal.ofReal (1 / (2 * Real.pi))
  have hg : Measurable g := by unfold g returnIntegrand; fun_prop
  have hf : ∀ n, Measurable (f n) := fun _ => hg.indicator measurableSet_Ioc
  have hfm : Monotone f := fun _ _ h _ =>
    indicator_le_indicator_of_subset (Ioc_subset_Ioc_left (hmono h)) (fun _ => zero_le _) _
  have hcut (n : ℕ) : ENNReal.ofReal (visitCutoff (δ n) T x) = c * ∫⁻ t, f n t := by
    rw [cutoff_visit_time (hδ n) (hδT n)]
    unfold f
    rw [lintegral_indicator measurableSet_Ioc]
  have hsup : (fun t => ⨆ n, f n t) = (Ioc (0 : ℝ) T).indicator g := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) T
    · rw [indicator_of_mem ht]
      refine le_antisymm (iSup_le fun n => indicator_le_self' (fun _ _ => zero_le _) _) ?_
      obtain ⟨n, hn⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds ht.1))
      have he := le_iSup (fun n => f n t) n
      simpa only [f, indicator_of_mem (show t ∈ Ioc (δ n) T from ⟨hn n le_rfl, ht.2⟩)] using he
    · rw [indicator_of_notMem ht]
      apply iSup_eq_bot.mpr
      intro n
      exact indicator_of_notMem (fun hn : t ∈ Ioc (δ n) T => ht ⟨(hδ n).trans hn.1, hn.2⟩) _
  constructor
  · intro n m hn
    simp_rw [hcut]
    exact mul_le_mul_left' (lintegral_mono (hfm hn)) _
  · simp_rw [hcut]
    rw [← ENNReal.mul_iSup, ← lintegral_iSup hf hfm, hsup,
      lintegral_indicator measurableSet_Ioc, uncut_visit_time hT]

theorem cutoff_visit_moment_tendsto {T : ℝ} (hT : 0 < T) {δ : ℕ → ℝ}
    (hδ : ∀ n, 0 < δ n) (hδT : ∀ n, δ n ≤ T) (hmono : Antitone δ)
    (hlim : Tendsto δ atTop (𝓝 0)) (μ : Measure ℝ) (p : ℕ) :
    Tendsto (fun n => ∫⁻ x, (ENNReal.ofReal (visitCutoff (δ n) T x)) ^ p ∂μ) atTop
      (𝓝 (∫⁻ x, uncutVisit T x ^ p ∂μ)) := by
  refine lintegral_tendsto_of_tendsto_of_monotone
    (fun n => ((visit_cutoff_measurable _ _).ennreal_ofReal.pow_const _).aemeasurable)
    (Eventually.of_forall fun x a b hab =>
      pow_le_pow_left' ((cutoff_visit_isup hT hδ hδT hmono hlim x).1 hab) p) ?_
  apply Eventually.of_forall
  intro x
  obtain ⟨hm, hi⟩ := cutoff_visit_isup hT hδ hδT hmono hlim x
  exact ((ENNReal.continuous_pow p).tendsto _).comp
    (hi ▸ tendsto_atTop_iSup hm)

theorem uncut_visit_first_moment {T : ℝ} (hT : 0 < T) (μ : Measure ℝ) [SFinite μ] :
    (∫⁻ x, uncutVisit T x ∂μ) = integratedNormalReturn T μ := by
  rw [integratedNormalReturn_eq hT]
  unfold uncutVisit
  rw [lintegral_const_mul]
  unfold returnCost
  refine Measurable.ite (measurableSet_singleton _) measurable_const ?_
  fun_prop

theorem eventually_positive_visit_cutoff {T : ℝ} (hT : 0 < T) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ ≤ T := by
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ)),
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hT)] with δ hδ hδT
  exact ⟨hδ, hδT.le⟩

/-- The first and higher moments converge through all positive cutoff
depths as the depth tends down to zero. -/
theorem cutoff_visit_moment_tendsto_right {T : ℝ} (hT : 0 < T) (μ : Measure ℝ) (p : ℕ) :
    Tendsto (fun δ => ∫⁻ x, (ENNReal.ofReal (visitCutoff δ T x)) ^ p ∂μ) (𝓝[>] 0)
      (𝓝 (∫⁻ x, uncutVisit T x ^ p ∂μ)) := by
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 1)
  have hd (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity
  have hδ (n : ℕ) : 0 < δ n := div_pos hT (hd n)
  have hδT (n : ℕ) : δ n ≤ T := by
    apply (div_le_iff₀ (hd n)).mpr
    nth_rw 1 [← mul_one T]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Nat.cast_nonneg _)) hT.le
  have hm : Antitone δ := fun i j hij =>
    div_le_div_of_nonneg_left hT.le (hd i) (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hdlim : Tendsto δ atTop (𝓝 0) := by
    convert tendsto_one_div_add_atTop_nhds_zero_nat.const_mul T using 1
    · funext n
      unfold δ
      rw [← mul_div_assoc, mul_one]
    · rw [mul_zero]
  have hlim := cutoff_visit_moment_tendsto hT hδ hδT hm hdlim μ p
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨n, hn⟩ := ((tendsto_order.mp hlim).1 a ha).exists
    filter_upwards [eventually_positive_visit_cutoff hT,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (hδ n))] with η hη hηn
    refine hn.trans_le (lintegral_mono fun x => ?_)
    exact pow_le_pow_left' (cutoff_visit_antitone hη.1 hηn.le (hδT n) x) p
  · intro a ha
    filter_upwards [eventually_positive_visit_cutoff hT] with η hη
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) ha
    exact pow_le_pow_left' (cutoff_visit_le_uncut hη.1 hη.2 x) p

end UV.ContinueVisitCutoffLimit
