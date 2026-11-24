import UV.ContinueSewnAnalyticVolume
import UV.ContinueSewnFlagEndpoint
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Positive sublevel exponents on compact analytic charts yield every finite
logarithmic moment, including against the full paired density in `Lᵖ`. -/

noncomputable section
open Real Set Filter MeasureTheory
open scoped ENNReal Topology
namespace UV.SewnFlags

/-- On the compact coordinate region one common positive exponent works for
the chosen nonidentity component, even when the order of its zeros varies. -/
theorem analytic_compact_power_volume {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {U K : Set E} {f : E → ℝ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (ha : AnalyticOnNhd ℝ f U) (hnon : ¬ EqOn f 0 U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (C : ℝ≥0∞) (b : ℝ), C < ⊤ ∧ 0 < b ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      volume.restrict K {z | |f z| < r} ≤ C * ENNReal.ofReal (r ^ b) := by
  classical
  choose B C b hB hC hb hpow using
    fun x : K => analytic_local_power_volume hU hconn ha hnon (hKU x.property)
  obtain ⟨s,hcov⟩ := hK.elim_nhds_subcover' (fun x hx => B ⟨x,hx⟩) (fun x hx => hB ⟨x,hx⟩)
  by_cases hs : s.Nonempty
  · refine ⟨∑ x ∈ s, C x,s.inf' hs b,ENNReal.sum_lt_top.mpr (fun i _ => hC i),
      (Finset.lt_inf'_iff hs).mpr (fun i _ => hb i),?_⟩
    intro r hr hr₁
    rw [Measure.restrict_apply' hK.isClosed.measurableSet, Finset.sum_mul]
    calc
      _ ≤ volume (⋃ i ∈ s, {z ∈ B i | |f z| < r}) := by
        apply measure_mono; intro z hz
        obtain ⟨i,hi,hi'⟩ := mem_iUnion₂.mp (hcov hz.2)
        exact mem_iUnion₂.mpr ⟨i,hi,hi',hz.1⟩
      _ ≤ ∑ i ∈ s, volume {z ∈ B i | |f z| < r} := measure_biUnion_finset_le _ _
      _ ≤ _ := Finset.sum_le_sum (fun i hi => (hpow i r hr hr₁).trans
        (mul_le_mul_left' (ENNReal.ofReal_le_ofReal (rpow_le_rpow_of_exponent_ge hr hr₁
          (Finset.inf'_le b hi))) _))
  · have hKe : K = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty.mp hs] using hcov
    exact ⟨0,1,by simp,zero_lt_one,by simp [hKe]⟩

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The coincidence set is genuinely null. This matters since the displacement
cost in the UV estimate is infinite at zero. -/
theorem ae_nonzero_of_power_sublevels (f : X → ℝ) {C : ℝ≥0∞} {b : ℝ}
    (hC : C < ⊤) (hb : 0 < b)
    (hsub : ∀ r : ℝ, 0 < r → r ≤ 1 → μ {x | |f x| < r} ≤ C * ENNReal.ofReal (r^b)) :
    ∀ᵐ x ∂μ, f x ≠ 0 := by
  rw [ae_iff]; simp only [not_not]
  apply le_antisymm _ (zero_le _)
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (r^b)) (𝓝[>] 0) (𝓝 0) := by
    have ht : ContinuousAt (fun r : ℝ => ENNReal.ofReal (r^b)) 0 :=
      ENNReal.continuous_ofReal.continuousAt.comp (continuousAt_id.rpow_const (Or.inr hb.le))
    simpa [zero_rpow hb.ne'] using ht.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  have hlim' := ENNReal.Tendsto.const_mul hlim (Or.inr hC.ne)
  simp only [mul_zero] at hlim'
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim'
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (zero_lt_one : (0:ℝ) < 1)).filter_mono
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)] with r hr hr'
  exact (measure_mono (fun x hx => by simpa [show f x = 0 from hx] using (show 0 < r from hr))).trans
    (hsub r hr hr'.le)

private theorem log_power_of_sublevels (f : X → ℝ) (hf : AEMeasurable f μ)
    {C : ℝ≥0∞} {b : ℝ} (hC : C < ⊤) (hb : 0 < b)
    (hsub : ∀ r : ℝ, 0 < r → r ≤ 1 → μ {x | |f x| < r} ≤ C * ENNReal.ofReal (r^b))
    {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, ENNReal.ofReal ((max 0 (-log |f x|))^p) ∂μ) < ⊤ := by
  let L (x : X) := max 0 (-log |f x|)
  have hL : AEMeasurable L μ := aemeasurable_const.max (Real.measurable_log.comp_aemeasurable (continuous_abs.measurable.comp_aemeasurable hf)).neg
  have htail (t : ℝ) (ht : 0 < t) : μ {x | t < L x} ≤ C * ENNReal.ofReal (exp (-b*t)) := by
    have h := hsub (exp (-t)) (exp_pos _) (exp_le_one_iff.mpr (by linarith))
    rw [← exp_mul, show -t*b = -b*t by ring] at h
    apply le_trans (measure_mono ?_) h
    intro x hx
    have hlog : log |f x| < -t := by
      have hmax : t < max 0 (-log |f x|) := hx
      rcases lt_max_iff.mp hmax with h₀ | hh
      · linarith
      · linarith
    by_cases hz : f x = 0
    · simp [hz,exp_pos]
    · exact (log_lt_iff_lt_exp (abs_pos.mpr hz)).mp hlog
  change (∫⁻ x, ENNReal.ofReal (L x^p) ∂μ) < ⊤
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul μ (f := L) (ae_of_all _ (fun x => le_max_left _ _)) hL hp]
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  let G (t : ℝ) := t^(p-1)*exp (-b*t)
  have hG : IntegrableOn G (Ioi 0) := by
    simpa [G] using integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < p-1) (le_refl (1:ℝ)) hb
  have hGfin : (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (G t)) < ⊤ := by
    apply (hasFiniteIntegral_iff_ofReal ?_).mp hG.hasFiniteIntegral
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (rpow_nonneg ht.le _) (exp_pos _).le
  calc
    _ ≤ ∫⁻ t in Ioi (0:ℝ), C * ENNReal.ofReal (G t) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      calc
        _ ≤ (C * ENNReal.ofReal (exp (-b*t))) * ENNReal.ofReal (t^(p-1)) :=
          mul_le_mul_right' (htail t ht) _
        _ = _ := by rw [mul_assoc, ← ENNReal.ofReal_mul (exp_pos _).le]; congr 2; exact mul_comm _ _
    _ = _ := lintegral_const_mul' _ _ hC.ne
    _ < ⊤ := ENNReal.mul_lt_top hC hGfin

/-- The ordinary real representative of the one-face logarithmic majorant
belongs to every finite positive `Lᵖ` space. -/
private theorem memLp_marginal_component [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : AEMeasurable f μ) {C : ℝ≥0∞} {b : ℝ} (hC : C < ⊤) (hb : 0 < b)
    (hsub : ∀ r : ℝ, 0 < r → r ≤ 1 → μ {x | |f x| < r} ≤ C * ENNReal.ofReal (r^b))
    {p : ℝ} (hp : 0 < p) :
    MemLp (fun x => 1 + max 0 (-log |f x|)) (ENNReal.ofReal p) μ := by
  let L (x : X) := max 0 (-log |f x|)
  have hm : AEMeasurable L μ := aemeasurable_const.max
    (Real.measurable_log.comp_aemeasurable (continuous_abs.measurable.comp_aemeasurable hf)).neg
  have hLp : MemLp L (ENNReal.ofReal p) μ := by
    refine ⟨hm.aestronglyMeasurable, (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top).mpr ?_⟩
    rw [ENNReal.toReal_ofReal hp.le]
    have h := log_power_of_sublevels f hf hC hb hsub hp
    simpa only [L,Real.enorm_of_nonneg (le_max_left (0:ℝ) _),
      ENNReal.ofReal_rpow_of_nonneg (le_max_left (0:ℝ) _) hp.le] using h
  exact (memLp_const (1:ℝ)).add hLp

private theorem memLp_product_all {ι : Type*} [IsFiniteMeasure μ]
    (s : Finset ι) (g : ι → X → ℝ)
    (hg : ∀ i ∈ s, ∀ p : ℝ, 0 < p → MemLp (g i) (ENNReal.ofReal p) μ) :
    ∀ p : ℝ, 0 < p → MemLp (fun x => ∏ i ∈ s, g i x) (ENNReal.ofReal p) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => intro p _; simpa using (memLp_const (μ := μ) (p := ENNReal.ofReal p) (1:ℝ))
  | @insert i s hi ih =>
    intro p hp
    have hp' : 0 < 2*p := by positivity
    have ht : Real.HolderTriple (2*p) (2*p) p :=
      ⟨by field_simp; ring, hp', hp'⟩
    letI := ht.ennrealOfReal
    have ha := hg i (Finset.mem_insert_self ..) _ hp'
    have hb := ih (fun j hj => hg j (Finset.mem_insert_of_mem hj)) _ hp'
    simpa only [Finset.prod_insert hi] using hb.mul' ha

/-- All marginal factors may use the very same chart variables and a complex
paired density. A chosen component can be any component whose absolute value
is bounded by the projected Euclidean displacement norm. Repetitions in the
list of faces give arbitrary finite powers. -/
theorem analytic_chart_weighted_joint_marginals {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {U K : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hK : IsCompact K) (hKU : K ⊆ U) {ι : Type*} [Fintype ι]
    (f : ι → E → ℝ) (ha : ∀ i, AnalyticOnNhd ℝ (f i) U) (hnon : ∀ i, ¬ EqOn (f i) 0 U)
    (radius : ι → E → ℝ) (hcomponent : ∀ i, ∀ x ∈ K, |f i x| ≤ radius i x)
    {p : ℝ} (hp : 1 < p) (w : E → ℂ) (hw : MemLp w (ENNReal.ofReal p) (volume.restrict K)) :
    (∫⁻ x in K, ‖w x‖ₑ * ∏ i, displacementCost 0 (radius i x)) < ⊤ := by
  let μ : Measure E := volume.restrict K
  letI : IsFiniteMeasure μ := ⟨by simpa [μ] using hK.measure_lt_top (μ := volume)⟩
  let L (i : ι) (x : E) := 1 + max 0 (-log |f i x|)
  have hpos (i : ι) (x : E) : 0 ≤ L i x := by dsimp [L]; linarith [le_max_left 0 (-log |f i x|)]
  have hfm (i : ι) : AEMeasurable (f i) μ := by
    apply ContinuousOn.aemeasurable _ hK.isClosed.measurableSet
    exact fun x hx => (ha i x (hKU hx)).continuousAt.continuousWithinAt
  choose C b hC hb hsub using (fun i => analytic_compact_power_volume hU hconn (ha i) (hnon i) hK hKU)
  have hLp (i : ι) (q : ℝ) (hq : 0 < q) : MemLp (L i) (ENNReal.ofReal q) μ :=
    memLp_marginal_component (f i) (hfm i) (hC i) (hb i) (hsub i) hq
  have hconj := Real.HolderConjugate.conjExponent hp
  letI := hconj.ennrealOfReal
  have hj := memLp_product_all Finset.univ L (fun i _ => hLp i) _ hconj.symm.pos
  have hint : Integrable (fun x => ‖w x‖ * ∏ i, L i x) μ := memLp_one_iff_integrable.mp (hj.mul' hw.norm)
  have hnz : ∀ᵐ x ∂μ, ∀ i, f i x ≠ 0 := ae_all_iff.mpr fun i =>
    ae_nonzero_of_power_sublevels (f i) (hC i) (hb i) (hsub i)
  refine (lintegral_mono_ae (g := fun x => ‖‖w x‖ * ∏ i, L i x‖ₑ) ?_).trans_lt hint.hasFiniteIntegral
  filter_upwards [hnz, ae_restrict_mem hK.isClosed.measurableSet] with x hx hxK
  rw [enorm_mul, enorm_norm, Real.enorm_of_nonneg (Finset.prod_nonneg (fun i _ => hpos i x)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => hpos i x)]
  apply mul_le_mul_left'
  apply Finset.prod_le_prod'
  intro i _
  have hfi : 0 < |f i x| := abs_pos.mpr (hx i)
  have hrad := hcomponent i x hxK
  have hr := hfi.trans_le hrad
  rw [displacementCost, if_neg (lt_irrefl _), if_neg hr.ne', if_pos rfl]
  rw [one_div,log_inv]
  exact ENNReal.ofReal_le_ofReal (add_le_add_left (max_le_max_left _ (neg_le_neg (log_le_log hfi hrad))) _)

end UV.SewnFlags
