import UV.ContinueSewnFlagLogKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Uniform logarithmic asymptotics at coincidence for the normalized
marginal Bessel kernel, including the physical argument μ|d|. -/

noncomputable section
open MeasureTheory Real Filter Set
open scoped ENNReal Interval
namespace UV.SewnFlags

open UV.RevisionJointHeat

private theorem unit_selector_eq (a t : ℝ) :
    selectorDensity 1 a 0 t = exp (-(t+a/t))/t := by
  simp [selectorDensity,rpow_neg_one,div_eq_mul_inv,mul_comm]

private theorem unit_selector_nonneg (a : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ selectorDensity 1 a 0 t := by
  rw [unit_selector_eq]
  exact div_nonneg (exp_pos _).le ht.le

private theorem unit_selector_small {a : ℝ} (ha : 0 < a) {t : ℝ} (ht : 0 < t) :
    selectorDensity 1 a 0 t ≤ a⁻¹ := by
  rw [unit_selector_eq]
  have he : exp (-(t+a/t)) ≤ exp (-(a/t)) := exp_le_exp.mpr (by linarith)
  refine (div_le_div_of_nonneg_right he ht.le).trans ?_
  rw [exp_neg]
  have h := add_one_le_exp (a/t)
  have hf : a/t ≤ exp (a/t) := by linarith
  have hmul := (div_le_iff₀ ht).1 hf
  apply (div_le_iff₀ ht).2
  apply (inv_le_iff_one_le_mul₀ (exp_pos _)).2
  rw [← div_eq_inv_mul,div_mul_eq_mul_div]
  exact (one_le_div ha).2 (by simpa [mul_comm] using hmul)

private theorem unit_selector_large {a : ℝ} (ha : 0 ≤ a) {t : ℝ} (ht : 1 < t) :
    selectorDensity 1 a 0 t ≤ exp (-t) := by
  rw [unit_selector_eq]
  have he : exp (-(t+a/t)) ≤ exp (-t) :=
    exp_le_exp.mpr (by linarith [div_nonneg ha (zero_lt_one.trans ht).le])
  exact (div_le_div_of_nonneg_right he (zero_lt_one.trans ht).le).trans (div_le_self (exp_pos _).le ht.le)

private theorem unit_selector_middle {a : ℝ} (ha : 0 ≤ a) {t : ℝ} (ht : 0 < t) :
    1/t - (1+a/(t^2)) ≤ selectorDensity 1 a 0 t ∧
      selectorDensity 1 a 0 t ≤ 1/t := by
  rw [unit_selector_eq]
  constructor
  · have he := add_one_le_exp (-(t+a/t))
    apply (le_div_iff₀ ht).2
    have h : (1/t - (1+a/t^2))*t = 1-(t+a/t) := by
      field_simp [ht.ne']
    rw [h]
    linarith
  · apply div_le_div_of_nonneg_right _ ht.le
    exact exp_le_one_iff.mpr (neg_nonpos.mpr (add_nonneg ht.le (div_nonneg ha ht.le)))

private theorem unit_selector_log {a : ℝ} (ha : 0 < a) (h₁ : a ≤ 1) :
    |selectorZ 1 a 0 - log (1/a)| ≤ 2 := by
  let f := selectorDensity 1 a 0
  have hi : IntegrableOn f (Ioi 0) := selectorDensity_integrable zero_lt_one ha 0
  have hm : Icc a 1 ⊆ Ioi (0:ℝ) := fun _ hu => ha.trans_le hu.1
  have ht : Ioi (1:ℝ) ⊆ Ioi 0 := fun _ h => mem_Ioi.mpr (zero_lt_one.trans (mem_Ioi.mp h))
  have hlo : 0 ≤ ∫ t in Ioo (0:ℝ) a, f t :=
    setIntegral_nonneg measurableSet_Ioo fun _ h => unit_selector_nonneg a h.1
  have hhi : 0 ≤ ∫ t in Ioi (1:ℝ), f t :=
    setIntegral_nonneg measurableSet_Ioi fun _ h => unit_selector_nonneg a (ht h)
  have hsmall : (∫ t in Ioo (0:ℝ) a, f t) ≤ 1 := by
    calc
      _ ≤ ∫ _ in Ioo (0:ℝ) a, a⁻¹ := by
        exact setIntegral_mono_on (hi.mono_set Ioo_subset_Ioi_self)
          (integrable_const (μ := volume.restrict (Ioo 0 a)) _) measurableSet_Ioo
          (fun _ h => unit_selector_small ha h.1)
      _ = _ := by simp [Measure.real,Real.volume_Ioo,ha.le,mul_inv_cancel₀ ha.ne']
  have hlarge : (∫ t in Ioi (1:ℝ), f t) ≤ 1 := by
    have hI : IntegrableOn (fun t : ℝ => exp (-t)) (Ioi 1) := by
      simpa [neg_mul] using integrableOn_exp_mul_Ioi (show (-1:ℝ)<0 by norm_num) 1
    calc
      _ ≤ ∫ t in Ioi (1:ℝ), exp (-t) := setIntegral_mono_on (hi.mono_set ht) hI measurableSet_Ioi
        (fun _ h => unit_selector_large ha.le h)
      _ = exp (-1) := by
        simpa [neg_mul] using integral_exp_mul_Ioi (show (-1:ℝ)<0 by norm_num) 1
      _ ≤ 1 := exp_le_one_iff.mpr (by norm_num)
  let g := fun t : ℝ => 1/t
  let e := fun t : ℝ => 1+a/t^2
  have hg : IntegrableOn g (Icc a 1) :=
    (continuousOn_const.div continuousOn_id (fun _ h => (hm h).ne')).integrableOn_compact isCompact_Icc
  have he : IntegrableOn e (Icc a 1) :=
    (continuousOn_const.add (continuousOn_const.div (continuousOn_id.pow 2)
      (fun _ h => pow_ne_zero _ (hm h).ne'))).integrableOn_compact isCompact_Icc
  have hlog : (∫ t in Icc a 1, g t) = log (1/a) := by
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le h₁]
    exact integral_one_div_of_pos ha zero_lt_one
  have hE : (∫ t in Icc a 1, e t) ≤ 2 := by
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le h₁]
    have hD (t : ℝ) (ht : t ∈ [[a,1]]) : HasDerivAt (fun t => t-a/t) (e t) t := by
      rw [uIcc_of_le h₁] at ht
      have ht₀ : t ≠ 0 := (hm ht).ne'
      convert (hasDerivAt_id t).sub ((hasDerivAt_const t a).div (hasDerivAt_id t) ht₀) using 1
      simp [e,neg_div]
    have hEI := (intervalIntegrable_iff_integrableOn_Ioc_of_le h₁).2 (he.mono_set Ioc_subset_Icc_self)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hD hEI]
    simp only [div_one,div_self ha.ne']
    linarith
  have hmiddle₁ : (∫ t in Icc a 1, f t) ≤ log (1/a) := by
    rw [← hlog]
    exact setIntegral_mono_on (hi.mono_set hm) hg measurableSet_Icc
      (fun _ h => (unit_selector_middle ha.le (hm h)).2)
  have hmiddle₂ : log (1/a)-2 ≤ ∫ t in Icc a 1, f t := by
    have h := setIntegral_mono_on (hg.sub he) (hi.mono_set hm) measurableSet_Icc
      (fun _ h => (unit_selector_middle ha.le (hm h)).1)
    change (∫ t in Icc a 1, g t-e t) ≤ _ at h
    rw [integral_sub hg he,hlog] at h
    linarith
  have hsplit : Ioi (0:ℝ) = Ioo 0 a ∪ (Icc a 1 ∪ Ioi 1) := by
    ext t; simp only [mem_Ioi,mem_union,mem_Ioo,mem_Icc]; constructor
    · intro h
      by_cases ha' : t < a
      · exact Or.inl ⟨h,ha'⟩
      · by_cases ht' : t ≤ 1
        · exact Or.inr (Or.inl ⟨le_of_not_gt ha',ht'⟩)
        · exact Or.inr (Or.inr (lt_of_not_ge ht'))
    · rintro (h|h|h)
      · exact h.1
      · exact ha.trans_le h.1
      · exact zero_lt_one.trans h
  have hdisj : Disjoint (Icc a 1) (Ioi (1:ℝ)) :=
    disjoint_left.mpr (fun _ h k => not_lt_of_ge h.2 k)
  have hdisj' : Disjoint (Ioo 0 a) (Icc a 1 ∪ Ioi (1:ℝ)) := by
    refine disjoint_left.mpr (fun t h k => ?_)
    rcases k with k | k
    · exact not_lt_of_ge k.1 h.2
    · exact not_lt_of_ge (h.2.le.trans h₁) k
  unfold selectorZ
  change |(∫ t in Ioi (0:ℝ), f t) - log (1/a)| ≤ 2
  have hsplitI : (∫ t in Ioi (0:ℝ), f t) =
      (∫ t in Ioo (0:ℝ) a,f t) + ((∫ t in Icc a 1,f t) + ∫ t in Ioi (1:ℝ),f t) := by
    rw [hsplit,setIntegral_union hdisj' (measurableSet_Icc.union measurableSet_Ioi)
      (hi.mono_set Ioo_subset_Ioi_self) (hi.mono_set (union_subset hm ht)),
      setIntegral_union hdisj measurableSet_Ioi (hi.mono_set hm) (hi.mono_set ht)]
  rw [hsplitI,abs_le]
  constructor <;> linarith

theorem logKernel_antitone (μ : ℝ) : AntitoneOn (logKernel μ) (Ici 0) := by
  intro x hx y hy hxy
  rw [logKernel_proper_time,logKernel_proper_time]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hp : 0 < t := ht
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (mul_nonneg (sq_nonneg _) hp.le)
  apply exp_le_exp.mpr
  have hq := div_le_div_of_nonneg_right ((sq_le_sq₀ hx hy).2 hxy) (by positivity : 0 ≤ 4*t)
  linarith

/-- With positive mass, the logarithmic remainder at small positive
separation is uniformly bounded in the complete physical argument μx. -/
theorem logKernel_log_remainder {μ x : ℝ} (hμ : 0 < μ) (hx : 0 < x) (hz : μ*x ≤ 2) :
    |(logKernel μ x).toReal - log (1/(μ*x))/(8*π^2)| ≤ (2+log 4)/(16*π^2) := by
  let z := μ*x
  let a := z^2/4
  have hz₀ : 0 < z := mul_pos hμ hx
  have ha : 0 < a := by unfold a; positivity
  have ha₁ : a ≤ 1 := by
    have h := (sq_le_sq₀ hz₀.le (by norm_num : (0:ℝ) ≤ 2)).2 hz
    unfold a
    linarith
  have hc : logKernel μ x = logKernel 1 z := by
    rw [logKernel_bessel hμ hx,logKernel_bessel zero_lt_one hz₀,one_mul]
  have hInt := selectorDensity_integrable zero_lt_one ha 0
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] selectorDensity 1 a 0 :=
    (ae_restrict_mem measurableSet_Ioi).mono (fun _ h => unit_selector_nonneg a h)
  have hZ : 0 ≤ selectorZ 1 a 0 := setIntegral_nonneg measurableSet_Ioi (fun _ h => unit_selector_nonneg a h)
  have hval : (logKernel μ x).toReal = selectorZ 1 a 0/(16*π^2) := by
    rw [hc,logKernel,one_pow]
    change (ENNReal.ofReal (((4*π)^2)⁻¹) * ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (selectorDensity 1 a 0 t)).toReal = _
    rw [← ofReal_integral_eq_lintegral_ofReal hInt hnonneg,← selectorZ,
      ← ENNReal.ofReal_mul (by positivity),ENNReal.toReal_ofReal (by positivity)]
    ring
  have hlog : log (1/a) = 2*log (1/z)+log 4 := by
    rw [one_div,log_inv,log_div (pow_ne_zero _ hz₀.ne') (by norm_num),log_pow,one_div,log_inv]
    push_cast
    ring
  have hcore := (abs_le.mp (unit_selector_log ha ha₁))
  rw [hlog] at hcore
  rw [hval]
  change |selectorZ 1 a 0/(16*π^2)-log (1/z)/(8*π^2)| ≤ _
  rw [show selectorZ 1 a 0/(16*π^2)-log (1/z)/(8*π^2) =
    (selectorZ 1 a 0-2*log (1/z))/(16*π^2) by ring,abs_div,abs_of_pos (by positivity : 0<16*π^2)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h4 : 0 ≤ log (4:ℝ) := log_nonneg (by norm_num)
  exact abs_le.mpr ⟨by linarith [hcore.1],by linarith [hcore.2]⟩

end UV.SewnFlags
