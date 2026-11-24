import UV.ContinueSewnFlagLogFourier

/-! The nonnegative characteristic of a finite positive joint measure
can be integrated against all marginal resolvents before the positive
time and displacement integrals. -/

noncomputable section
open MeasureTheory Real Filter Set
open scoped ENNReal BigOperators RealInnerProductSpace
namespace UV.SewnFlags

def marginalPhase {ι : Type*} [Fintype ι] (q d : ι → ScalarMomentum) : ℂ :=
  ∏ i, stableFourierPhase (d i) (q i)

def weightedMarginalCharacteristic {ι : Type*} [Fintype ι] (μ : Measure (ι → ScalarMomentum))
    (w : (ι → ScalarMomentum) → ℂ) (q : ι → ScalarMomentum) : ℝ :=
  (∫ d, w d * marginalPhase q d ∂μ).re

def marginalCharacteristic {ι : Type*} [Fintype ι] (μ : Measure (ι → ScalarMomentum))
    (q : ι → ScalarMomentum) : ℝ :=
  (∫ d, marginalPhase q d ∂μ).re

theorem marginalPhase_measurable {ι : Type*} [Fintype ι] :
    Measurable (fun q : (ι → ScalarMomentum) × (ι → ScalarMomentum) => marginalPhase q.1 q.2) := by
  let f := fun (i : ι) (q : (ι → ScalarMomentum) × (ι → ScalarMomentum)) =>
    stableFourierPhase (q.2 i) (q.1 i)
  have h (i : ι) : Measurable (f i) := by
    have h₁ : Continuous (fun q : (ι → ScalarMomentum) × (ι → ScalarMomentum) => q.1 i) :=
      (continuous_apply i).comp continuous_fst
    have h₂ : Continuous (fun q : (ι → ScalarMomentum) × (ι → ScalarMomentum) => q.2 i) :=
      (continuous_apply i).comp continuous_snd
    have he : Continuous (fun q : (ι → ScalarMomentum) × (ι → ScalarMomentum) =>
        Complex.exp (Complex.I * (⟪q.2 i,q.1 i⟫:ℝ))) :=
      Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (h₂.inner h₁)))
    exact he.measurable
  exact Finset.measurable_prod (f := f) Finset.univ (fun i _ => h i)

private theorem weightedMarginalCharacteristic_measurable {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ScalarMomentum)) [IsFiniteMeasure μ] (w : (ι → ScalarMomentum) → ℂ)
    (hw : Measurable w) : Measurable (weightedMarginalCharacteristic μ w) :=
  Complex.measurable_re.comp ((hw.comp measurable_snd).mul
    marginalPhase_measurable).stronglyMeasurable.integral_prod_right'.measurable

private theorem marginalPhase_norm {ι : Type*} [Fintype ι] (q d : ι → ScalarMomentum) :
    ‖marginalPhase q d‖ = 1 := by simp [marginalPhase,norm_prod,stableFourierPhase_norm]

private theorem weighted_marginal_fixed_time {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ScalarMomentum)) [IsFiniteMeasure μ] (m : ℝ)
    (w : (ι → ScalarMomentum) → ℂ) (hwm : Measurable w) (hww : ∀ d, ‖w d‖ ≤ 1)
    {t : ι → ℝ} (ht : ∀ i, 0 < t i) :
    let F := fun q : ι → ScalarMomentum => weightedMarginalCharacteristic μ w q *
      ∏ i, marginalSchwinger m (q i) (t i)
    let H := fun d : ι → ScalarMomentum => (w d).re * ∏ i, marginalHeat m (t i) ‖d i‖
    Integrable F ∧ Integrable H μ ∧ (∫ q, F q) = ∫ d, H d ∂μ := by
  let W := fun q : ι → ScalarMomentum => ∏ i, marginalSchwinger m (q i) (t i)
  let G := fun q : (ι → ScalarMomentum) × (ι → ScalarMomentum) =>
      (W q.1:ℂ) * (w q.2 * marginalPhase q.1 q.2)
  have hw (q : ι → ScalarMomentum) (i : ι) : 0 ≤ marginalSchwinger m (q i) (t i) := by
    unfold marginalSchwinger
    exact div_nonneg (mul_nonneg (ht i).le (exp_pos _).le) (by positivity)
  have hW₀ (q : ι → ScalarMomentum) : 0 ≤ W q := Finset.prod_nonneg fun i _ => hw q i
  have hW : Measurable W := by unfold W marginalSchwinger; fun_prop
  have hG : Measurable G := (hW.comp measurable_fst).complex_ofReal.mul
    ((hwm.comp measurable_snd).mul marginalPhase_measurable)
  have hWι (i : ι) : Integrable (fun q : ScalarMomentum => marginalSchwinger m q (t i)) := by
    have h := (marginal_fourier_integrable m (ht i) 0).norm
    exact h.congr (ae_of_all _ fun q => by
      dsimp only
      rw [norm_mul,stableFourierPhase_norm,mul_one,Complex.norm_real,Real.norm_of_nonneg]
      unfold marginalSchwinger
      exact div_nonneg (mul_nonneg (ht i).le (exp_pos _).le) (by positivity))
  have hIW : Integrable W := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun i q => marginalSchwinger m q (t i)) hWι
  have hphase (q : ι → ScalarMomentum) : Integrable (fun d => w d * marginalPhase q d) μ :=
    Integrable.of_bound (hwm.mul (marginalPhase_measurable.comp measurable_prodMk_left)).aestronglyMeasurable 1
      (ae_of_all _ fun d => by simp only [norm_mul,marginalPhase_norm,mul_one]; exact hww d)
  have hIq (q : ι → ScalarMomentum) : Integrable (fun d => G (q,d)) μ := by
    change Integrable (fun d => (W q:ℂ)*(w d * marginalPhase q d)) μ
    exact (hphase q).const_mul (W q:ℂ)
  have hI : Integrable G ((volume : Measure (ι → ScalarMomentum)).prod μ) := by
    refine (integrable_prod_iff hG.aestronglyMeasurable).2 ⟨ae_of_all _ hIq,?_⟩
    convert hIW.mul_const (∫ d, ‖w d‖ ∂μ) using 1
    ext q
    simp [G,marginalPhase_norm,Real.norm_of_nonneg (hW₀ q),integral_const_mul]
  have hq (q : ι → ScalarMomentum) :
      (∫ d, (G (q,d)).re ∂μ) = weightedMarginalCharacteristic μ w q * W q := by
    change (∫ d, RCLike.re (G (q,d)) ∂μ) = _
    rw [integral_re (hIq q)]
    change (∫ d, (W q:ℂ)*(w d * marginalPhase q d) ∂μ).re = _
    rw [integral_const_mul]
    simp [weightedMarginalCharacteristic,Complex.mul_re,mul_comm]
  have hprod (q d : ι → ScalarMomentum) :
      G (q,d) = w d * ∏ i, (marginalSchwinger m (q i) (t i):ℂ)*stableFourierPhase (d i) (q i) := by
    simp only [G,W,marginalPhase,Complex.ofReal_prod,Finset.prod_mul_distrib]
    ring
  have hId (d : ι → ScalarMomentum) : Integrable (fun q => G (q,d)) := by
    simp_rw [hprod]
    have h : Integrable (fun q : ι → ScalarMomentum =>
        ∏ i, (marginalSchwinger m (q i) (t i):ℂ)*stableFourierPhase (d i) (q i)) := by
      rw [volume_pi]
      exact Integrable.fintype_prod (f := fun i q => (marginalSchwinger m q (t i):ℂ)*stableFourierPhase (d i) q)
        (fun i => marginal_fourier_integrable m (ht i) (d i))
    exact h.const_mul (w d)
  have hd (d : ι → ScalarMomentum) :
      (∫ q, (G (q,d)).re) = (w d).re * ∏ i, marginalHeat m (t i) ‖d i‖ := by
    change (∫ q, RCLike.re (G (q,d))) = _
    rw [integral_re (hId d)]
    change (∫ q, G (q,d)).re = _
    simp_rw [hprod]
    rw [integral_const_mul,joint_marginal_fourier_gaussian m t ht d]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  have hRe : Integrable (fun q => (G q).re) ((volume : Measure (ι → ScalarMomentum)).prod μ) := hI.re
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hq] using hRe.integral_prod_left
  · simpa only [hd] using hRe.integral_prod_right
  · simpa only [hq,hd] using integral_integral_swap (f := fun q d => (G (q,d)).re) hRe

private theorem marginal_fixed_time_pairing {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ScalarMomentum)) [IsFiniteMeasure μ] (m : ℝ)
    (hC : ∀ q, 0 ≤ marginalCharacteristic μ q) {t : ι → ℝ} (ht : ∀ i, 0 < t i) :
    (∫⁻ q : ι → ScalarMomentum, ENNReal.ofReal (marginalCharacteristic μ q) *
      ∏ i, ENNReal.ofReal (marginalSchwinger m (q i) (t i))) =
      ∫⁻ d, ∏ i, ENNReal.ofReal (marginalHeat m (t i) ‖d i‖) ∂μ := by
  obtain ⟨hF,hH,hEq⟩ : Integrable (fun q => marginalCharacteristic μ q *
      ∏ i, marginalSchwinger m (q i) (t i)) ∧
      Integrable (fun d : ι → ScalarMomentum => ∏ i, marginalHeat m (t i) ‖d i‖) μ ∧
      (∫ q, marginalCharacteristic μ q * ∏ i, marginalSchwinger m (q i) (t i)) =
        ∫ d, ∏ i, marginalHeat m (t i) ‖d i‖ ∂μ := by
    simpa [weightedMarginalCharacteristic,marginalCharacteristic] using
      weighted_marginal_fixed_time μ m (fun _ => 1) measurable_const
        (fun _ => norm_one.le) ht
  have hw (q : ι → ScalarMomentum) (i : ι) : 0 ≤ marginalSchwinger m (q i) (t i) := by
    unfold marginalSchwinger
    exact div_nonneg (mul_nonneg (ht i).le (exp_pos _).le) (by positivity)
  have hH₀ (d : ι → ScalarMomentum) (i : ι) : 0 ≤ marginalHeat m (t i) ‖d i‖ := by
    unfold marginalHeat
    exact div_nonneg (exp_pos _).le (mul_nonneg (sq_nonneg _) (ht i).le)
  simp_rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => hw _ i),
    ← ENNReal.ofReal_mul (hC _),← ENNReal.ofReal_prod_of_nonneg (fun i _ => hH₀ _ i)]
  rw [← ofReal_integral_eq_lintegral_ofReal hF (ae_of_all _ fun q =>
        mul_nonneg (hC q) (Finset.prod_nonneg fun i _ => hw q i)),
    ← ofReal_integral_eq_lintegral_ofReal hH (ae_of_all _ fun d => Finset.prod_nonneg (fun i _ => hH₀ d i))]
  rw [hEq]

private def marginalTimeMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => volume.restrict (Ioi (0:ℝ)))

private instance (ι : Type*) [Fintype ι] : SigmaFinite (marginalTimeMeasure ι) := by
  unfold marginalTimeMeasure
  infer_instance

private theorem ae_marginal_time_pos (ι : Type*) [Fintype ι] :
    ∀ᵐ t ∂marginalTimeMeasure ι, ∀ i, 0 < t i :=
  eventually_all.2 (fun _ => Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem measurableSet_Ioi))

private theorem marginal_schwinger_time {ι : Type*} [Fintype ι] {m : ℝ} (hm : 0 < m)
    (C : (ι → ScalarMomentum) → ℝ) (hC : Measurable C) :
    (∫⁻ q : ι → ScalarMomentum, ENNReal.ofReal (C q) *
      ∏ i, ENNReal.ofReal (((m^2+‖q i‖^2)^2)⁻¹/(2*π)^4)) =
      ∫⁻ t, (∫⁻ q : ι → ScalarMomentum, ENNReal.ofReal (C q) *
        ∏ i, ENNReal.ofReal (marginalSchwinger m (q i) (t i))) ∂marginalTimeMeasure ι := by
  let f := fun q : (ι → ScalarMomentum) × (ι → ℝ) =>
    ENNReal.ofReal (C q.1) * ∏ i, ENNReal.ofReal (marginalSchwinger m (q.1 i) (q.2 i))
  have hf : Measurable f := (hC.comp measurable_fst).ennreal_ofReal.mul
    (Finset.measurable_prod _ fun i _ => by
      have hq := (measurable_pi_apply i).comp
        (measurable_fst : Measurable (Prod.fst : (ι → ScalarMomentum) × (ι → ℝ) → _))
      have ht := (measurable_pi_apply i).comp
        (measurable_snd : Measurable (Prod.snd : (ι → ScalarMomentum) × (ι → ℝ) → _))
      unfold marginalSchwinger
      fun_prop)
  let τ := marginalTimeMeasure ι
  calc
    _ = ∫⁻ q : (ι → ScalarMomentum), ∫⁻ t, f (q,t) ∂τ := by
      apply lintegral_congr
      intro q
      dsimp only [f,τ,marginalTimeMeasure]
      have h (i : ι) : Measurable (fun t => ENNReal.ofReal (marginalSchwinger m (q i) t)) := by
        unfold marginalSchwinger
        fun_prop
      have hW : Measurable (fun t : ι → ℝ => ∏ i, ENNReal.ofReal (marginalSchwinger m (q i) (t i))) :=
        Finset.measurable_prod _ fun i _ => (h i).comp (measurable_pi_apply i)
      rw [lintegral_const_mul _ hW, UV.network_lintegral_fintype_prod _
        (fun i t => ENNReal.ofReal (marginalSchwinger m (q i) t)) h]
      simp only [marginal_schwinger_lintegral hm]
    _ = _ := lintegral_lintegral_swap hf.aemeasurable

/-- The literal joint marginal-loop equality for a finite positive
displacement measure with nonnegative characteristic. The extended
positive integrals retain the value infinity. -/
theorem joint_marginal_log_energy {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ScalarMomentum)) [IsFiniteMeasure μ] {m : ℝ} (hm : 0 < m)
    (hC : ∀ q, 0 ≤ marginalCharacteristic μ q) :
    (∫⁻ q : ι → ScalarMomentum, ENNReal.ofReal (marginalCharacteristic μ q) *
      ∏ i, ENNReal.ofReal (((m^2+‖q i‖^2)^2)⁻¹/(2*π)^4)) =
      ∫⁻ d, ∏ i, logKernel m ‖d i‖ ∂μ := by
  let τ := marginalTimeMeasure ι
  let H := fun q : (ι → ℝ) × (ι → ScalarMomentum) =>
    ∏ i, ENNReal.ofReal (marginalHeat m (q.1 i) ‖q.2 i‖)
  have hCmeas : Measurable (marginalCharacteristic μ) := by
    have he : weightedMarginalCharacteristic μ (fun _ => 1) = marginalCharacteristic μ := by
      funext q
      simp [weightedMarginalCharacteristic,marginalCharacteristic]
    simpa only [he] using
      weightedMarginalCharacteristic_measurable μ (fun _ => 1) measurable_const
  have hH : Measurable H := by unfold H marginalHeat; fun_prop
  rw [marginal_schwinger_time hm _ hCmeas]
  calc
    _ = ∫⁻ t, ∫⁻ d, H (t,d) ∂μ ∂τ := by
      apply lintegral_congr_ae
      filter_upwards [ae_marginal_time_pos ι] with t ht'
      exact marginal_fixed_time_pairing μ m hC ht'
    _ = ∫⁻ d, ∫⁻ t, H (t,d) ∂τ ∂μ := lintegral_lintegral_swap hH.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro d
      exact joint_marginal_proper_time m d

/-- A measurable complex density of modulus at most one can be
included in the same joint pairing when the log-energy envelope is
integrable against the dominating positive measure. -/
theorem weighted_joint_marginal_log_energy {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ScalarMomentum)) [IsFiniteMeasure μ] {m : ℝ} (hm : 0 < m)
    (w : (ι → ScalarMomentum) → ℂ) (hwm : Measurable w) (hww : ∀ d, ‖w d‖ ≤ 1)
    (hC : ∀ q, 0 ≤ weightedMarginalCharacteristic μ w q)
    (hEnergy : (∫⁻ d, ∏ i, logKernel m ‖d i‖ ∂μ) < ⊤) :
    let A := ∫ d, (w d).re * (∏ i, logKernel m ‖d i‖).toReal ∂μ
    0 ≤ A ∧
      (∫⁻ q : ι → ScalarMomentum, ENNReal.ofReal (weightedMarginalCharacteristic μ w q) *
        ∏ i, ENNReal.ofReal (((m^2+‖q i‖^2)^2)⁻¹/(2*π)^4)) = ENNReal.ofReal A := by
  let τ := marginalTimeMeasure ι
  let H : (ι → ℝ) × (ι → ScalarMomentum) → ℝ :=
    fun p => ∏ i, marginalHeat m (p.1 i) ‖p.2 i‖
  let F : (ι → ℝ) × (ι → ScalarMomentum) → ℝ := fun p => (w p.2).re * H p
  let A : (ι → ScalarMomentum) → ℝ := fun d => (w d).re * (∏ i, logKernel m ‖d i‖).toReal
  have ht := ae_marginal_time_pos ι
  have hMeas : Measurable H := by unfold H marginalHeat; fun_prop
  have hFmeas : Measurable F := ((Complex.measurable_re.comp hwm).comp measurable_snd).mul hMeas
  have hH₀ {t : ι → ℝ} (ht : ∀ i, 0 < t i) (d : ι → ScalarMomentum) (i : ι) :
      0 ≤ marginalHeat m (t i) ‖d i‖ := by
    unfold marginalHeat
    exact div_nonneg (exp_pos _).le (mul_nonneg (sq_nonneg _) (ht i).le)
  have hHp : ∀ᵐ p : (ι → ℝ) × (ι → ScalarMomentum) ∂τ.prod μ, ∀ i, 0 < p.1 i :=
    (Measure.quasiMeasurePreserving_fst (μ := τ) (ν := μ)).tendsto_ae.eventually ht
  have hHq : 0 ≤ᵐ[τ.prod μ] H := hHp.mono fun p hp =>
    Finset.prod_nonneg (fun i _ => hH₀ hp p.2 i)
  have hH_time (d : ι → ScalarMomentum) :
      (∫⁻ t, ENNReal.ofReal (H (t,d)) ∂τ) = ∏ i, logKernel m ‖d i‖ := by
    refine Eq.trans (lintegral_congr_ae (ht.mono (fun t hp => ?_)))
      (joint_marginal_proper_time m d)
    exact ENNReal.ofReal_prod_of_nonneg (fun i _ => hH₀ hp d i)
  have hHI : Integrable H (τ.prod μ) := by
    apply (lintegral_ofReal_ne_top_iff_integrable hMeas.aestronglyMeasurable hHq).1
    rw [lintegral_prod_symm (fun p => ENNReal.ofReal (H p)) hMeas.ennreal_ofReal.aemeasurable]
    simpa only [hH_time] using hEnergy.ne
  have hFI : Integrable F (τ.prod μ) := by
    refine hHI.mono' hFmeas.aestronglyMeasurable (hHq.mono (fun p hp => ?_))
    change 0 ≤ H p at hp
    have hr : |(w p.2).re| ≤ 1 := (Complex.abs_re_le_norm _).trans (hww _)
    change ‖(w p.2).re * H p‖ ≤ H p
    rw [norm_mul,Real.norm_eq_abs,Real.norm_of_nonneg hp]
    exact mul_le_of_le_one_left hp hr
  let J := fun t => ∫ d, F (t,d) ∂μ
  let C := weightedMarginalCharacteristic μ w
  have hT {t : ι → ℝ} (ht : ∀ i, 0 < t i) : 0 ≤ J t ∧
      (∫⁻ q : ι → ScalarMomentum, ENNReal.ofReal (C q) *
        ∏ i, ENNReal.ofReal (marginalSchwinger m (q i) (t i))) = ENNReal.ofReal (J t) := by
    obtain ⟨hF,_,hEq⟩ := weighted_marginal_fixed_time μ m w hwm hww ht
    dsimp only at hF hEq
    have hn (q : ι → ScalarMomentum) (i : ι) : 0 ≤ marginalSchwinger m (q i) (t i) := by
      unfold marginalSchwinger
      exact div_nonneg (mul_nonneg (ht i).le (exp_pos _).le) (by positivity)
    have hP (q : ι → ScalarMomentum) :
        0 ≤ C q * ∏ i, marginalSchwinger m (q i) (t i) :=
      mul_nonneg (hC q) (Finset.prod_nonneg (fun i _ => hn q i))
    change (∫ q, C q * ∏ i, marginalSchwinger m (q i) (t i)) = J t at hEq
    refine ⟨hEq ▸ integral_nonneg hP,?_⟩
    have hC₀ (q : ι → ScalarMomentum) : 0 ≤ C q := hC q
    simp_rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => hn _ i),← ENNReal.ofReal_mul (hC₀ _)]
    rw [← ofReal_integral_eq_lintegral_ofReal hF (ae_of_all _ hP),hEq]
  have hJ₀ : 0 ≤ᵐ[τ] J := ht.mono (fun _ hp => (hT hp).1)
  have hJI : Integrable J τ := hFI.integral_prod_left
  have hRight : (∫ t, J t ∂τ) = ∫ d, A d ∂μ := by
    rw [show (∫ t, J t ∂τ) = ∫ d, ∫ t, F (t,d) ∂τ ∂μ from
      integral_integral_swap (f := fun t d => F (t,d)) hFI]
    apply integral_congr_ae
    filter_upwards [hHI.prod_left_ae] with d hHd
    have hn : 0 ≤ᵐ[τ] fun t => H (t,d) := ht.mono (fun _ hp =>
      Finset.prod_nonneg (fun i _ => hH₀ hp d i))
    have hEq := ofReal_integral_eq_lintegral_ofReal hHd hn
    rw [hH_time d] at hEq
    have hEq' : (∫ t, H (t,d) ∂τ) = (∏ i, logKernel m ‖d i‖).toReal := by
      rw [← hEq,ENNReal.toReal_ofReal (integral_nonneg_of_ae hn)]
    change (∫ t, (w d).re * H (t,d) ∂τ) = A d
    rw [integral_const_mul,hEq']
  change 0 ≤ (∫ d, A d ∂μ) ∧ _
  refine ⟨hRight ▸ integral_nonneg_of_ae hJ₀,?_⟩
  rw [marginal_schwinger_time hm _ (weightedMarginalCharacteristic_measurable μ w hwm)]
  have hL := lintegral_congr_ae (ht.mono (fun _ hp => (hT hp).2))
  rw [hL,← ofReal_integral_eq_lintegral_ofReal hJI hJ₀,hRight]

/-- The complex-valued pairing with a finite log-energy envelope.
The hypothesis on the imaginary part is the manuscript's requirement
that the full characteristic be real and nonnegative. -/
theorem complex_weighted_joint_marginal_log_energy {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ScalarMomentum)) [IsFiniteMeasure μ] {m : ℝ} (hm : 0 < m)
    (w : (ι → ScalarMomentum) → ℂ) (hwm : Measurable w) (hww : ∀ d, ‖w d‖ ≤ 1)
    (hC : ∀ q, 0 ≤ weightedMarginalCharacteristic μ w q)
    (hIm : ∀ q, (∫ d, w d * marginalPhase q d ∂μ).im = 0)
    (hEnergy : (∫⁻ d, ∏ i, logKernel m ‖d i‖ ∂μ) < ⊤) :
    let E := ∫⁻ q : ι → ScalarMomentum, ENNReal.ofReal (weightedMarginalCharacteristic μ w q) *
      ∏ i, ENNReal.ofReal (((m^2+‖q i‖^2)^2)⁻¹/(2*π)^4)
    E < ⊤ ∧ (E.toReal : ℂ) =
      ∫ d, w d * ((∏ i, logKernel m ‖d i‖).toReal:ℂ) ∂μ := by
  let K := fun d : ι → ScalarMomentum => (∏ i, logKernel m ‖d i‖).toReal
  have hKmeas : Measurable K := (Finset.measurable_prod _ fun i _ =>
    (logKernel_measurable m).comp (measurable_pi_apply i).norm).ennreal_toReal
  have hKi : Integrable K μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable hKmeas.aestronglyMeasurable
      (ae_of_all _ fun _ => ENNReal.toReal_nonneg)).1
    have h : (∫⁻ d, ENNReal.ofReal (K d) ∂μ) ≤ ∫⁻ d, ∏ i, logKernel m ‖d i‖ ∂μ :=
      lintegral_mono (fun _ => ENNReal.ofReal_toReal_le)
    exact (h.trans_lt hEnergy).ne
  have hW : Integrable (fun d => w d * (K d:ℂ)) μ := by
    apply hKi.mono' (hwm.mul hKmeas.complex_ofReal).aestronglyMeasurable
    refine ae_of_all _ (fun d => ?_)
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_of_le_one_left ENNReal.toReal_nonneg (hww d)
  obtain ⟨hA,hE⟩ := weighted_joint_marginal_log_energy μ hm w hwm hww hC hEnergy
  have hI (c : ℂ) (hc : c.re = 0) (q : ι → ScalarMomentum) :
      weightedMarginalCharacteristic μ (fun d => c*w d) q = 0 := by
    unfold weightedMarginalCharacteristic
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    simp [Complex.mul_re,hc,hIm q]
  have hNorm (c : ℂ) (hc : ‖c‖ = 1) (d : ι → ScalarMomentum) : ‖c * w d‖ ≤ 1 := by
    simpa only [norm_mul,hc,one_mul] using hww d
  have hPos := (weighted_joint_marginal_log_energy μ hm (fun d => (-Complex.I)*w d)
    (measurable_const.mul hwm) (hNorm _ (by simp))
    (fun q => (hI _ (by simp) q).ge) hEnergy).1
  have hNeg := (weighted_joint_marginal_log_energy μ hm (fun d => Complex.I*w d)
    (measurable_const.mul hwm) (hNorm _ (by simp))
    (fun q => (hI _ (by simp) q).ge) hEnergy).1
  change 0 ≤ ∫ d, ((-Complex.I)*w d).re * K d ∂μ at hPos
  change 0 ≤ ∫ d, (Complex.I*w d).re * K d ∂μ at hNeg
  simp only [Complex.mul_re,Complex.neg_re,Complex.I_re,Complex.I_im,
    zero_mul,neg_mul,one_mul,zero_sub,neg_neg] at hPos hNeg
  rw [integral_neg] at hNeg
  have hImag : (∫ d, (w d).im*K d ∂μ)=0 := le_antisymm (neg_nonneg.mp hNeg) hPos
  dsimp only
  refine ⟨hE ▸ ENNReal.ofReal_lt_top,?_⟩
  rw [hE,ENNReal.toReal_ofReal hA]
  apply Complex.ext
  · rw [Complex.ofReal_re]
    change _ = RCLike.re (∫ d, w d * (K d:ℂ) ∂μ)
    rw [← integral_re hW]
    simp only [RCLike.re_eq_complex_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,K]
  · rw [Complex.ofReal_im]
    change _ = RCLike.im (∫ d, w d * (K d:ℂ) ∂μ)
    rw [← integral_im hW]
    simpa only [RCLike.im_eq_complex_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add]
      using hImag.symm

/-- A pairing imposing exact coincidence in every marginal direction
has characteristic one and infinite bare energy at any positive mass. -/
theorem collapsed_marginal_pairing_diverges (ι : Type*) [Fintype ι] [Nonempty ι]
    {m : ℝ} (hm : 0 < m) :
    (∫⁻ q : ι → ScalarMomentum,
      ∏ i, ENNReal.ofReal (((m^2+‖q i‖^2)^2)⁻¹/(2*π)^4)) = ⊤ := by
  let D := Measure.dirac (0 : ι → ScalarMomentum)
  have hD (q : ι → ScalarMomentum) : marginalCharacteristic D q = 1 := by
    unfold marginalCharacteristic D
    rw [integral_dirac]
    simp [marginalPhase,stableFourierPhase]
  have h := joint_marginal_log_energy D hm (fun q => hD q ▸ zero_le_one)
  simp only [hD,ENNReal.ofReal_one,one_mul] at h
  rw [h]
  change (∫⁻ d, ∏ i, logKernel m ‖d i‖ ∂Measure.dirac (0 : ι → ScalarMomentum)) = ⊤
  rw [lintegral_dirac]
  simp [logKernel_zero hm, Fintype.card_ne_zero]

end UV.SewnFlags
