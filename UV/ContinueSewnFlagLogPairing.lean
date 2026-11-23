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

def marginalCharacteristic {ι : Type*} [Fintype ι] (μ : Measure (ι → ScalarMomentum))
    (q : ι → ScalarMomentum) : ℝ :=
  (∫ d, marginalPhase q d ∂μ).re

private theorem marginalPhase_measurable {ι : Type*} [Fintype ι] :
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

private theorem marginalCharacteristic_measurable {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ScalarMomentum)) [IsFiniteMeasure μ] : Measurable (marginalCharacteristic μ) :=
  Complex.measurable_re.comp marginalPhase_measurable.stronglyMeasurable.integral_prod_right'.measurable

private theorem marginalPhase_norm {ι : Type*} [Fintype ι] (q d : ι → ScalarMomentum) :
    ‖marginalPhase q d‖ = 1 := by simp [marginalPhase,norm_prod,stableFourierPhase_norm]

private theorem marginal_fixed_time_pairing {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ScalarMomentum)) [IsFiniteMeasure μ] (m : ℝ)
    (hC : ∀ q, 0 ≤ marginalCharacteristic μ q) {t : ι → ℝ} (ht : ∀ i, 0 < t i) :
    (∫⁻ q : ι → ScalarMomentum, ENNReal.ofReal (marginalCharacteristic μ q) *
      ∏ i, ENNReal.ofReal (marginalSchwinger m (q i) (t i))) =
      ∫⁻ d, ∏ i, ENNReal.ofReal (marginalHeat m (t i) ‖d i‖) ∂μ := by
  let W := fun q : ι → ScalarMomentum => ∏ i, marginalSchwinger m (q i) (t i)
  let G := fun q : (ι → ScalarMomentum) × (ι → ScalarMomentum) =>
      (W q.1:ℂ) * marginalPhase q.1 q.2
  have hw (q : ι → ScalarMomentum) (i : ι) : 0 ≤ marginalSchwinger m (q i) (t i) := by
    unfold marginalSchwinger
    exact div_nonneg (mul_nonneg (ht i).le (exp_pos _).le) (by positivity)
  have hW₀ (q : ι → ScalarMomentum) : 0 ≤ W q := Finset.prod_nonneg fun i _ => hw q i
  have hW : Measurable W := by unfold W marginalSchwinger; fun_prop
  have hG : Measurable G := (hW.comp measurable_fst).complex_ofReal.mul marginalPhase_measurable
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
  have hphase (q : ι → ScalarMomentum) : Integrable (marginalPhase q) μ :=
    Integrable.of_bound ((marginalPhase_measurable.comp measurable_prodMk_left).aestronglyMeasurable) 1
      (ae_of_all _ fun d => (marginalPhase_norm q d).le)
  have hIq (q : ι → ScalarMomentum) : Integrable (fun d => G (q,d)) μ := by
    change Integrable (fun d => (W q:ℂ)*marginalPhase q d) μ
    exact (hphase q).const_mul (W q:ℂ)
  have hI : Integrable G ((volume : Measure (ι → ScalarMomentum)).prod μ) := by
    refine (integrable_prod_iff hG.aestronglyMeasurable).2 ⟨ae_of_all _ hIq,?_⟩
    convert hIW.mul_const (μ.real univ) using 1
    ext q
    simp [G,marginalPhase_norm,Real.norm_of_nonneg (hW₀ q),mul_comm]
  have hq (q : ι → ScalarMomentum) :
      (∫ d, (G (q,d)).re ∂μ) = marginalCharacteristic μ q * W q := by
    change (∫ d, RCLike.re (G (q,d)) ∂μ) = _
    rw [integral_re (hIq q)]
    change (∫ d, (W q:ℂ)*marginalPhase q d ∂μ).re = _
    rw [integral_const_mul]
    simp [marginalCharacteristic,Complex.mul_re,mul_comm]
  have hprod (q d : ι → ScalarMomentum) :
      G (q,d) = ∏ i, (marginalSchwinger m (q i) (t i):ℂ)*stableFourierPhase (d i) (q i) := by
    simp [G,W,marginalPhase,Complex.ofReal_prod,Finset.prod_mul_distrib]
  have hId (d : ι → ScalarMomentum) : Integrable (fun q => G (q,d)) := by
    simp_rw [hprod,volume_pi]
    exact Integrable.fintype_prod (f := fun i q => (marginalSchwinger m q (t i):ℂ)*stableFourierPhase (d i) q)
      (fun i => marginal_fourier_integrable m (ht i) (d i))
  have hd (d : ι → ScalarMomentum) :
      (∫ q, (G (q,d)).re) = ∏ i, marginalHeat m (t i) ‖d i‖ := by
    change (∫ q, RCLike.re (G (q,d))) = _
    rw [integral_re (hId d)]
    change (∫ q, G (q,d)).re = _
    simp_rw [hprod]
    rw [joint_marginal_fourier_gaussian m t ht d,Complex.ofReal_re]
  have hRe : Integrable (fun q => (G q).re) ((volume : Measure (ι → ScalarMomentum)).prod μ) := hI.re
  have hF : Integrable (fun q => marginalCharacteristic μ q * W q) := by
    simpa only [hq] using hRe.integral_prod_left
  have hH : Integrable (fun d : ι → ScalarMomentum => ∏ i, marginalHeat m (t i) ‖d i‖) μ := by
    simpa only [hd] using hRe.integral_prod_right
  have hH₀ (d : ι → ScalarMomentum) (i : ι) : 0 ≤ marginalHeat m (t i) ‖d i‖ := by
    unfold marginalHeat
    exact div_nonneg (exp_pos _).le (mul_nonneg (sq_nonneg _) (ht i).le)
  simp_rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => hw _ i),
    ← ENNReal.ofReal_mul (hC _),← ENNReal.ofReal_prod_of_nonneg (fun i _ => hH₀ _ i)]
  rw [← ofReal_integral_eq_lintegral_ofReal hF (ae_of_all _ fun q => mul_nonneg (hC q) (hW₀ q)),
    ← ofReal_integral_eq_lintegral_ofReal hH (ae_of_all _ fun d => Finset.prod_nonneg (fun i _ => hH₀ d i))]
  congr 1
  simpa only [hq,hd] using integral_integral_swap (f := fun q d => (G (q,d)).re) hRe

/-- The literal joint marginal-loop equality for a finite positive
displacement measure with nonnegative characteristic. The extended
positive integrals retain the value infinity. -/
theorem joint_marginal_log_energy {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ScalarMomentum)) [IsFiniteMeasure μ] {m : ℝ} (hm : 0 < m)
    (hC : ∀ q, 0 ≤ marginalCharacteristic μ q) :
    (∫⁻ q : ι → ScalarMomentum, ENNReal.ofReal (marginalCharacteristic μ q) *
      ∏ i, ENNReal.ofReal (((m^2+‖q i‖^2)^2)⁻¹/(2*π)^4)) =
      ∫⁻ d, ∏ i, logKernel m ‖d i‖ ∂μ := by
  let τ : Measure (ι → ℝ) := Measure.pi (fun _ : ι => volume.restrict (Ioi (0:ℝ)))
  have ht : ∀ᵐ t ∂τ, ∀ i, 0 < t i :=
    eventually_all.2 (fun i => Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem measurableSet_Ioi))
  let f := fun q : (ι → ScalarMomentum) × (ι → ℝ) =>
    ENNReal.ofReal (marginalCharacteristic μ q.1) *
      ∏ i, ENNReal.ofReal (marginalSchwinger m (q.1 i) (q.2 i))
  let H := fun q : (ι → ℝ) × (ι → ScalarMomentum) =>
    ∏ i, ENNReal.ofReal (marginalHeat m (q.1 i) ‖q.2 i‖)
  have hf : Measurable f := ((marginalCharacteristic_measurable μ).comp measurable_fst).ennreal_ofReal.mul
    (Finset.measurable_prod _ fun i _ => by
      have hq := (measurable_pi_apply i).comp
        (measurable_fst : Measurable (Prod.fst : (ι → ScalarMomentum) × (ι → ℝ) → _))
      have ht := (measurable_pi_apply i).comp
        (measurable_snd : Measurable (Prod.snd : (ι → ScalarMomentum) × (ι → ℝ) → _))
      unfold marginalSchwinger
      fun_prop)
  have hH : Measurable H := by unfold H marginalHeat; fun_prop
  calc
    _ = ∫⁻ q : (ι → ScalarMomentum), ∫⁻ t, f (q,t) ∂τ := by
      apply lintegral_congr
      intro q
      dsimp only [f]
      have h (i : ι) : Measurable (fun t => ENNReal.ofReal (marginalSchwinger m (q i) t)) := by
        unfold marginalSchwinger
        fun_prop
      have hW : Measurable (fun t : ι → ℝ => ∏ i, ENNReal.ofReal (marginalSchwinger m (q i) (t i))) :=
        Finset.measurable_prod _ fun i _ => (h i).comp (measurable_pi_apply i)
      rw [lintegral_const_mul _ hW, UV.network_lintegral_fintype_prod _
        (fun i t => ENNReal.ofReal (marginalSchwinger m (q i) t)) h]
      simp only [marginal_schwinger_lintegral hm]
    _ = ∫⁻ t, ∫⁻ q : (ι → ScalarMomentum), f (q,t) ∂volume ∂τ :=
      lintegral_lintegral_swap hf.aemeasurable
    _ = ∫⁻ t, ∫⁻ d, H (t,d) ∂μ ∂τ := by
      apply lintegral_congr_ae
      filter_upwards [ht] with t ht'
      exact marginal_fixed_time_pairing μ m hC ht'
    _ = ∫⁻ d, ∫⁻ t, H (t,d) ∂τ ∂μ := lintegral_lintegral_swap hH.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro d
      exact joint_marginal_proper_time m d

end UV.SewnFlags
