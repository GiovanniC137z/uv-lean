import UV.GeneralQED
import UV.GlobalConvergence

/-! The common-domain Ward translation at the canonical massless endpoint. -/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped BigOperators Matrix Topology Matrix.Norms.Elementwise

namespace UV

private theorem freeDirac_inverse_of_denominator {m : ℝ} {k : DiracMomentum}
    (h : ‖k‖ ^ 2 + m ^ 2 ≠ 0) : freeDiracSymbol m k * freeDiracPropagator m k = 1 := by
  have hc : ((‖k‖ ^ 2 + m ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h
  unfold freeDiracPropagator
  rw [Matrix.mul_smul, freeDiracSymbol_mul_numerator, smul_smul, inv_mul_cancel₀ hc, one_smul]

private theorem bare_ward_trace_contraction_of_denominators {m : ℝ}
    (Q k : DiracMomentum) (ν : Fin 4)
    (hk : ‖k‖ ^ 2 + m ^ 2 ≠ 0) (hl : ‖k + Q‖ ^ 2 + m ^ 2 ≠ 0) :
    (∑ μ, (Q μ : ℂ) * Matrix.trace (bareWardLine m k μ * bareWardLine m (k + Q) ν)) =
      Matrix.trace (bareWardLine m k ν) - Matrix.trace (bareWardLine m (k + Q) ν) := by
  have hsum : (∑ μ, (Q μ : ℂ) •
      (bareWardLine m k μ * bareWardLine m (k + Q) ν)) =
      (freeDiracSymbol m (k + Q) - freeDiracSymbol m k) * freeDiracPropagator m k *
        bareWardLine m (k + Q) ν := by
    simp only [bareWardLine, ← smul_mul_assoc, ← Finset.sum_mul]
    rw [bare_gamma_contraction, freeDiracSymbol_add_sub]
  have htrace : (∑ μ, (Q μ : ℂ) * Matrix.trace
      (bareWardLine m k μ * bareWardLine m (k + Q) ν)) =
      Matrix.trace (∑ μ, (Q μ : ℂ) •
        (bareWardLine m k μ * bareWardLine m (k + Q) ν)) := by
    rw [Matrix.trace_sum]
    simp only [Matrix.trace_smul, smul_eq_mul]
  rw [htrace, hsum, sub_mul, sub_mul, Matrix.trace_sub]
  congr 1
  · rw [Matrix.trace_mul_cycle (freeDiracSymbol m (k + Q))
      (freeDiracPropagator m k) (bareWardLine m (k + Q) ν)]
    unfold bareWardLine
    rw [Matrix.mul_assoc (Complex.I • euclideanGamma ν) (freeDiracPropagator m (k + Q))
      (freeDiracSymbol m (k + Q)), Matrix.mul_eq_one_comm.mp (freeDirac_inverse_of_denominator hl),
      Matrix.mul_one]
  · rw [freeDirac_inverse_of_denominator hk, Matrix.one_mul]

private theorem bare_ward_tensor_contraction_ae_general (m : ℝ)
    (F : ℝ → ℝ) (Q : DiracMomentum) (ν : Fin 4) :
    (fun k => ∑ μ, (Q μ : ℂ) * bareWardTensor F m Q μ ν k) =ᵐ[volume]
      bareWardContracted F m Q ν := by
  have hk : ∀ᵐ k : DiracMomentum, k ≠ 0 := by rw [ae_iff]; simp
  have hl : ∀ᵐ k : DiracMomentum, k ≠ -Q := by rw [ae_iff]; simp
  filter_upwards [hk, hl] with k hk hl
  have hkp : 0 < ‖k‖ := norm_pos_iff.mpr hk
  have hlp : 0 < ‖k + Q‖ := norm_pos_iff.mpr (by intro hz; exact hl (eq_neg_of_add_eq_zero_left hz))
  unfold bareWardTensor bareWardContracted
  have h := bare_ward_trace_contraction_of_denominators (m := m) Q k ν
    (by positivity) (by positivity)
  rw [← h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro μ _
  ring

/-- Local integrability of the massless one-power singularity in four
dimensions, retaining the canonical value at the origin. -/
private theorem momentum_inv_norm_locally_integrable (R : ℝ) :
    IntegrableOn (fun k : DiracMomentum => ‖k‖⁻¹) (closedBall 0 R) := by
  have h := (massless_gaussian_integrable (d := 1) (by norm_num) zero_lt_one).const_mul
    (Real.exp (R ^ 2))
  apply h.integrableOn.mono' measurable_norm.inv.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with k hk
  have hR : ‖k‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hk
  have hsq := pow_le_pow_left₀ (norm_nonneg k) hR 2
  have hcoef : 1 ≤ Real.exp (R ^ 2) * Real.exp (-‖k‖ ^ 2) := by
    rw [← Real.exp_add]
    exact Real.one_le_exp (by linarith)
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg k))]
  have hbound := le_mul_of_one_le_right (inv_nonneg.mpr (norm_nonneg k)) hcoef
  simp only [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one, neg_mul, one_mul]
  convert hbound using 1
  ring

private theorem integrable_tent_of_weighted {C : DiracMomentum → ℂ}
    (hC : AEStronglyMeasurable C volume) (Q : DiracMomentum) {R : ℝ} (hR : 0 < R)
    (hW : Integrable (fun k => ‖C k‖ / (1 + ‖k‖))) :
    Integrable (fun k => (wardTentCutoff R (k - Q) : ℂ) * C k) := by
  apply (hW.const_mul (1 + R + ‖Q‖)).mono'
    ((Complex.continuous_ofReal.comp ((wardTentCutoff_continuous R).comp
      (continuous_id.sub continuous_const))).aestronglyMeasurable.mul hC)
  filter_upwards with k
  change ‖(wardTentCutoff R (k - Q) : ℂ) * C k‖ ≤
    (1 + R + ‖Q‖) * (‖C k‖ / (1 + ‖k‖))
  by_cases hk : R ≤ ‖k - Q‖
  · rw [wardTentCutoff_zero hR hk, Complex.ofReal_zero, zero_mul, norm_zero]
    positivity
  · have hb : ‖k‖ ≤ R + ‖Q‖ := by
      have ht := norm_sub_norm_le k Q
      linarith
    have hm : 1 ≤ (1 + R + ‖Q‖) / (1 + ‖k‖) := by
      exact (one_le_div (by positivity)).mpr (by linarith)
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (wardTentCutoff_bounds hR _).1]
    calc
      _ ≤ ‖C k‖ := mul_le_of_le_one_left (norm_nonneg _) (wardTentCutoff_bounds hR _).2
      _ ≤ ((1 + R + ‖Q‖) / (1 + ‖k‖)) * ‖C k‖ :=
        le_mul_of_one_le_left (norm_nonneg _) hm
      _ = _ := by ring

private theorem integral_translation_difference_eq_zero_measurable
    {C : DiracMomentum → ℂ} (hC : AEStronglyMeasurable C volume) (Q : DiracMomentum)
    (hW : Integrable (fun k => ‖C k‖ / (1 + ‖k‖)))
    (hD : Integrable (fun k => C k - C (k + Q))) :
    (∫ k, C k - C (k + Q)) = 0 := by
  let D : ℕ → DiracMomentum → ℂ := fun n k =>
    (wardTentCutoff (n + 1) k : ℂ) * (C k - C (k + Q))
  let E : ℕ → DiracMomentum → ℂ := fun n k =>
    ((wardTentCutoff (n + 1) k - wardTentCutoff (n + 1) (k - Q) : ℝ) : ℂ) * C k
  have hDm (n : ℕ) : AEStronglyMeasurable (D n) volume := by
    exact (Complex.continuous_ofReal.comp
      (wardTentCutoff_continuous (n + 1))).aestronglyMeasurable.mul hD.aestronglyMeasurable
  have hEm (n : ℕ) : AEStronglyMeasurable (E n) volume := by
    exact (Complex.continuous_ofReal.comp ((wardTentCutoff_continuous (n + 1)).sub
      ((wardTentCutoff_continuous (n + 1)).comp
        (continuous_id.sub continuous_const)))).aestronglyMeasurable.mul hC
  have hDb (n : ℕ) : ∀ᵐ k, ‖D n k‖ ≤ ‖C k - C (k + Q)‖ := by
    filter_upwards with k
    dsimp [D]
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (wardTentCutoff_bounds (by positivity : (0 : ℝ) < n + 1) k).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (wardTentCutoff_bounds (by positivity : (0 : ℝ) < (n : ℝ) + 1) k).2
  have hEb (n : ℕ) : ∀ᵐ k, ‖E n k‖ ≤
      (‖Q‖ * (2 + ‖Q‖)) * (‖C k‖ / (1 + ‖k‖)) := by
    filter_upwards with k
    dsimp [E]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hh := wardTentCutoff_weighted_shift_difference (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith : (1 : ℝ) ≤ n + 1) Q k
    have hden : 0 < 1 + ‖k‖ := by positivity
    have hcoef := (le_div_iff₀ hden).mpr hh
    have hb := mul_le_mul_of_nonneg_right hcoef (norm_nonneg (C k))
    convert hb using 1
    ring
  have hDl : ∀ᵐ k, Tendsto (fun n => D n k) atTop (𝓝 (C k - C (k + Q))) := by
    filter_upwards with k
    have hh := (Complex.continuous_ofReal.tendsto 1).comp (wardTentCutoff_tendsto k)
    simpa only [Complex.ofReal_one, one_mul] using hh.mul_const (C k - C (k + Q))
  have hEl : ∀ᵐ k, Tendsto (fun n => E n k) atTop (𝓝 (0 : ℂ)) := by
    filter_upwards with k
    have hh := (wardTentCutoff_tendsto k).sub (wardTentCutoff_tendsto (k - Q))
    have hh' := (Complex.continuous_ofReal.tendsto 0).comp (by simpa only [sub_self] using hh)
    simpa only [Complex.ofReal_zero, zero_mul] using hh'.mul_const (C k)
  have hDlim := tendsto_integral_of_dominated_convergence (fun k => ‖C k - C (k + Q)‖)
    hDm hD.norm hDb hDl
  have hElim := tendsto_integral_of_dominated_convergence
    (fun k => (‖Q‖ * (2 + ‖Q‖)) * (‖C k‖ / (1 + ‖k‖)))
    hEm (hW.const_mul _) hEb hEl
  have heq : ∀ n, (∫ k, D n k) = ∫ k, E n k := by
    intro n
    have hR : (0 : ℝ) < n + 1 := by positivity
    have h₀ := integrable_tent_of_weighted hC (0 : DiracMomentum) hR hW
    simp only [sub_zero] at h₀
    have hMinus := integrable_tent_of_weighted hC Q hR hW
    have hPlus := hMinus.comp_add_right Q
    simp only [add_sub_cancel_right] at hPlus
    have hshift := integral_add_right_eq_self (μ := (volume : Measure DiracMomentum))
      (fun k : DiracMomentum => (wardTentCutoff (n + 1) (k - Q) : ℂ) * C k) Q
    simp only [add_sub_cancel_right] at hshift
    have hDeq : D n = (fun k => (wardTentCutoff (n + 1) k : ℂ) * C k -
        (wardTentCutoff (n + 1) k : ℂ) * C (k + Q)) := by funext k; dsimp [D]; ring
    have hEeq : E n = (fun k => (wardTentCutoff (n + 1) k : ℂ) * C k -
        (wardTentCutoff (n + 1) (k - Q) : ℂ) * C k) := by
      funext k
      dsimp [E]
      push_cast
      ring
    rw [hDeq, hEeq, integral_sub h₀ hPlus, integral_sub h₀ hMinus, hshift]
  have hElim' : Tendsto (fun n => ∫ k, D n k) atTop (𝓝 (0 : ℂ)) := by
    simpa only [heq, integral_zero] using hElim
  exact tendsto_nhds_unique hDlim hElim'


private theorem wardTrace_measurable (m : ℝ) (ν : Fin 4) :
    Measurable (fun k : DiracMomentum => Matrix.trace (bareWardLine m k ν)) := by
  simp_rw [bareWardLine_trace]
  fun_prop

private theorem ward_trace_with_bounded_coefficient_integrableOn
    {g : DiracMomentum → ℝ} (hg : Measurable g) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ k, |g k| ≤ B) (m R : ℝ) (ν : Fin 4) :
    IntegrableOn (fun k : DiracMomentum => (g k : ℂ) * Matrix.trace (bareWardLine m k ν))
      (closedBall 0 R) := by
  apply ((momentum_inv_norm_locally_integrable R).const_mul (4 * B)).mono'
    ((Complex.continuous_ofReal.measurable.comp hg).mul
      (wardTrace_measurable m ν)).aestronglyMeasurable
  filter_upwards with k
  change ‖(g k : ℂ) * Matrix.trace (bareWardLine m k ν)‖ ≤ 4 * B * ‖k‖⁻¹
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases hk : k = 0
  · simp only [hk, bareWardLine_trace, PiLp.zero_apply, mul_zero, zero_div, Complex.ofReal_zero,
      norm_zero, inv_zero]
    exact le_rfl
  have h := mul_le_mul (hb k) (bareWardLine_trace_norm_bound m k ν (norm_pos_iff.mpr hk))
    (norm_nonneg _) hB
  convert h using 1
  ring

private theorem wardLaplaceKernel_abs_le {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) (u : ℝ) : |wardLaplaceKernel ρ 1 u| ≤ (ρ univ).toReal := by
  rw [wardLaplaceKernel, one_pow, one_mul]
  have h0 : 0 ≤ laplace ρ (max u 0) := integral_nonneg fun _ => Real.exp_nonneg _
  rw [abs_of_nonneg h0]
  have h := nonnegative_laplace_antitone ρ hp (le_refl 0) (le_max_right u 0)
  simpa [laplace, measureReal_def] using h

private theorem laplace_ward_remainder_local (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) (m : ℝ) (Q : DiracMomentum) (ν : Fin 4) (R : ℝ) :
    IntegrableOn (bareWardRemainder (wardLaplaceKernel ρ 1) m Q ν) (closedBall 0 R) := by
  let F := wardLaplaceKernel ρ 1
  have hF := wardLaplaceKernel_continuous ρ hp 1
  have hG : Measurable (fun k : DiracMomentum =>
      F (‖k‖ ^ 2) * (F (‖k + Q‖ ^ 2) - F (‖k - Q‖ ^ 2))) := by
    exact ((hF.comp (by fun_prop : Continuous fun k : DiracMomentum => ‖k‖ ^ 2)).mul
      ((hF.comp (by fun_prop : Continuous fun k : DiracMomentum => ‖k + Q‖ ^ 2)).sub
       (hF.comp (by fun_prop : Continuous fun k : DiracMomentum => ‖k - Q‖ ^ 2)))).measurable
  apply ward_trace_with_bounded_coefficient_integrableOn hG
    (B := (ρ univ).toReal * ((ρ univ).toReal + (ρ univ).toReal)) (by positivity) _ m R ν
  intro k
  rw [abs_mul]
  apply mul_le_mul (wardLaplaceKernel_abs_le hp _) _ (abs_nonneg _) ENNReal.toReal_nonneg
  exact (abs_sub _ _).trans (add_le_add (wardLaplaceKernel_abs_le hp _)
    (wardLaplaceKernel_abs_le hp _))

private theorem laplace_ward_cutoff_local (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) (m : ℝ) (Q : DiracMomentum) (ν : Fin 4) (R : ℝ) :
    IntegrableOn (bareWardCutoffTerm (wardLaplaceKernel ρ 1) m Q ν) (closedBall 0 R) := by
  let F := wardLaplaceKernel ρ 1
  have hF := wardLaplaceKernel_continuous ρ hp 1
  have hG : Measurable (fun k : DiracMomentum => F (‖k‖ ^ 2) * F (‖k - Q‖ ^ 2)) :=
    ((hF.comp (by fun_prop : Continuous fun k : DiracMomentum => ‖k‖ ^ 2)).mul
     (hF.comp (by fun_prop : Continuous fun k : DiracMomentum => ‖k - Q‖ ^ 2))).measurable
  apply ward_trace_with_bounded_coefficient_integrableOn hG
    (B := (ρ univ).toReal * (ρ univ).toReal) (by positivity) _ m R ν
  intro k
  rw [abs_mul]
  exact mul_le_mul (wardLaplaceKernel_abs_le hp _) (wardLaplaceKernel_abs_le hp _)
    (abs_nonneg _) ENNReal.toReal_nonneg

private theorem ward_remainder_measurable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) (m : ℝ) (Q : DiracMomentum) (ν : Fin 4) :
    Measurable (bareWardRemainder (wardLaplaceKernel ρ 1) m Q ν) := by
  unfold bareWardRemainder
  have hF := (wardLaplaceKernel_continuous ρ hp 1).measurable
  have hT := wardTrace_measurable m ν
  fun_prop

private theorem ward_cutoff_measurable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) (m : ℝ) (Q : DiracMomentum) (ν : Fin 4) :
    Measurable (bareWardCutoffTerm (wardLaplaceKernel ρ 1) m Q ν) := by
  unfold bareWardCutoffTerm
  have hF := (wardLaplaceKernel_continuous ρ hp 1).measurable
  have hT := wardTrace_measurable m ν
  fun_prop

private theorem laplace_bare_ward_remainder_integrable_general (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) {m : ℝ} (hm : 0 ≤ m) (Q : DiracMomentum)
    (hH : ∀ μ ν, Integrable (bareWardTensor (wardLaplaceKernel ρ 1) m Q μ ν))
    (ν : Fin 4) : Integrable (bareWardRemainder (wardLaplaceKernel ρ 1) m Q ν) := by
  let J := bareWardRemainder (wardLaplaceKernel ρ 1) m Q ν
  have hJ : Measurable J := ward_remainder_measurable ρ hp m Q ν
  have hsum : Integrable (fun k : DiracMomentum => ∑ μ,
      bareWardTensor (wardLaplaceKernel ρ 1) m Q μ μ k) :=
    integrable_finset_sum _ (fun μ _ => hH μ μ)
  have hmajor : Integrable (fun k : DiracMomentum => (4 * ‖Q‖) *
      ‖∑ μ, bareWardTensor (wardLaplaceKernel ρ 1) m Q μ μ ((1 / 8 : ℝ) • k)‖) :=
    (hsum.comp_smul (by norm_num : (1 / 8 : ℝ) ≠ 0)).norm.const_mul _
  let K : ℝ := 16 * ‖Q‖ + 8 * m + 1
  have hlocal : IntegrableOn J (closedBall (0 : DiracMomentum) K) :=
    laplace_ward_remainder_local ρ hp m Q ν K
  have htail : IntegrableOn J (closedBall (0 : DiracMomentum) K)ᶜ := by
    apply hmajor.integrableOn.mono' hJ.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with k hk
    have hknorm : K < ‖k‖ := by simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hk
    have hkpos : 0 < ‖k‖ := by dsimp [K] at hknorm; nlinarith [norm_nonneg Q]
    have hQk : 16 * ‖Q‖ ≤ ‖k‖ := by dsimp [K] at hknorm; linarith
    have hmk : 8 * m ≤ ‖k‖ := by dsimp [K] at hknorm; nlinarith [norm_nonneg Q]
    have hsmall := laplace_bare_ward_remainder_tail ρ hp m Q k ν hkpos (by linarith [norm_nonneg Q])
    have hlarge := mul_le_mul_of_nonneg_left
      (laplace_bare_ward_scaled_tensor_lower ρ hp hm Q k hkpos hQk hmk)
      (by positivity : 0 ≤ 4 * ‖Q‖)
    apply hsmall.trans
    convert hlarge using 1
    ring
  have hall := hlocal.union htail
  simpa only [union_compl_self, integrableOn_univ] using hall

private theorem laplace_bare_ward_weighted_cutoff_integrable_general (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) {m : ℝ} (hm : 0 ≤ m) (Q : DiracMomentum)
    (hH : ∀ μ ν, Integrable (bareWardTensor (wardLaplaceKernel ρ 1) m Q μ ν))
    (ν : Fin 4) : Integrable (fun k =>
      ‖bareWardCutoffTerm (wardLaplaceKernel ρ 1) m Q ν k‖ / (1 + ‖k‖)) := by
  let W : DiracMomentum → ℝ := fun k =>
    ‖bareWardCutoffTerm (wardLaplaceKernel ρ 1) m Q ν k‖ / (1 + ‖k‖)
  have hW : Measurable W := (ward_cutoff_measurable ρ hp m Q ν).norm.div
    (measurable_const.add measurable_norm)
  have hsum : Integrable (fun k : DiracMomentum => ∑ μ,
      bareWardTensor (wardLaplaceKernel ρ 1) m Q μ μ k) :=
    integrable_finset_sum _ (fun μ _ => hH μ μ)
  have hmajor : Integrable (fun k : DiracMomentum => (1 / 8 : ℝ) *
      ‖∑ μ, bareWardTensor (wardLaplaceKernel ρ 1) m Q μ μ ((1 / 8 : ℝ) • k)‖) :=
    (hsum.comp_smul (by norm_num : (1 / 8 : ℝ) ≠ 0)).norm.const_mul _
  let K : ℝ := 16 * ‖Q‖ + 8 * m + 1
  have hlocal : IntegrableOn W (closedBall (0 : DiracMomentum) K) :=
    by
    apply (laplace_ward_cutoff_local ρ hp m Q ν K).norm.mono' hW.aestronglyMeasurable
    filter_upwards with k
    dsimp [W]
    rw [abs_of_nonneg (by positivity)]
    exact div_le_self (norm_nonneg _) (le_add_of_nonneg_right (norm_nonneg _))
  have htail : IntegrableOn W (closedBall (0 : DiracMomentum) K)ᶜ := by
    apply hmajor.integrableOn.mono' hW.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with k hk
    have hknorm : K < ‖k‖ := by simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hk
    have hkpos : 0 < ‖k‖ := by dsimp [K] at hknorm; nlinarith [norm_nonneg Q]
    have hQk : 16 * ‖Q‖ ≤ ‖k‖ := by dsimp [K] at hknorm; linarith
    have hmk : 8 * m ≤ ‖k‖ := by dsimp [K] at hknorm; nlinarith [norm_nonneg Q]
    rw [Real.norm_of_nonneg (by dsimp [W]; positivity : 0 ≤ W k)]
    have hsmall := laplace_bare_ward_weighted_cutoff_tail ρ hp m Q k ν hkpos (by linarith [norm_nonneg Q])
    have hlarge := mul_le_mul_of_nonneg_left
      (laplace_bare_ward_scaled_tensor_lower ρ hp hm Q k hkpos hQk hmk)
      (by norm_num : (0 : ℝ) ≤ 1 / 8)
    apply hsmall.trans
    convert hlarge using 1
    ring
  have hall := hlocal.union htail
  simpa only [union_compl_self, integrableOn_univ] using hall


private theorem laplace_bare_ward_integral_eq_general (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) {m : ℝ} (hm : 0 ≤ m) (Q : DiracMomentum)
    (hH : ∀ μ ν, Integrable (bareWardTensor (wardLaplaceKernel ρ 1) m Q μ ν))
    (ν : Fin 4) :
    (∫ k, bareWardContracted (wardLaplaceKernel ρ 1) m Q ν k) =
      ∫ k, bareWardRemainder (wardLaplaceKernel ρ 1) m Q ν k := by
  let A := bareWardContracted (wardLaplaceKernel ρ 1) m Q ν
  let J := bareWardRemainder (wardLaplaceKernel ρ 1) m Q ν
  let C := bareWardCutoffTerm (wardLaplaceKernel ρ 1) m Q ν
  have hA : Integrable A :=
    (integrable_finset_sum Finset.univ fun i _ => (hH i ν).const_mul (Q i : ℂ)).congr
      (bare_ward_tensor_contraction_ae_general m _ Q ν)
  have hJ : Integrable J := laplace_bare_ward_remainder_integrable_general ρ hp hm Q hH ν
  have hC : Measurable C := ward_cutoff_measurable ρ hp m Q ν
  have hW : Integrable (fun k => ‖C k‖ / (1 + ‖k‖)) :=
    laplace_bare_ward_weighted_cutoff_integrable_general ρ hp hm Q hH ν
  have hpoint : (fun k => A k - J k) =ᵐ[volume] (fun k => C k - C (k + Q)) := by
    filter_upwards with k
    have hh := bare_ward_pointwise_common_domain (wardLaplaceKernel ρ 1) m Q ν k
    change A k = J k + C k - C (k + Q) at hh
    linear_combination hh
  have hD : Integrable (fun k => C k - C (k + Q)) := by
    apply (hA.sub hJ).congr
    simpa only [Pi.sub_apply] using hpoint
  have hz := integral_translation_difference_eq_zero_measurable hC.aestronglyMeasurable Q hW hD
  have hz' : (∫ k, A k - J k) = 0 := by rwa [integral_congr_ae hpoint]
  rw [integral_sub hA hJ] at hz'
  exact sub_eq_zero.mp hz'

/-- Revised Ward remainder and unsplit common-cutoff integral identity.
Both singular momenta in the canonical massless case are volume-null. -/
theorem revised_ward_common_cutoff (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) (a : ℝ) {m : ℝ} (hm : 0 ≤ m) (Q : DiracMomentum)
    (hH : ∀ μ ν, Integrable (bareWardTensor (wardLaplaceKernel ρ a) m Q μ ν)) :
    (∀ ν, Integrable (bareWardRemainder (wardLaplaceKernel ρ a) m Q ν)) ∧
    ∀ ν, (∑ μ, (Q μ : ℂ) * ∫ k, bareWardTensor (wardLaplaceKernel ρ a) m Q μ ν k) =
      ∫ k, bareWardRemainder (wardLaplaceKernel ρ a) m Q ν k := by
  rw [wardLaplaceKernel_pushforward] at hH ⊢
  let σ := ρ.map (fun τ : ℝ => a ^ 2 * τ)
  have hσ : ∀ᵐ τ ∂σ, 0 ≤ τ := ward_heat_support_nonnegative ρ hp a
  refine ⟨fun ν => laplace_bare_ward_remainder_integrable_general σ hσ hm Q hH ν, ?_⟩
  intro ν
  calc
    _ = ∫ k, ∑ μ, (Q μ : ℂ) * bareWardTensor (wardLaplaceKernel σ 1) m Q μ ν k := by
      rw [integral_finset_sum _ (fun μ _ => (hH μ ν).const_mul (Q μ : ℂ))]
      simp only [integral_const_mul]
    _ = ∫ k, bareWardContracted (wardLaplaceKernel σ 1) m Q ν k :=
      integral_congr_ae (bare_ward_tensor_contraction_ae_general m _ Q ν)
    _ = _ := laplace_bare_ward_integral_eq_general σ hσ hm Q hH ν

theorem revised_ward_common_cutoff_polarization (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) (a : ℝ) {m : ℝ} (hm : 0 ≤ m) (e : ℝ) (Q : DiracMomentum)
    (hH : ∀ μ ν, Integrable (bareWardTensor (wardLaplaceKernel ρ a) m Q μ ν)) (ν : Fin 4) :
    (∑ μ, (Q μ : ℂ) * bareWardPolarization (wardLaplaceKernel ρ a) m e Q μ ν) =
      ((-(e ^ 2) * (2 * Real.pi) ^ (-4 : ℤ) : ℝ) : ℂ) *
        ∫ k, bareWardRemainder (wardLaplaceKernel ρ a) m Q ν k := by
  have hh := (revised_ward_common_cutoff ρ hp a hm Q hH).2 ν
  unfold bareWardPolarization
  calc
    _ = ((-(e ^ 2) * (2 * Real.pi) ^ (-4 : ℤ) : ℝ) : ℂ) *
        ∑ μ, (Q μ : ℂ) * ∫ k, bareWardTensor (wardLaplaceKernel ρ a) m Q μ ν k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro μ _
      ring
    _ = _ := by rw [hh]

end UV
