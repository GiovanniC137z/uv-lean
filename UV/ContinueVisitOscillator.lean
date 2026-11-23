import UV.ContinueVisitVarianceLimit
import UV.ContinueVisitOscillatorIntegral
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-! The odd oscillator on the same normal return coordinate as the
double-tag coefficient. The cutoff is removed through the right filter. -/

noncomputable section

namespace UV.ContinueVisitOscillator

open MeasureTheory Real Set Filter
open scoped Topology Asymptotics

open UV.VerifyVisitConnectedJet UV.ContinueVisitCutoffLimit

def oddOscillatorDensity (C a x : ℝ) : ℝ := C * x^2 * exp (-a*x^2)

def oddOscillatorLaw (C a : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (oddOscillatorDensity C a x))

private theorem odd_density_nonneg {C a : ℝ} (hC : 0 ≤ C) (x : ℝ) :
    0 ≤ oddOscillatorDensity C a x := by unfold oddOscillatorDensity; positivity

private theorem integral_odd_oscillator {C a : ℝ} (hC : 0 ≤ C) (f : ℝ → ℝ) :
    (∫ x, f x ∂oddOscillatorLaw C a) = ∫ x, oddOscillatorDensity C a x * f x := by
  unfold oddOscillatorLaw
  rw [integral_withDensity_eq_integral_toReal_smul (by unfold oddOscillatorDensity; fun_prop)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (odd_density_nonneg hC _),smul_eq_mul]

def oscillatorRescaledReturn (a T δ u : ℝ) :=
  exp (-a*δ*u^2) * (exp (-δ*u^2/T) - exp (-u^2))^2 / u^2

def oscillatorReturnKernel (u : ℝ) := (1 - exp (-u^2))^2 / u^2

theorem oscillator_second_moment_scale {C a T δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) :
    sqrt δ * (∫ x, visitCutoff δ T x ^ 2 ∂oddOscillatorLaw C a) =
      C / (4*π^2) * ∫ u, oscillatorRescaledReturn a T δ u := by
  rw [integral_odd_oscillator hC]
  let G (x : ℝ) := oddOscillatorDensity C a x * visitCutoff δ T x ^ 2
  let r := sqrt δ
  have hr : 0 < r := sqrt_pos.2 hδ
  have hr2 : r^2 = δ := sq_sqrt hδ.le
  have hs : (∫ u, G (r*u)) = r⁻¹ * ∫ x, G x := by
    simpa only [abs_of_pos (inv_pos.mpr hr),smul_eq_mul] using Measure.integral_comp_mul_left G r
  have hi : r * (∫ x, G x) = r^2 * ∫ u, G (r*u) := by
    rw [hs]
    field_simp [hr.ne']
  change r * (∫ x, G x) = _
  rw [hi,← integral_const_mul,← integral_const_mul]
  apply integral_congr_ae
  refine Eventually.of_forall fun u => ?_
  by_cases hu : u = 0
  · subst u
    simp [G,oddOscillatorDensity,oscillatorRescaledReturn]
  · have hru : r*u ≠ 0 := mul_ne_zero hr.ne' hu
    have he : (r*u)^2 = δ*u^2 := by rw [mul_pow,hr2]
    have he' : -(δ*u^2)/δ = -(u^2) := by field_simp
    simp only [G,oddOscillatorDensity,visitCutoff,if_neg hru,he,he',oscillatorRescaledReturn,hr2]
    rw [show -(δ * u^2) / T = -δ*u^2/T by ring, show -a*(δ*u^2) = -a*δ*u^2 by ring]
    field_simp [Real.pi_ne_zero,hδ.ne',hu]
    ring

private theorem oscillator_rescaled_kernel_bound {a T δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ)
    (hδT : δ ≤ T) (u : ℝ) : ‖oscillatorRescaledReturn a T δ u‖ ≤ oscillatorReturnKernel u := by
  have hT := hδ.trans_le hδT
  have hpow := sq_nonneg u
  have h₁ : exp (-a*δ*u^2) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have hn : 0 ≤ a * δ * u^2 := by positivity
    linarith)
  have h₂ : exp (-δ*u^2/T) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by
      rw [neg_mul]; exact neg_nonpos.mpr (mul_nonneg hδ.le hpow)) hT.le)
  have h₃ : exp (-u^2) ≤ exp (-δ*u^2/T) := by
    apply Real.exp_le_exp.mpr
    apply (le_div_iff₀ hT).mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hδT) hpow]
  rw [Real.norm_of_nonneg (by unfold oscillatorRescaledReturn; positivity)]
  unfold oscillatorRescaledReturn oscillatorReturnKernel
  apply div_le_div_of_nonneg_right _ hpow
  exact (mul_le_mul_of_nonneg_right h₁ (sq_nonneg _)).trans (by
    rw [one_mul]
    exact (sq_le_sq₀ (sub_nonneg.mpr h₃) ((sub_nonneg.mpr (h₃.trans h₂)))).mpr (sub_le_sub_right h₂ _))

theorem oscillator_second_moment_right_limit {C a T : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (hT : 0 < T)
    (hkernel : Integrable oscillatorReturnKernel) :
    Tendsto (fun δ => sqrt δ * (∫ x, visitCutoff δ T x ^ 2 ∂oddOscillatorLaw C a)) (𝓝[>] 0)
      (𝓝 (C / (4*π^2) * ∫ u, oscillatorReturnKernel u)) := by
  have hI : Tendsto (fun δ => ∫ u, oscillatorRescaledReturn a T δ u) (𝓝[>] 0)
      (𝓝 (∫ u, oscillatorReturnKernel u)) := by
    apply tendsto_integral_filter_of_dominated_convergence oscillatorReturnKernel
      (Eventually.of_forall fun δ => (show Measurable (oscillatorRescaledReturn a T δ) from by
        unfold oscillatorRescaledReturn; fun_prop).aestronglyMeasurable)
      ((eventually_positive_visit_cutoff hT).mono fun δ hδ =>
        Eventually.of_forall (oscillator_rescaled_kernel_bound ha hδ.1 hδ.2)) hkernel
    refine Eventually.of_forall fun u => ?_
    have hc : Continuous (fun δ => oscillatorRescaledReturn a T δ u) := by
      unfold oscillatorRescaledReturn
      fun_prop
    have H := (hc.continuousAt (x := 0)).continuousWithinAt (s := Ioi (0 : ℝ))
    simpa [oscillatorRescaledReturn,oscillatorReturnKernel] using H.tendsto
  refine (hI.const_mul (C/(4*π^2))).congr' ?_
  filter_upwards [eventually_positive_visit_cutoff hT] with δ hδ
  exact (oscillator_second_moment_scale hC hδ.1).symm

private theorem odd_oscillator_mean_bounded {C a T δ : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    (hδ : 0 < δ) (hδT : δ ≤ T) :
    0 ≤ (∫ x, visitCutoff δ T x ∂oddOscillatorLaw C a) ∧
      (∫ x, visitCutoff δ T x ∂oddOscillatorLaw C a) ≤ C/(2*π) * sqrt (π/a) := by
  have hT := hδ.trans_le hδT
  rw [integral_odd_oscillator hC]
  have hn (x : ℝ) : 0 ≤ oddOscillatorDensity C a x * visitCutoff δ T x :=
    mul_nonneg (odd_density_nonneg hC _) (visit_cutoff_bounds hδ hδT _).1
  have hb (x : ℝ) : oddOscillatorDensity C a x * visitCutoff δ T x ≤ C/(2*π) * exp (-a*x^2) := by
    by_cases hx : x = 0
    · subst x
      simp [oddOscillatorDensity]
      positivity
    · simp only [oddOscillatorDensity,visitCutoff,if_neg hx]
      have he : exp (-(x^2)/T) - exp (-(x^2)/δ) ≤ 1 := by
        have hh := Real.exp_le_one_iff.mpr
          (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) hT.le)
        linarith [Real.exp_pos (-(x^2)/δ)]
      have hcalc : C * x^2 * exp (-a*x^2) * (1/(2*π) * ((exp (-(x^2)/T)-exp (-(x^2)/δ))/x^2))
          = (C/(2*π)*exp (-a*x^2)) * (exp (-(x^2)/T)-exp (-(x^2)/δ)) := by
        field_simp [Real.pi_ne_zero,hx]
      rw [hcalc]
      exact mul_le_of_le_one_right (by positivity) he
  let g (x : ℝ) := C/(2*π) * exp (-a*x^2)
  have hg : Integrable g := (integrable_exp_neg_mul_sq ha).const_mul _
  have hi : Integrable (fun x => oddOscillatorDensity C a x * visitCutoff δ T x) :=
    hg.mono' (((show Continuous (oddOscillatorDensity C a) from by unfold oddOscillatorDensity; fun_prop).measurable.mul
      (visit_cutoff_measurable δ T)).aestronglyMeasurable)
      (Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (hn x)]; exact hb x)
  have hj := integral_mono hi hg hb
  rw [show (∫ x, g x) = C/(2*π)*sqrt (π/a) by rw [integral_const_mul,integral_gaussian]] at hj
  exact ⟨integral_nonneg hn,hj⟩

theorem odd_oscillator_uncut_mean_finite {C a T : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hT : 0 < T)
    [IsProbabilityMeasure (oddOscillatorLaw C a)] :
    UV.RevisionBoundary.integratedNormalReturn T (oddOscillatorLaw C a) ≠ ⊤ := by
  let μ := oddOscillatorLaw C a
  have H := cutoff_visit_moment_tendsto_right hT μ 1
  simp_rw [pow_one] at H
  rw [uncut_visit_first_moment hT] at H
  apply ne_top_of_le_ne_top (b := ENNReal.ofReal (C/(2*π) * sqrt (π/a))) ENNReal.ofReal_ne_top
  apply le_of_tendsto H
  filter_upwards [eventually_positive_visit_cutoff hT] with δ hδ
  have hL : MemLp (visitCutoff δ T) 2 μ :=
    memLp_of_bounded (Eventually.of_forall (visit_cutoff_bounds hδ.1 hδ.2))
      (visit_cutoff_measurable δ T).aestronglyMeasurable 2
  rw [← ofReal_integral_eq_lintegral_ofReal (hL.integrable (by norm_num))
    (Eventually.of_forall fun x => (visit_cutoff_bounds hδ.1 hδ.2 x).1)]
  exact ENNReal.ofReal_le_ofReal (odd_oscillator_mean_bounded hC ha hδ.1 hδ.2).2

/-- The bounded mean contributes nothing after multiplication by the
square root of the cutoff. The second moment therefore gives the
leading coefficient of the actual normalized shared-law variance. -/
theorem odd_oscillator_variance_right_limit_of_kernel {C a T : ℝ}
    (hC : 0 ≤ C) (ha : 0 < a) (hT : 0 < T)
    [IsProbabilityMeasure (oddOscillatorLaw C a)] (hkernel : Integrable oscillatorReturnKernel) :
    Tendsto (fun δ => sqrt δ * ProbabilityTheory.variance (visitCutoff δ T) (oddOscillatorLaw C a))
      (𝓝[>] 0) (𝓝 (C / (4*π^2) * ∫ u, oscillatorReturnKernel u)) := by
  let B := C/(2*π) * sqrt (π/a)
  let M (δ : ℝ) := ∫ x, visitCutoff δ T x ∂oddOscillatorLaw C a
  have hsmall : Tendsto (fun δ => sqrt δ * (M δ)^2) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall (fun δ => by positivity)
    · filter_upwards [eventually_positive_visit_cutoff hT] with δ hδ
      have H := odd_oscillator_mean_bounded hC ha hδ.1 hδ.2
      exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ H.1 (by positivity : 0 ≤ B)).mpr H.2) (sqrt_nonneg _)
    · simpa only [sqrt_zero,zero_mul] using (continuous_sqrt.continuousAt (x := 0)).continuousWithinAt.tendsto.mul_const (B^2)
  have H := (oscillator_second_moment_right_limit hC ha.le hT hkernel).sub hsmall
  rw [sub_zero] at H
  refine H.congr' ?_
  filter_upwards [eventually_positive_visit_cutoff hT] with δ hδ
  have hL : MemLp (visitCutoff δ T) 2 (oddOscillatorLaw C a) :=
      memLp_of_bounded (Eventually.of_forall (visit_cutoff_bounds hδ.1 hδ.2))
        (visit_cutoff_measurable δ T).aestronglyMeasurable 2
  rw [ProbabilityTheory.variance_eq_sub hL, mul_sub]
  rfl

/-- Exact leading odd-oscillator constant for the variance in the
literal zero-cutoff shared-return law. -/
theorem odd_oscillator_variance_right_limit {C a T : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hT : 0 < T)
    [IsProbabilityMeasure (oddOscillatorLaw C a)] :
    Tendsto (fun δ => sqrt δ * ProbabilityTheory.variance (visitCutoff δ T) (oddOscillatorLaw C a))
      (𝓝[>] 0) (𝓝 (C * (1 - (sqrt 2)⁻¹) / π ^ (3/2 : ℝ))) := by
  obtain ⟨hi,he⟩ := ContinueVisitOscillatorIntegral.odd_oscillator_scaling_profile_integral
  change Integrable oscillatorReturnKernel at hi
  change (∫ u, oscillatorReturnKernel u) = 4 * sqrt π * (1 - (sqrt 2)⁻¹) at he
  have hpow : π ^ (3/2 : ℝ) = π * sqrt π := by
    rw [show (3/2 : ℝ) = 1 + 1/2 by norm_num, Real.rpow_add pi_pos, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hq : sqrt π / π^2 = (π * sqrt π)⁻¹ := by
    field_simp [pi_ne_zero,(sqrt_pos.mpr pi_pos).ne']
    exact sq_sqrt pi_pos.le
  have H := odd_oscillator_variance_right_limit_of_kernel hC ha hT hi
  rw [he] at H
  have heq : C / (4*π^2) * (4 * sqrt π * (1 - (sqrt 2)⁻¹)) =
      C * (1 - (sqrt 2)⁻¹) / π ^ (3/2 : ℝ) := by
    rw [hpow,div_eq_mul_inv (C * (1 - (sqrt 2)⁻¹)),← hq]
    ring
  rwa [heq] at H

theorem odd_oscillator_variance_asymptotic {C a T : ℝ} (hC : 0 < C) (ha : 0 < a) (hT : 0 < T)
    [IsProbabilityMeasure (oddOscillatorLaw C a)] :
    (fun δ => ProbabilityTheory.variance (visitCutoff δ T) (oddOscillatorLaw C a)) ~[𝓝[>] 0]
      (fun δ => C * (1 - (sqrt 2)⁻¹) / π ^ (3/2 : ℝ) / sqrt δ) := by
  let A := C * (1 - (sqrt 2)⁻¹) / π ^ (3/2 : ℝ)
  have hs : (1 : ℝ) < sqrt 2 := by
    have H := sq_sqrt (by positivity : (0:ℝ) ≤ 2)
    nlinarith [sqrt_nonneg 2]
  have hA : 0 < A := div_pos
    (mul_pos hC (sub_pos.mpr (inv_lt_one_of_one_lt₀ hs))) (rpow_pos_of_pos pi_pos _)
  have hnear : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  apply (Asymptotics.isEquivalent_iff_tendsto_one
    (hnear.mono fun δ hδ => div_ne_zero hA.ne' (sqrt_pos.mpr hδ).ne')).mpr
  have H := (odd_oscillator_variance_right_limit hC.le ha hT).div_const A
  change Tendsto (fun δ => sqrt δ * ProbabilityTheory.variance (visitCutoff δ T) (oddOscillatorLaw C a) / A)
    (𝓝[>] 0) (𝓝 (A/A)) at H
  rw [div_self hA.ne'] at H
  refine H.congr (fun δ => ?_)
  change _ = ProbabilityTheory.variance (visitCutoff δ T) (oddOscillatorLaw C a) / (A / sqrt δ)
  conv_rhs => rw [div_div_eq_mul_div]
  rw [mul_comm (sqrt δ)]

end UV.ContinueVisitOscillator
