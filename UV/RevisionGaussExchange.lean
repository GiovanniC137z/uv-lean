import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.Basic

/-! A positive spectral weight forces divergence of instantaneous electric exchange
at the level of a scalar positive spectral matrix element. -/

namespace UV.RevisionGaussExchange

open MeasureTheory Filter Set
open scoped Topology

noncomputable def chargeResolvent (μ : Measure ℝ) (u : ℝ) : ℂ :=
  ∫ E, ((E : ℂ) + (u : ℂ) * Complex.I)⁻¹ ∂μ

theorem charge_resolvent_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    {u : ℝ} (hu : 0 < u) :
    Integrable (fun E : ℝ => ((E : ℂ) + (u : ℂ) * Complex.I)⁻¹) μ := by
  have hm : Measurable (fun E : ℝ => ((E : ℂ) + (u : ℂ) * Complex.I)⁻¹) := by
    fun_prop
  refine (integrable_const (u⁻¹)).mono' hm.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun E => ?_
  rw [norm_inv]
  apply inv_anti₀ hu
  simpa [abs_of_pos hu] using Complex.abs_im_le_norm ((E : ℂ) + (u : ℂ) * Complex.I)

theorem charge_resolvent_im (μ : Measure ℝ) [IsFiniteMeasure μ] {u : ℝ} (hu : 0 < u) :
    -u * (chargeResolvent μ u).im = ∫ E, u ^ 2 / (u ^ 2 + E ^ 2) ∂μ := by
  have hi := charge_resolvent_integrable μ hu
  unfold chargeResolvent
  rw [← Complex.imCLM_apply, ← Complex.imCLM.integral_comp_comm hi, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun E => ?_)
  simp only [Complex.imCLM_apply, Complex.inv_im, Complex.add_im,
    Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_re,
    mul_one, mul_zero, add_zero, zero_add, Complex.normSq_apply, Complex.add_re,
    Complex.mul_re, sub_zero]
  ring_nf

theorem charge_resolvent_mass (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto (fun u => -u * (chargeResolvent μ u).im) atTop (𝓝 (μ Set.univ).toReal) := by
  suffices h : Tendsto (fun u : ℝ => ∫ E : ℝ, u ^ 2 / (u ^ 2 + E ^ 2) ∂μ)
      atTop (𝓝 (∫ _ : ℝ, (1 : ℝ) ∂μ)) by
    have h' := h.congr' ((eventually_gt_atTop (0 : ℝ)).mono fun _ hu =>
      (charge_resolvent_im μ hu).symm)
    simpa using h'
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => 1) ?_ ?_
    (integrable_const 1) ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have hden (E : ℝ) : u ^ 2 + E ^ 2 ≠ 0 := ne_of_gt (by positivity)
    exact (continuous_const.div (by fun_prop) hden).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    refine Filter.Eventually.of_forall fun E => ?_
    have hden : 0 < u ^ 2 + E ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hden.le)]
    exact (div_le_one hden).mpr (le_add_of_nonneg_right (sq_nonneg _))
  · refine Filter.Eventually.of_forall fun E => ?_
    have h0 : Tendsto (fun u : ℝ => (1 + E ^ 2 * (u⁻¹) ^ 2)⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
        ((tendsto_const_nhds (x := E ^ 2)).mul (tendsto_inv_atTop_zero.pow 2)) |>.inv₀ (by simp)
    refine h0.congr' ((eventually_gt_atTop (0 : ℝ)).mono fun u hu => ?_)
    have hd : u ^ 2 + E ^ 2 ≠ 0 := ne_of_gt (by positivity)
    have hh : 1 + E ^ 2 * (u⁻¹) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp

theorem charge_resolvent_mass_monotone (μ : Measure ℝ) [IsFiniteMeasure μ] :
    MonotoneOn (fun u => -u * (chargeResolvent μ u).im) (Ioi (0 : ℝ)) := by
  intro u hu v hv huv
  change -u * (chargeResolvent μ u).im ≤ -v * (chargeResolvent μ v).im
  rw [charge_resolvent_im μ hu, charge_resolvent_im μ hv]
  have hint (x : ℝ) (hx : 0 < x) :
      Integrable (fun E : ℝ => x ^ 2 / (x ^ 2 + E ^ 2)) μ := by
    have hden (E : ℝ) : x ^ 2 + E ^ 2 ≠ 0 := ne_of_gt (by positivity)
    refine (integrable_const 1).mono' (continuous_const.div (by fun_prop) hden).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun E => ?_
    have hp : 0 < x ^ 2 + E ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (div_le_one hp).mpr (le_add_of_nonneg_right (sq_nonneg _))
  refine integral_mono (hint u hu) (hint v hv) fun E => ?_
  rw [div_le_div_iff₀ (add_pos_of_pos_of_nonneg (sq_pos_of_pos hu) (sq_nonneg E))
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos hv) (sq_nonneg E))]
  have hsq : u ^ 2 ≤ v ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr huv) (add_nonneg (le_of_lt hv) (le_of_lt hu))]
  nlinarith [mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg E)]

/-- A positive scalar spectral measure, however small its mass, gives a
nonintegrable carrier-frequency exchange for every positive Coulomb weight. -/
theorem instantaneous_exchange_fibre (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ Set.univ ≠ 0) {c : ℝ} (hc : 0 < c) :
    ¬ Integrable (fun u => (c : ℂ) * chargeResolvent μ u) := by
  intro hi
  let m := (μ Set.univ).toReal
  have hm : 0 < m := ENNReal.toReal_pos hμ (measure_ne_top μ _)
  have ht := (charge_resolvent_mass μ).eventually (lt_mem_nhds (half_lt_self hm))
  obtain ⟨R, hR⟩ := eventually_atTop.1 ht
  let B := max R 1
  have hB : 0 < B := zero_lt_one.trans_le (le_max_right _ _)
  have htail : IntegrableOn (fun u : ℝ => (c * (m / 2)) * u⁻¹) (Ioi B) := by
    have hrest : Integrable (fun u => (c : ℂ) * chargeResolvent μ u) (volume.restrict (Ioi B)) :=
      hi.integrableOn
    refine hrest.norm.mono' (by fun_prop) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun u hu => ?_
    have hu0 : 0 < u := hB.trans hu
    have hRu : R ≤ u := (le_max_left _ _).trans hu.le
    have huest : m / 2 ≤ u * ‖chargeResolvent μ u‖ := by
      calc
        _ ≤ -u * (chargeResolvent μ u).im := (hR u hRu).le
        _ ≤ u * ‖chargeResolvent μ u‖ := by
          rw [neg_mul, ← mul_neg]
          exact mul_le_mul_of_nonneg_left ((neg_le_abs _).trans (Complex.abs_im_le_norm _)) hu0.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (by
      rw [← div_eq_mul_inv, div_le_iff₀ hu0]
      simpa only [mul_comm] using huest) hc.le
  have hinv : IntegrableOn (fun u : ℝ => u⁻¹) (Ioi B) := by
    have h : IntegrableOn (fun u : ℝ => (c * (m / 2))⁻¹ * ((c * (m / 2)) * u⁻¹))
        (Ioi B) := htail.const_mul (c * (m / 2))⁻¹
    refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have hp : IntegrableOn (fun u : ℝ => u ^ (-1 : ℝ)) (Ioi B) := by
    simpa [Real.rpow_neg_one] using hinv
  exact (lt_irrefl (-1 : ℝ)) ((integrableOn_Ioi_rpow_iff hB).mp hp)

/-- Tonelli/Fubini forces the full absolute integral to diverge if positive
spectral mass and positive instantaneous weight occur on a non-null set
of spatial transfers. There is no uniform carrier threshold assumption. -/
theorem instantaneous_exchange_nonintegrable {P : Type*} [MeasurableSpace P]
    (ν : Measure P) [SFinite ν] (μ : P → Measure ℝ)
    (c : P → ℝ) (S : Set P) (hS : ν S ≠ 0)
    (hμ : ∀ p ∈ S, μ p Set.univ ≠ 0) (hfin : ∀ p ∈ S, IsFiniteMeasure (μ p))
    (hc : ∀ p ∈ S, 0 < c p) :
    ¬ Integrable (fun x : P × ℝ => (c x.1 : ℂ) * chargeResolvent (μ x.1) x.2)
      (ν.prod volume) := by
  intro h
  have habs : ∀ᵐ p ∂ν, p ∉ S := h.prod_right_ae.mono fun p hf hp => by
    letI := hfin p hp
    exact instantaneous_exchange_fibre (μ p) (hμ p hp) (hc p hp) hf
  exact hS (by simpa using ae_iff.mp habs)

end UV.RevisionGaussExchange
