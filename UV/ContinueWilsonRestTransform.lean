import UV.ContinueWilsonChargedPole
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! The compact hop law controls growth in complex energy. Absolute
continuity of the displacement marginal gives both imaginary-axis limits. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology FourierTransform ENNReal

namespace UV

theorem WilsonRestLaw.complex_block_growth {L : ℝ} (D : WilsonRestLaw L) {σ : ℝ} (hσ : |σ| ≤ 1) (z : ℂ) :
    ‖D.complexBlock σ 0 z‖ ≤ Real.exp (2*L*‖z‖) := by
  rw [D.complex_block_integral]
  have hi := (D.block_integrable σ 0 0).mul_const (Real.exp (2*L*‖z‖))
  simp only [pow_zero,zero_mul,Real.exp_zero,mul_one] at hi
  calc
    _ ≤ ∫ s, ‖(wilsonTimeWeight L σ s : ℂ)*Complex.exp (z*(s:ℂ))‖ ∂D.law := norm_integral_le_integral_norm _
    _ ≤ ∫ s, wilsonTimeWeight L σ s * Real.exp (2*L*‖z‖) ∂D.law := by
      apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => norm_nonneg _)) hi
      filter_upwards [D.band] with s hs
      have hw := wilsonTimeWeight_nonneg D.length_pos hσ hs
      have hr : (z*(s:ℂ)).re ≤ 2*L*‖z‖ := by
        calc
          _ ≤ ‖z*(s:ℂ)‖ := Complex.re_le_norm _
          _ = |s| * ‖z‖ := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_comm]
          _ ≤ _ := mul_le_mul_of_nonneg_right hs (norm_nonneg z)
      simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw,Complex.norm_exp]
        using mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hr) hw
    _ = _ := by
      rw [integral_mul_const]
      have hw := D.block_at_zero σ
      simp only [WilsonRestLaw.block,pow_zero,zero_mul,Real.exp_zero,mul_one] at hw
      rw [hw,one_mul]

theorem WilsonRestLaw.rest_denominator_growth {L : ℝ} (D : WilsonRestLaw L) (lam : ℝ) {σ : ℝ}
    (hσ : |σ| ≤ 1) (z : ℂ) : ‖D.restDenominator lam σ z‖ ≤ Real.exp (|lam| + 2*L*‖z‖) := by
  have hL := D.length_pos
  have hp : 0 ≤ 2*L*‖z‖ := by positivity
  calc
    _ ≤ ‖(1:ℂ)‖ + ‖(lam:ℂ)*D.complexBlock σ 0 z‖ := norm_sub_le _ _
    _ ≤ 1 + |lam| * Real.exp (2*L*‖z‖) := by
      rw [norm_one,norm_mul,Complex.norm_real,Real.norm_eq_abs]
      gcongr
      exact D.complex_block_growth hσ z
    _ ≤ (1+|lam|)*Real.exp (2*L*‖z‖) := by
      have := Real.one_le_exp hp
      linarith
    _ ≤ _ := by rw [Real.exp_add]; gcongr; linarith [Real.add_one_le_exp |lam|]

/-- The angular frequency is `t`, while mathlib's transform uses cycles:
the matching transform argument is `-t/(2π)`. -/
theorem WilsonRestLaw.complex_block_fourier {L : ℝ} (D : WilsonRestLaw L) (σ : ℝ)
    {ρ : ℝ → ℝ≥0∞} (hρ : Measurable ρ) (hfin : ∀ᵐ s ∂volume, ρ s < ⊤)
    (hlaw : D.law = volume.withDensity ρ) (t : ℝ) :
    D.complexBlock σ 0 ((t:ℂ)*Complex.I) =
      𝓕 (fun s : ℝ => (((ρ s).toReal * wilsonTimeWeight L σ s : ℝ):ℂ)) (-t/(2*Real.pi)) := by
  rw [D.complex_block_integral,hlaw,integral_withDensity_eq_integral_toReal_smul hρ hfin,
    Real.fourierIntegral_real_eq_integral_exp_smul]
  congr 1
  funext s
  change ((ρ s).toReal:ℂ) * ((wilsonTimeWeight L σ s:ℂ) * _) = _ * _
  have he : -2*Real.pi*s*(-t/(2*Real.pi)) = t*s := by field_simp [Real.pi_ne_zero]
  rw [he]
  simp only [Complex.ofReal_mul]
  ring_nf

theorem WilsonRestLaw.rest_denominator_imaginary_limits {L : ℝ} (D : WilsonRestLaw L) (lam σ : ℝ)
    (hac : D.law ≪ volume) :
    Tendsto (fun t : ℝ => D.restDenominator lam σ ((t:ℂ)*Complex.I)) (cocompact ℝ) (𝓝 1) := by
  let ρ := D.law.rnDeriv volume
  have hlaw : D.law = volume.withDensity ρ := (Measure.withDensity_rnDeriv_eq _ _ hac).symm
  have hf := Real.zero_at_infty_fourierIntegral (fun s : ℝ => (((ρ s).toReal * wilsonTimeWeight L σ s : ℝ):ℂ))
  have hscale : Tendsto (fun t : ℝ => -t/(2*Real.pi)) (cocompact ℝ) (cocompact ℝ) := by
    rw [cocompact_eq_atBot_atTop, tendsto_sup]
    constructor
    · apply Tendsto.mono_right _ le_sup_right
      exact (tendsto_neg_atBot_atTop.atTop_div_const (by positivity))
    · apply Tendsto.mono_right _ le_sup_left
      exact (tendsto_neg_atTop_atBot.atBot_div_const (by positivity))
  have hF : Tendsto (fun t : ℝ => D.complexBlock σ 0 ((t:ℂ)*Complex.I)) (cocompact ℝ) (𝓝 0) :=
    (hf.comp hscale).congr (fun t => (D.complex_block_fourier σ (Measure.measurable_rnDeriv _ _)
      (Measure.rnDeriv_lt_top _ _) hlaw t).symm)
  simpa only [mul_zero,sub_zero] using
    (tendsto_const_nhds (x := (1:ℂ))).sub ((tendsto_const_nhds (x := (lam:ℂ))).mul hF)

end UV
