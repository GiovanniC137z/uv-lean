import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! The positive two-line proper-time substitution, including its actual
Jacobian. Translation, Tonelli, and one-dimensional dilation prove the
identity even when either side has infinite integral. -/

noncomputable section
open MeasureTheory Set Function
open scoped ENNReal

namespace UV

theorem positive_time_translation (g : ℝ → ℝ≥0∞) (a : ℝ) :
    (∫⁻ b in Ioi (0 : ℝ), g b) = ∫⁻ S in Ioi a, g (S - a) := by
  have he : (fun b : ℝ => (Ioi a).indicator (fun S => g (S - a)) (a + b)) =
      (Ioi (0 : ℝ)).indicator g := by
    funext b
    by_cases hb : 0 < b
    · simp only [indicator_of_mem (show a + b ∈ Ioi a from (by change a < a + b; linarith)),
        indicator_of_mem (show b ∈ Ioi (0 : ℝ) from hb), add_sub_cancel_left]
    · simp only [indicator_of_notMem (show a + b ∉ Ioi a from (by change ¬a < a + b; linarith)),
        indicator_of_notMem (show b ∉ Ioi (0 : ℝ) from hb)]
  have h := lintegral_add_left_eq_self (μ := volume)
    ((Ioi a).indicator (fun S => g (S - a))) a
  rw [he, lintegral_indicator measurableSet_Ioi, lintegral_indicator measurableSet_Ioi] at h
  exact h

theorem positive_time_triangle (g : ℝ → ℝ → ℝ≥0∞) (hg : Measurable (uncurry g)) :
    (∫⁻ a in Ioi (0 : ℝ), ∫⁻ S in Ioi a, g a S) =
      ∫⁻ S in Ioi (0 : ℝ), ∫⁻ a in Ioo (0 : ℝ) S, g a S := by
  let G : ℝ → ℝ → ℝ≥0∞ := fun a S => if a < S then g a S else 0
  have hG : Measurable (uncurry G) := by
    exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd) hg measurable_const
  calc
    _ = ∫⁻ a in Ioi (0 : ℝ), ∫⁻ S in Ioi (0 : ℝ), G a S := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      have hfun : G a = (Ioi a).indicator (g a) := rfl
      rw [hfun, lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
      rw [inter_eq_left.mpr (show Ioi a ⊆ Ioi (0 : ℝ) from fun S hS =>
        (show 0 < a from ha).trans (show a < S from hS))]
    _ = ∫⁻ S in Ioi (0 : ℝ), ∫⁻ a in Ioi (0 : ℝ), G a S :=
      lintegral_lintegral_swap hG.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro S
      have hfun : (fun a => G a S) = (Iio S).indicator (fun a => g a S) := rfl
      rw [hfun, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
      have hi : Iio S ∩ Ioi (0 : ℝ) = Ioo (0 : ℝ) S := by ext a; simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo, and_comm]
      rw [hi]

theorem positive_time_dilation {S : ℝ} (hS : 0 < S) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ a in Ioo (0 : ℝ) S, g a) =
      ENNReal.ofReal S * ∫⁻ x in Ioo (0 : ℝ) 1, g (S * x) := by
  conv_lhs => rw [← Real.smul_map_volume_mul_left hS.ne']
  rw [setLIntegral_smul_measure, setLIntegral_map measurableSet_Ioo hg (measurable_const_mul S)]
  have hpre : (fun x : ℝ => S * x) ⁻¹' Ioo (0 : ℝ) S = Ioo (0 : ℝ) 1 := by
    ext x
    simp only [mem_preimage, mem_Ioo]
    constructor
    · intro hx
      exact ⟨(mul_pos_iff_of_pos_left hS).mp hx.1, (mul_lt_iff_lt_one_right hS).mp hx.2⟩
    · intro hx
      exact ⟨mul_pos hS hx.1, (mul_lt_iff_lt_one_right hS).mpr hx.2⟩
  rw [hpre, abs_of_pos hS]
  rfl

/-- Exact Feynman-time formula with α=Sx and β=S(1-x). Its only hypothesis is
joint measurability of the nonnegative extended-real integrand. -/
theorem positive_feynman_time (f : ℝ → ℝ → ℝ≥0∞) (hf : Measurable (uncurry f)) :
    (∫⁻ a in Ioi (0 : ℝ), ∫⁻ b in Ioi (0 : ℝ), f a b) =
      ∫⁻ S in Ioi (0 : ℝ), ENNReal.ofReal S *
        ∫⁻ x in Ioo (0 : ℝ) 1, f (S * x) (S * (1 - x)) := by
  have hg : Measurable (uncurry (fun a S : ℝ => f a (S - a))) :=
    hf.comp (measurable_fst.prodMk (measurable_snd.sub measurable_fst))
  calc
    _ = ∫⁻ a in Ioi (0 : ℝ), ∫⁻ S in Ioi a, f a (S - a) := by
      apply lintegral_congr
      intro a
      exact positive_time_translation (f a) a
    _ = ∫⁻ S in Ioi (0 : ℝ), ∫⁻ a in Ioo (0 : ℝ) S, f a (S - a) :=
      positive_time_triangle _ hg
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with S hS
      rw [positive_time_dilation hS (fun a => f a (S - a))
        (hf.comp (measurable_id.prodMk (measurable_const.sub measurable_id)))]
      congr 1
      apply lintegral_congr
      intro x
      congr 1
      ring

theorem positive_feynman_time_prod (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) =
      ∫⁻ p, ENNReal.ofReal p.1 * f (p.1 * p.2, p.1 * (1 - p.2))
        ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 *
      f (p.1 * p.2, p.1 * (1 - p.2))) := by fun_prop
  rw [lintegral_prod _ hf.aemeasurable, lintegral_prod _ hm.aemeasurable]
  rw [positive_feynman_time (fun a b => f (a, b)) hf]
  apply lintegral_congr
  intro S
  exact (lintegral_const_mul' (ENNReal.ofReal S) _ ENNReal.ofReal_ne_top).symm

/-- Real, nonnegative form. Measurability and positivity suffice; no
integrability of either parametrization is assumed. If the integral is
infinite both real Bochner integrals use their ordinary total value zero. -/
theorem positive_feynman_time_real (f : ℝ × ℝ → ℝ) (hf : Measurable f)
    (h0 : ∀ a > 0, ∀ b > 0, 0 ≤ f (a, b)) :
    (∫ p, f p ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) =
      ∫ p, p.1 * f (p.1 * p.2, p.1 * (1 - p.2))
        ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have hparams₁ : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))),
      0 < p.1 ∧ 0 < p.2 :=
    ((Measure.quasiMeasurePreserving_fst).ae (ae_restrict_mem measurableSet_Ioi)).and
      ((Measure.quasiMeasurePreserving_snd).ae (ae_restrict_mem measurableSet_Ioi))
  have hparams₂ : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1)),
      0 < p.1 ∧ p.2 ∈ Ioo (0 : ℝ) 1 :=
    ((Measure.quasiMeasurePreserving_fst).ae (ae_restrict_mem measurableSet_Ioi)).and
      ((Measure.quasiMeasurePreserving_snd).ae (ae_restrict_mem measurableSet_Ioo))
  have hleft : 0 ≤ᵐ[(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))] f := by
    filter_upwards [hparams₁] with p hp
    exact h0 p.1 hp.1 p.2 hp.2
  have hright : 0 ≤ᵐ[(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1))]
      (fun p : ℝ × ℝ => p.1 * f (p.1 * p.2, p.1 * (1 - p.2))) := by
    filter_upwards [hparams₂] with p hp
    exact mul_nonneg hp.1.le (h0 _ (mul_pos hp.1 hp.2.1) _ (mul_pos hp.1 (sub_pos.mpr hp.2.2)))
  have hmeas : Measurable (fun p : ℝ × ℝ => p.1 * f (p.1 * p.2, p.1 * (1 - p.2))) := by fun_prop
  rw [integral_eq_lintegral_of_nonneg_ae hleft hf.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae hright hmeas.aestronglyMeasurable]
  congr 1
  rw [positive_feynman_time_prod (fun p => ENNReal.ofReal (f p)) hf.ennreal_ofReal]
  apply lintegral_congr_ae
  filter_upwards [hparams₂] with p hp
  exact (ENNReal.ofReal_mul hp.1.le).symm

/-- Absolute integrability is equivalent under the genuine proper-time
substitution; the Jacobian multiplies the transformed integrand. -/
theorem positive_feynman_time_integrable_iff (f : ℝ × ℝ → ℝ) (hf : Measurable f) :
    Integrable f ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) ↔
      Integrable (fun p : ℝ × ℝ => p.1 * f (p.1 * p.2, p.1 * (1 - p.2)))
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hmeas : Measurable (fun p : ℝ × ℝ => p.1 * f (p.1 * p.2, p.1 * (1 - p.2))) := by fun_prop
  have he := positive_feynman_time_prod (fun p => ‖f p‖ₑ) hf.enorm
  have hright : (∫⁻ p, ENNReal.ofReal p.1 * ‖f (p.1 * p.2, p.1 * (1 - p.2))‖ₑ
      ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1))) =
      ∫⁻ p, ‖p.1 * f (p.1 * p.2, p.1 * (1 - p.2))‖ₑ
        ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1)) := by
    apply lintegral_congr_ae
    filter_upwards [(Measure.quasiMeasurePreserving_fst).ae (ae_restrict_mem measurableSet_Ioi)] with p hp
    rw [enorm_mul, Real.enorm_eq_ofReal hp.le]
  rw [hright] at he
  constructor
  · intro h
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, ← he]
    exact (hasFiniteIntegral_iff_enorm.mp h.2)
  · intro h
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, he]
    exact (hasFiniteIntegral_iff_enorm.mp h.2)

/-- The common positive proper-time envelope after taking one external
subtraction. This definition retains the literal two proper times. -/
def feynmanTimeEnvelope (m : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-m ^ 2 * (p.1 + p.2)) / (p.1 + p.2)

theorem feynman_time_envelope_measurable (m : ℝ) : Measurable (feynmanTimeEnvelope m) := by
  unfold feynmanTimeEnvelope
  fun_prop

theorem feynman_time_envelope_rescaled {m : ℝ} {p : ℝ × ℝ} (hp : 0 < p.1) :
    p.1 * feynmanTimeEnvelope m (p.1 * p.2, p.1 * (1 - p.2)) = Real.exp (-m ^ 2 * p.1) := by
  unfold feynmanTimeEnvelope
  have hsum : p.1 * p.2 + p.1 * (1 - p.2) = p.1 := by ring
  dsimp only
  rw [hsum]
  field_simp [hp.ne']

theorem feynman_time_envelope_integrable {m : ℝ} (hm : 0 < m) :
    Integrable (feynmanTimeEnvelope m)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  apply (positive_feynman_time_integrable_iff _ (feynman_time_envelope_measurable m)).mpr
  have hi : IntegrableOn (fun S : ℝ => Real.exp (-m ^ 2 * S)) (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (sq_pos_of_pos hm)) 0
  apply (hi.comp_fst (volume.restrict (Ioo (0 : ℝ) 1))).congr
  filter_upwards [(Measure.quasiMeasurePreserving_fst).ae (ae_restrict_mem measurableSet_Ioi)] with p hp
  exact (feynman_time_envelope_rescaled (m := m) hp).symm

theorem feynman_time_envelope_integral {m : ℝ} (hm : 0 < m) :
    (∫ p, feynmanTimeEnvelope m p
      ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) = 1 / m ^ 2 := by
  rw [positive_feynman_time_real _ (feynman_time_envelope_measurable m)
    (fun a ha b hb => div_nonneg (Real.exp_nonneg _) (by dsimp; linarith))]
  have he : (fun p : ℝ × ℝ => p.1 * feynmanTimeEnvelope m (p.1 * p.2, p.1 * (1 - p.2))) =ᵐ[
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1))]
      (fun p => Real.exp (-m ^ 2 * p.1)) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst).ae (ae_restrict_mem measurableSet_Ioi)] with p hp
    exact feynman_time_envelope_rescaled hp
  rw [integral_congr_ae he]
  have hi : IntegrableOn (fun S : ℝ => Real.exp (-m ^ 2 * S)) (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (sq_pos_of_pos hm)) 0
  rw [integral_prod _ (hi.comp_fst (volume.restrict (Ioo (0 : ℝ) 1)))]
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo,
    sub_zero, ENNReal.toReal_ofReal zero_le_one, one_smul]
  rw [integral_exp_mul_Ioi (neg_lt_zero.mpr (sq_pos_of_pos hm)) 0]
  simp

end UV
