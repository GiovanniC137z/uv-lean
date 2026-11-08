import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-! A positive Frullani identity from actual parameter integrals and Fubini. -/

noncomputable section
open MeasureTheory Filter Set Real
open scoped Topology

namespace UV

def frullaniIntegrand (b c S : ℝ) : ℝ :=
  Real.exp (-b * S) * (1 - Real.exp (-c * S)) / S

theorem frullani_integrand_nonneg {b c S : ℝ} (hc : 0 ≤ c) (hS : 0 ≤ S) :
    0 ≤ frullaniIntegrand b c S := by
  unfold frullaniIntegrand
  exact div_nonneg (mul_nonneg (Real.exp_nonneg _)
    (sub_nonneg.mpr (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) hS)))) hS

theorem frullani_integrable {b c : ℝ} (hb : 0 < b) (hc : 0 ≤ c) :
    IntegrableOn (frullaniIntegrand b c) (Ioi 0) := by
  have hi : IntegrableOn (fun S : ℝ => Real.exp (-b * S)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  apply (hi.const_mul c).mono'
  · exact (by unfold frullaniIntegrand; fun_prop : Measurable (frullaniIntegrand b c)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with S hS
    rw [Real.norm_of_nonneg (frullani_integrand_nonneg hc hS.le)]
    have hlin : 1 - Real.exp (-c * S) ≤ c * S := by
      have hh := Real.add_one_le_exp (-c * S)
      linarith
    unfold frullaniIntegrand
    calc
      _ ≤ Real.exp (-b * S) * (c * S) / S :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlin (Real.exp_nonneg _)) hS.le
      _ = c * Real.exp (-b * S) := by field_simp [ne_of_gt (show 0 < S from hS)]

theorem frullani_parameter_integral {b c S : ℝ} (hc : 0 ≤ c) (hS : 0 < S) :
    (∫ t in Ioc (0 : ℝ) c, Real.exp (-(b + t) * S)) = frullaniIntegrand b c S := by
  rw [← intervalIntegral.integral_of_le hc]
  have hder : ∀ t ∈ Set.uIcc (0 : ℝ) c,
      HasDerivAt (fun t : ℝ => Real.exp (-(b + t) * S) / (-S))
        (Real.exp (-(b + t) * S)) t := by
    intro t _
    have hh := ((((hasDerivAt_id t).const_add b).neg.mul_const S).exp).div_const (-S)
    convert hh using 1
    simp only [id_eq, Pi.neg_apply]
    field_simp
  have hi : IntervalIntegrable (fun t : ℝ => Real.exp (-(b + t) * S)) volume 0 c :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (-(b + t) * S))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hi]
  have he : Real.exp (-(b + c) * S) = Real.exp (-b * S) * Real.exp (-c * S) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  unfold frullaniIntegrand
  simp only [add_zero]
  ring

theorem frullani_joint_integrable {b c : ℝ} (hb : 0 < b) :
    Integrable (fun p : ℝ × ℝ => Real.exp (-(b + p.2) * p.1))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc 0 c))) := by
  have hS : IntegrableOn (fun S : ℝ => Real.exp (-b * S)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have ht : IntegrableOn (fun _t : ℝ => (1 : ℝ)) (Ioc 0 c) := integrable_const _
  have hmajor := hS.mul_prod ht
  apply hmajor.mono'
  · exact (by fun_prop : Continuous (fun p : ℝ × ℝ =>
      Real.exp (-(b + p.2) * p.1))).aestronglyMeasurable
  · have hSae := (Measure.quasiMeasurePreserving_fst
      (μ := volume.restrict (Ioi (0 : ℝ))) (ν := volume.restrict (Ioc (0 : ℝ) c))).ae
      (ae_restrict_mem measurableSet_Ioi)
    have htae := (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (Ioi (0 : ℝ))) (ν := volume.restrict (Ioc (0 : ℝ) c))).ae
      (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hSae, htae] with p hpS hpt
    rw [Real.norm_of_nonneg (Real.exp_nonneg _), mul_one]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hpt.1.le hpS.le]

theorem frullani_integral {b c : ℝ} (hb : 0 < b) (hc : 0 ≤ c) :
    (∫ S in Ioi (0 : ℝ), frullaniIntegrand b c S) = Real.log (1 + c / b) := by
  have hswap := integral_integral_swap
    (μ := volume.restrict (Ioi (0 : ℝ))) (ν := volume.restrict (Ioc (0 : ℝ) c))
    (f := fun S t : ℝ => Real.exp (-(b + t) * S)) (frullani_joint_integrable hb)
  have hinnerS : ∀ t ∈ Ioc (0 : ℝ) c,
      (∫ S in Ioi (0 : ℝ), Real.exp (-(b + t) * S)) = 1 / (b + t) := by
    intro t ht
    have hp : 0 < b + t := by linarith [ht.1]
    have hh := integral_exp_mul_Ioi (a := -(b + t)) (by linarith) 0
    simpa only [mul_zero, Real.exp_zero, neg_div_neg_eq, neg_neg] using hh
  calc
    _ = ∫ S in Ioi (0 : ℝ), ∫ t in Ioc (0 : ℝ) c, Real.exp (-(b + t) * S) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro S hS
      exact (frullani_parameter_integral hc hS).symm
    _ = ∫ t in Ioc (0 : ℝ) c, ∫ S in Ioi (0 : ℝ), Real.exp (-(b + t) * S) := hswap
    _ = ∫ t in Ioc (0 : ℝ) c, 1 / (b + t) := setIntegral_congr_fun measurableSet_Ioc hinnerS
    _ = Real.log (1 + c / b) := by
      rw [← intervalIntegral.integral_of_le hc]
      have hder : ∀ t ∈ Set.uIcc (0 : ℝ) c,
          HasDerivAt (fun t : ℝ => Real.log (b + t)) (1 / (b + t)) t := by
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) c := by simpa only [uIcc_of_le hc] using ht
        exact ((hasDerivAt_id t).const_add b).log
          (by simpa only [id_eq] using (ne_of_gt (add_pos_of_pos_of_nonneg hb ht'.1)))
      have hi : IntervalIntegrable (fun t : ℝ => 1 / (b + t)) volume 0 c := by
        apply ContinuousOn.intervalIntegrable
        apply continuousOn_const.div (continuous_const.add continuous_id).continuousOn
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) c := by simpa only [uIcc_of_le hc] using ht
        simpa only [id_eq] using (ne_of_gt (add_pos_of_pos_of_nonneg hb ht'.1))
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hi, add_zero,
        ← Real.log_div (by linarith : b + c ≠ 0) hb.ne']
      congr 1
      field_simp

end UV
