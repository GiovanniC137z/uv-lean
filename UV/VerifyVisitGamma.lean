import UV.RevisionBoundaryHeat
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! Positive proper-time integration for the midpoint Gaussian in
any positive number of measured normal coordinates. -/

noncomputable section

open MeasureTheory Filter Set Real
open scoped ENNReal Topology

namespace UV.VerifyVisitGamma

/-- Upper incomplete Gamma with shape n + 1, in its defining positive
Euler integral. The real-valued integral is recovered on the positive ray. -/
def upperGamma (n : ℕ) (a : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in Ici a, ENNReal.ofReal (Real.exp (-u) * u ^ n)

theorem upper_gamma_antitone (n : ℕ) : Antitone (upperGamma n) :=
  fun _ _ h => lintegral_mono_set (Ici_subset_Ici.mpr h)

theorem upper_gamma_eq_ofReal (n : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    upperGamma n a = ENNReal.ofReal (∫ u in Ici a, Real.exp (-u) * u ^ n) := by
  have hG : IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ n) (Ioi 0) := by
    have h := Real.GammaIntegral_convergent (s := (n : ℝ) + 1) (by positivity)
    simpa only [add_sub_cancel_right, Real.rpow_natCast] using h
  have hi0 : IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ n) (Ici 0) := by
    rwa [integrableOn_Ici_iff_integrableOn_Ioi]
  have hi : IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ n) (Ici a) :=
    hi0.mono_set (Ici_subset_Ici.mpr ha)
  exact (ofReal_integral_eq_lintegral_ofReal hi (by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    exact mul_nonneg (Real.exp_nonneg _) (pow_nonneg (ha.trans hu) _))).symm

theorem upper_gamma_ne_top (n : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    upperGamma n a ≠ ⊤ := by
  rw [upper_gamma_eq_ofReal n ha]
  exact ENNReal.ofReal_ne_top

theorem upper_gamma_pos (n : ℕ) {a : ℝ} (ha : 0 < a) :
    0 < upperGamma n a := by
  let c := Real.exp (-(a + 1)) * a ^ n
  have hc : 0 < c := mul_pos (Real.exp_pos _) (pow_pos ha _)
  have hle : (∫⁻ _ in Ioc a (a + 1), ENNReal.ofReal c) ≤ upperGamma n a := by
    calc
      _ ≤ ∫⁻ u in Ioc a (a + 1), ENNReal.ofReal (Real.exp (-u) * u ^ n) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        exact ENNReal.ofReal_le_ofReal (mul_le_mul (Real.exp_le_exp.mpr (neg_le_neg hu.2))
          (pow_le_pow_left₀ ha.le hu.1.le _) (pow_nonneg ha.le _) (Real.exp_nonneg _))
      _ ≤ _ := lintegral_mono_set (by intro u hu; exact hu.1.le)
  have hmass : volume (Ioc a (a + 1)) = 1 := by
    rw [Real.volume_Ioc, add_sub_cancel_left, ENNReal.ofReal_one]
  rw [setLIntegral_const, hmass, mul_one] at hle
  exact (ENNReal.ofReal_pos.mpr hc).trans_le hle

def normalTimeIntegrand (n : ℕ) (D t : ℝ) : ℝ :=
  Real.exp (-D / t) / t ^ (n + 2)

private theorem normal_time_inv_chart_image {D T : ℝ} (hD : 0 < D) (hT : 0 < T) :
    (fun t : ℝ => D / t) '' Ioc 0 T = Ici (D / T) := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact div_le_div_of_nonneg_left hD.le ht.1 ht.2
  · intro hu
    have hu' : D / T ≤ u := hu
    have hu0 : 0 < u := (div_pos hD hT).trans_le hu'
    refine ⟨D / u, ⟨div_pos hD hu0, (div_le_iff₀ hu0).mpr ?_⟩, ?_⟩
    · simpa only [mul_comm T u] using (div_le_iff₀ hT).mp hu'
    · field_simp [hD.ne']

/-- The actual inverse-time coordinate D/t sends (0,T] to
the upper incomplete Gamma tail, with the exact D^(-(n+1)) factor. -/
theorem normal_time_gamma_exact (n : ℕ) {D T : ℝ} (hD : 0 < D) (hT : 0 < T) :
    (∫⁻ t in Ioc (0 : ℝ) T, ENNReal.ofReal (normalTimeIntegrand n D t)) =
      ENNReal.ofReal ((D ^ (n + 1))⁻¹) * upperGamma n (D / T) := by
  have hι : InjOn (fun t : ℝ => D / t) (Ioc 0 T) := by
    intro x hx y hy hh
    have hm : D * y = D * x := (div_eq_div_iff hx.1.ne' hy.1.ne').mp hh
    exact (mul_left_cancel₀ hD.ne' hm).symm
  have hd (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) :
      HasDerivWithinAt (fun s : ℝ => D / s) (-D / t ^ (2 : ℕ)) (Ioc 0 T) t := by
    apply HasDerivAt.hasDerivWithinAt
    convert (hasDerivAt_const t D).div (hasDerivAt_id t) ht.1.ne' using 1
    simp
  let g := fun u : ℝ => ENNReal.ofReal ((D ^ (n + 1))⁻¹) * ENNReal.ofReal (Real.exp (-u) * u ^ n)
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioc hd hι g
  rw [normal_time_inv_chart_image hD hT] at h
  calc
    _ = ∫⁻ t in Ioc (0 : ℝ) T,
        ENNReal.ofReal (|-D / t ^ (2 : ℕ)|) * g (D / t) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      have hD2 : 0 ≤ (D ^ (n + 1))⁻¹ := by positivity
      have hDt : 0 ≤ D / t ^ (2 : ℕ) := by positivity
      unfold g normalTimeIntegrand
      rw [abs_div, abs_neg, abs_of_pos hD, abs_of_nonneg (sq_nonneg t), ← ENNReal.ofReal_mul hD2,
        ← ENNReal.ofReal_mul hDt]
      congr 1
      rw [div_pow, pow_succ D n, show t ^ (n + 2) = t ^ n * t ^ (2 : ℕ) by rw [pow_add]]
      field_simp [hD.ne', ht0.ne']
    _ = ∫⁻ u in Ici (D / T), g u := h.symm
    _ = _ := by
      unfold g upperGamma
      rw [lintegral_const_mul _ (by fun_prop)]

theorem normal_time_zero_cost (n : ℕ) {T : ℝ} (hT : 0 < T) :
    (∫⁻ t in Ioc (0 : ℝ) T, ENNReal.ofReal (normalTimeIntegrand n 0 t)) = ⊤ := by
  by_contra hinf
  have hfmeas : Measurable (normalTimeIntegrand n 0) := by unfold normalTimeIntegrand; fun_prop
  have hi : IntegrableOn (normalTimeIntegrand n 0) (Ioc 0 T) :=
    (lintegral_ofReal_ne_top_iff_integrable hfmeas.aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      unfold normalTimeIntegrand
      exact div_nonneg (Real.exp_nonneg _) (pow_nonneg ht.1.le _))).mp hinf
  have hi' : IntegrableOn (fun t : ℝ => t ^ (-((n : ℝ) + 2))) (Ioo 0 T) := by
    refine (hi.mono_set Ioo_subset_Ioc_self).congr_fun ?_ measurableSet_Ioo
    intro t ht
    simp only [normalTimeIntegrand, neg_zero, zero_div, Real.exp_zero]
    rw [← Nat.cast_ofNat (R := ℝ) (n := 2), ← Nat.cast_add, Real.rpow_neg ht.1.le, Real.rpow_natCast]
    simp [one_div]
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff hT).mp hi'
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

end UV.VerifyVisitGamma
