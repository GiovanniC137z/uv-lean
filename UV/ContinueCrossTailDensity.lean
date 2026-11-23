import UV.ContinueCrossTailMeasure
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The exact large-(k) variation density and its integrable error.
The radial variable is (k=sqrt{s-M^2}) with (s) on the spectral
mass-squared axis of the fixed plane. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace UV.RevisionSpectrum

theorem crossTailDensity_momentum_formula {a M m₂ k : ℝ} (hk : 0 < k)
    (hd : 0 < k^2+(M^2-m₂)) :
    (2*k)*crossTailDensity a M m₂ (k^2+M^2) =
      (2*Real.exp (a*M)/Real.pi)*|Real.sin (a*k)| *(k/(k^2+(M^2-m₂))) := by
  have hcut : M^2 < k^2+M^2 := by linarith [sq_pos_of_pos hk]
  have hne : k^2+M^2 ≠ m₂ := by linarith
  have hd' : m₂-(k^2+M^2) = -(k^2+(M^2-m₂)) := by ring
  rw [crossTailDensity, verifyCrossContinuum, if_neg (fun h => hne h.1), crossDensity,
    if_pos hcut, show k^2+M^2-M^2 = k^2 by ring, Real.sqrt_sq hk.le, hd', abs_div,
    abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos Real.pi_pos, abs_neg, abs_of_pos hd]
  rw [div_eq_mul_inv, mul_inv]
  ring

theorem crossTailDensity_momentum_error {a M m₂ k : ℝ} (hk : 0 < k)
    (hlarge : 2*|M^2-m₂| ≤ k^2) :
    |(2*k)*crossTailDensity a M m₂ (k^2+M^2) -
      (2*Real.exp (a*M)/Real.pi)*(|Real.sin (a*k)|/k)| ≤
        (2*(2*Real.exp (a*M)/Real.pi)*|M^2-m₂|)/k^3 := by
  let B := 2*Real.exp (a*M)/Real.pi
  let d := M^2-m₂
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hhalf : k^2/2 ≤ k^2+d := by linarith [neg_abs_le d]
  have hd : 0 < k^2+d := (by positivity : 0 < k^2/2).trans_le hhalf
  have hdiff : k/(k^2+d)-1/k = -d/(k*(k^2+d)) := by
    field_simp
    ring
  rw [crossTailDensity_momentum_formula hk hd]
  change |B*|Real.sin (a*k)| *(k/(k^2+d))-B*(|Real.sin (a*k)|/k)| ≤ _
  rw [show B*(|Real.sin (a*k)|/k) = B*|Real.sin (a*k)| *(1/k) by ring,
    ← mul_sub, hdiff, abs_mul, abs_of_nonneg (mul_nonneg hB (abs_nonneg _)),
    abs_div, abs_neg, abs_of_pos (mul_pos hk hd)]
  calc
    _ ≤ B*(|d|/(k*(k^2+d))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (a*k)) hB
    _ ≤ B*(|d|/(k*(k^2/2))) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
          (mul_le_mul_of_nonneg_left hhalf hk.le)) hB
    _ = _ := by
      change B*(|d|/(k*(k^2/2))) = (2*B*|d|)/k^3
      field_simp

theorem crossTailDensity_cutoff_substitution {K R : ℝ} (hK : 0 < K) (hKR : K ≤ R)
    (M : ℝ) (f : ℝ → ℝ) :
    (∫ s in Ioc (K^2+M^2) (R^2+M^2), f s) =
      ∫ k in K..R, (2*k)*f (k^2+M^2) := by
  have hder : ∀ k ∈ Ioc K R, HasDerivWithinAt (fun k : ℝ => k^2+M^2) (2*k)
      (Ioc K R) k := by
    intro k _
    simpa using (((hasDerivAt_id k).pow 2).add_const (M^2)).hasDerivWithinAt
  have hinj : InjOn (fun k : ℝ => k^2+M^2) (Ioc K R) := by
    apply StrictMonoOn.injOn
    intro r hr k hk h
    exact add_lt_add_right ((sq_lt_sq₀ (hK.trans hr.1).le (hK.trans hk.1).le).mpr h) _
  have himage : (fun k : ℝ => k^2+M^2) '' Ioc K R = Ioc (K^2+M^2) (R^2+M^2) := by
    have hR := hK.trans_le hKR
    ext s
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact ⟨add_lt_add_right ((sq_lt_sq₀ hK.le (hK.trans hk.1).le).2 hk.1) _,
        add_le_add_right ((sq_le_sq₀ (hK.trans hk.1).le hR.le).2 hk.2) _⟩
    · intro hs
      have hs₀ : 0 < s-M^2 := by linarith [hs.1, sq_nonneg K]
      have hsq := Real.sq_sqrt hs₀.le
      refine ⟨Real.sqrt (s-M^2), ⟨?_, ?_⟩, by linarith⟩
      · exact (sq_lt_sq₀ hK.le (Real.sqrt_nonneg _)).1 (by linarith [hs.1])
      · exact (sq_le_sq₀ (Real.sqrt_nonneg _) hR.le).1 (by linarith [hs.2])
  rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc hder hinj,
    intervalIntegral.integral_of_le hKR]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro k hk
  dsimp only
  rw [abs_of_pos (by linarith [hK.trans hk.1] : 0 < 2*k), smul_eq_mul]

/-- The deviation from the literal oscillatory (dk/k) density has a
uniformly bounded integral on every finite far-tail interval. -/
theorem crossTailDensity_cutoff_error_bound {a M m₂ K : ℝ} (hK : 0 < K)
    (hlarge : 2*|M^2-m₂| ≤ K^2) :
    ∃ C ≥ 0, ∀ R ≥ K,
      |(∫ s in Ioc (K^2+M^2) (R^2+M^2), crossTailDensity a M m₂ s) -
        (2*Real.exp (a*M)/Real.pi)*(∫ k in K..R, |Real.sin (a*k)|/k)| ≤ C := by
  let B := 2*Real.exp (a*M)/Real.pi
  let G (k : ℝ) := (2*B*|M^2-m₂|)*(k^(-3 : ℝ))
  have hG (k : ℝ) (hk : K < k) : 0 ≤ G k :=
    mul_nonneg (by dsimp [B]; positivity) (Real.rpow_nonneg (hK.trans hk).le _)
  have hIg : IntegrableOn G (Ioi K) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hK).const_mul _
  refine ⟨∫ k in Ioi K, G k, setIntegral_nonneg measurableSet_Ioi (fun k hk => hG k hk), ?_⟩
  intro R hKR
  rw [crossTailDensity_cutoff_substitution hK hKR, ← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_of_le hKR, intervalIntegral.integral_of_le hKR]
  let F (k : ℝ) := (2*k)*crossTailDensity a M m₂ (k^2+M^2)
  let H (k : ℝ) := B*(|Real.sin (a*k)|/k)
  change |(∫ k in Ioc K R, F k) - (∫ k in Ioc K R, H k)| ≤ _
  have hiH : IntegrableOn H (Ioc K R) := by
    apply IntegrableOn.mono_set (t := Icc K R) _ Ioc_subset_Icc_self
    apply ContinuousOn.integrableOn_Icc
    unfold H
    exact continuousOn_const.mul
      ((continuous_abs.comp (Real.continuous_sin.comp (continuous_const.mul continuous_id))).continuousOn.div
        continuousOn_id (fun k hk => (hK.trans_le hk.1).ne'))
  have hdom (k : ℝ) (hk : k ∈ Ioc K R) : ‖F k-H k‖ ≤ G k := by
    have hk₀ := hK.trans hk.1
    have hk' := hlarge.trans ((sq_le_sq₀ hK.le hk₀.le).2 hk.1.le)
    rw [Real.norm_eq_abs, show G k = (2*B*|M^2-m₂|)/k^3 by
      dsimp [G]
      rw [show (-3 : ℝ) = -(3:ℕ) by norm_num, Real.rpow_neg_natCast, zpow_neg, zpow_natCast,
        div_eq_mul_inv]]
    exact crossTailDensity_momentum_error hk₀ hk'
  have hiEH : IntegrableOn (fun k => F k-H k) (Ioc K R) := by
    apply (hIg.mono_set Ioc_subset_Ioi_self).mono'
    · exact ((measurable_id.const_mul _).mul ((crossTailDensity_measurable a M m₂).comp
        ((measurable_id.pow_const 2).add_const _))).sub
          (by unfold H; fun_prop : Measurable H) |>.aestronglyMeasurable
    · exact (ae_restrict_mem measurableSet_Ioc).mono hdom
  have hiF : IntegrableOn F (Ioc K R) := (hiEH.add hiH).congr (by
    filter_upwards with k
    exact sub_add_cancel _ _)
  rw [← integral_sub hiF hiH, ← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  exact (setIntegral_mono_on hiEH.norm (hIg.mono_set Ioc_subset_Ioi_self)
    measurableSet_Ioc hdom).trans
    (setIntegral_mono_set hIg ((ae_restrict_mem measurableSet_Ioi).mono hG)
      Ioc_subset_Ioi_self.eventuallyLE)

end UV.RevisionSpectrum
