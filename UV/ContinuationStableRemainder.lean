import UV.ContinuationStablePolar
import UV.RevisionLegacyCosine
import Mathlib.Analysis.Calculus.Taylor

/-! Quantitative annulus and far-tail bounds for the leading stable-half logarithm. -/

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal

namespace UV

private def sixthCosRemainder (t : ℝ) : ℝ := stableCosRemainder t + t ^ 6 / 720

private theorem sixthCosRemainder_bound (t : ℝ) : |sixthCosRemainder t| ≤ |t| ^ 8 / 5040 := by
  by_cases ht : t = 0
  · simp [ht, sixthCosRemainder, stableCosRemainder]
  have hp : 0 < |t| := abs_pos.mpr ht
  have h0 : (0 : ℝ) ∈ Icc 0 |t| := ⟨le_rfl, hp.le⟩
  have h : ‖cos |t| - taylorWithinEval cos 7 (Icc 0 |t|) 0 |t|‖ ≤
      (1 : ℝ) * (|t| - 0)^8 / (5040 : ℝ) :=
    taylor_mean_remainder_bound (n := 7) hp.le Real.contDiff_cos.contDiffOn
      ⟨hp.le, le_rfl⟩ (fun y hy => by
        rw [Real.iteratedDerivWithin_cos_Icc 8 hp hy, Real.norm_eq_abs]
        exact Real.abs_iteratedDeriv_cos_le_one 8 y)
  have hEval : taylorWithinEval cos 7 (Icc 0 |t|) 0 |t| =
      1 - |t| ^ 2 / 2 + |t| ^ 4 / 24 - |t| ^ 6 / 720 := by
    rw [taylor_within_apply]
    simp_rw [Real.iteratedDerivWithin_cos_Icc _ hp h0]
    rw [show (7 : ℕ) + 1 = 8 by decide]
    norm_num [Finset.sum_range_succ, show iteratedDeriv 2 cos = -cos by simp,
      show iteratedDeriv 3 cos = sin by simpa using Real.iteratedDeriv_odd_cos 1,
      show iteratedDeriv 4 cos = cos by simp,
      show iteratedDeriv 5 cos = -sin by ext y; simp,
      show iteratedDeriv 6 cos = -cos by ext y; simp,
      show iteratedDeriv 7 cos = sin by ext y; simp]
    ring
  have h4 : |t| ^ 4 = t ^ 4 := by
    calc |t| ^ 4 = (|t| ^ 2) ^ 2 := by ring
      _ = t ^ 4 := by rw [sq_abs]; ring
  have h6 : |t| ^ 6 = t ^ 6 := by
    calc |t| ^ 6 = (|t| ^ 2) ^ 3 := by ring
      _ = t ^ 6 := by rw [sq_abs]; ring
  rw [hEval, Real.norm_eq_abs, Real.cos_abs, sq_abs, h4, h6] at h
  convert h using 2
  · unfold sixthCosRemainder stableCosRemainder
    ring
  · ring

private theorem stableCosRemainder_outer_bound (t s : ℝ) (hs : 1 ≤ s) (ht : |t| ≤ s) :
    |stableCosRemainder t| ≤ 3 * s ^ 4 := by
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  have hs2 : s^2 ≤ s^4 := by
    rw [show (4 : ℕ) = 2 + 2 by decide, pow_add]
    exact le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ hs)
  have ht2 : t^2 ≤ s^4 := (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ht 2 : t^2 ≤ s^2).trans hs2
  have ht4 : t^4 ≤ s^4 := by
    calc t^4 = (|t|^2)^2 := by rw [sq_abs]; ring
      _ ≤ (s^2)^2 := pow_le_pow_left₀ (sq_nonneg _) (pow_le_pow_left₀ (abs_nonneg _) ht 2) 2
      _ = _ := by ring
  have h1 : 1 ≤ s^4 := one_le_pow₀ hs
  unfold stableCosRemainder
  calc
    _ ≤ |cos t - 1 + t^2/2| + |t^4/24| := abs_sub _ _
    _ ≤ |cos t - 1| + |t^2/2| + |t^4/24| := by linarith [abs_add_le (cos t - 1) (t^2/2)]
    _ ≤ (|cos t| + |(1 : ℝ)|) + |t^2/2| + |t^4/24| :=
      add_le_add_right (add_le_add_right (abs_sub _ _) _) _
    _ ≤ _ := by
      have ht2n : 0 ≤ t^2/2 := by positivity
      have ht4n : 0 ≤ t^4/24 := by positivity
      rw [abs_one, abs_of_nonneg ht2n, abs_of_nonneg ht4n]
      linarith [abs_cos_le_one t]

private def inversePowerCut (s : Set ℝ) (q : ℕ) (x : ScalarMomentum) : ℝ :=
  s.indicator (fun r => (r ^ q)⁻¹) ‖x‖

private theorem inversePowerCut_integrable {s : Set ℝ} (hs : MeasurableSet s)
    (q : ℕ) (hi : IntegrableOn (fun r : ℝ => r ^ 3 * (r ^ q)⁻¹) s) :
    Integrable (inversePowerCut s q) := by
  unfold inversePowerCut
  apply (integrable_fun_norm_addHaar (E := ScalarMomentum) volume).mpr
  have h := ((integrable_indicator_iff hs).mpr hi).integrableOn (s := Ioi (0 : ℝ))
  apply h.congr_fun _ measurableSet_Ioi
  intro r _
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
  by_cases hr : r ∈ s <;> simp [Set.indicator, hr]

private theorem inversePowerCut_integral {s : Set ℝ} (hs : MeasurableSet s)
    (hs0 : s ⊆ Ioi 0) (q : ℕ) :
    (∫ x, inversePowerCut s q x) = 2 * π ^ 2 * ∫ r in s, r ^ 3 * (r ^ q)⁻¹ := by
  unfold inversePowerCut
  rw [integral_fun_norm_addHaar (E := ScalarMomentum) volume
    (s.indicator (fun r => (r ^ q)⁻¹))]
  have he : (∫ r : ℝ in Ioi 0,
      r ^ (Module.finrank ℝ ScalarMomentum - 1) • s.indicator (fun r => (r ^ q)⁻¹) r) =
      ∫ r in s, r ^ 3 * (r ^ q)⁻¹ := by
    calc
      _ = ∫ r : ℝ in Ioi 0, s.indicator (fun r => r ^ 3 * (r ^ q)⁻¹) r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r _
        simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
        by_cases hr : r ∈ s <;> simp [Set.indicator, hr]
      _ = _ := by
        rw [integral_indicator hs, Measure.restrict_restrict hs, Set.inter_eq_left.mpr hs0]
  rw [he]
  have hball : volume.real (ball (0 : ScalarMomentum) 1) = π ^ 2 / 2 := by
    rw [measureReal_def, EuclideanSpace.volume_ball]
    norm_num [Real.Gamma_nat_eq_factorial, Real.sq_sqrt Real.pi_nonneg]
    rw [ENNReal.toReal_ofReal (by positivity)]
    congr 1
    nlinarith [Real.sq_sqrt Real.pi_nonneg]
  simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul, hball]
  ring

private theorem inversePowerCut_annulus {R L : ℝ} (hR : 0 < R) (q : ℕ) :
    Integrable (inversePowerCut (Ioc R L) q) := by
  apply inversePowerCut_integrable measurableSet_Ioc
  apply IntegrableOn.mono_set _ Ioc_subset_Icc_self
  exact (continuousOn_id.pow 3 |>.mul
    ((continuousOn_id.pow q).inv₀ (fun r hr => pow_ne_zero _ (hR.trans_le hr.1).ne')) :
    ContinuousOn (fun r : ℝ => r ^ 3 * (r ^ q)⁻¹) (Icc R L))
    |>.integrableOn_compact isCompact_Icc

private theorem inversePowerCut_annulus_two {R L : ℝ} (hR : 0 < R) (hRL : R ≤ L) :
    (∫ x, inversePowerCut (Ioc R L) 2 x) = π ^ 2 * (L ^ 2 - R ^ 2) := by
  rw [inversePowerCut_integral measurableSet_Ioc (fun _ hr => hR.trans hr.1)]
  have he : (∫ r : ℝ in Ioc R L, r ^ 3 * (r ^ (2 : ℕ))⁻¹) = ∫ r : ℝ in Ioc R L, r := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    have hrp : 0 < r := hR.trans hr.1
    field_simp
  rw [he, ← intervalIntegral.integral_of_le hRL]
  have h := integral_pow (a := R) (b := L) 1
  simp only [pow_one, Nat.reduceAdd] at h
  rw [h]
  ring

private theorem inversePowerCut_outer_six {L : ℝ} (hL : 0 < L) :
    Integrable (inversePowerCut (Ioi L) 6) ∧
    (∫ x, inversePowerCut (Ioi L) 6 x) = π ^ 2 / L ^ 2 := by
  have he (r : ℝ) (hr : r ∈ Ioi L) : r ^ 3 * (r ^ (6 : ℕ))⁻¹ = r ^ (-3 : ℝ) := by
    have hrp : 0 < r := hL.trans hr
    rw [Real.rpow_neg hrp.le, show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
    field_simp
  refine ⟨inversePowerCut_integrable measurableSet_Ioi 6
    ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hL).congr_fun
      (fun r hr => (he r hr).symm) measurableSet_Ioi), ?_⟩
  rw [inversePowerCut_integral measurableSet_Ioi (Ioi_subset_Ioi hL.le)]
  rw [setIntegral_congr_fun measurableSet_Ioi he,
    integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hL]
  norm_num [Real.rpow_neg hL.le, Real.rpow_two]
  ring

private theorem inversePowerCut_nonneg (s : Set ℝ) (q : ℕ) (x : ScalarMomentum) : 0 ≤ inversePowerCut s q x := by
  unfold inversePowerCut
  by_cases h : ‖x‖ ∈ s <;> simp [h, inv_nonneg, pow_nonneg]

/-- Absolute tail integral and quantitative error for the exact sixth
logarithm after subtracting the fourth-order cosine polynomial. -/
theorem stable_square_tail_cosine_log {R h : ℝ} (hR : 0 < R) (hh : 0 < |h|)
    (hRh : R ≤ |h|⁻¹) :
    let J := fun x : ScalarMomentum => stableCosRemainder (h * x 0) * inversePowerCut (Ioi R) 10 x
    Integrable J ∧
    |(∫ x, J x) + (h ^ 6 / 720) * (5 * π ^ 2 / 32) * log (|h|⁻¹ / R)| ≤
      (4 * π ^ 2) * |h| ^ 6 := by
  intro J
  let L := |h|⁻¹
  have hL : 0 < L := inv_pos.mpr hh
  let D := fun x : ScalarMomentum => (x 0)^6 * inversePowerCut (Ioc R L) 10 x
  let E₁ := fun x : ScalarMomentum => sixthCosRemainder (h*x 0) * inversePowerCut (Ioc R L) 10 x
  let E₂ := fun x : ScalarMomentum => stableCosRemainder (h*x 0) * inversePowerCut (Ioi L) 10 x
  have hInvMeas {s : Set ℝ} (hs : MeasurableSet s) (n : ℕ) : Measurable (inversePowerCut s n) :=
    (((measurable_id.pow_const n).inv).indicator hs).comp continuous_norm.measurable
  let co := PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0
  have hA : Continuous stableCosRemainder := by unfold stableCosRemainder; fun_prop
  have hB : Continuous sixthCosRemainder := by unfold sixthCosRemainder; exact hA.add ((continuous_id.pow 6).div_const 720)
  have hE₁ : Measurable E₁ := ((hB.comp (continuous_const.mul co)).measurable).mul
    (hInvMeas measurableSet_Ioc 10)
  have hE₂ : Measurable E₂ := ((hA.comp (continuous_const.mul co)).measurable).mul
    (hInvMeas measurableSet_Ioi 10)
  have hDmeas : Measurable D := (co.pow 6).measurable.mul (hInvMeas measurableSet_Ioc 10)
  have hb1 (x : ScalarMomentum) :
      ‖E₁ x‖ ≤ (|h|^8/5040) * inversePowerCut (Ioc R L) 2 x := by
    have hx : |x 0| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
    by_cases hel : ‖x‖ ∈ Ioc R L
    · have hrp : 0 < ‖x‖ := hR.trans hel.1
      dsimp [E₁, inversePowerCut]
      rw [Set.indicator_of_mem hel, Set.indicator_of_mem hel, abs_mul,
        abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hrp.le _))]
      have h8 : |h * x 0| ^ 8 / 5040 ≤ (|h| * ‖x‖) ^ 8 / 5040 := by
        rw [abs_mul]
        gcongr
      apply (mul_le_mul_of_nonneg_right ((sixthCosRemainder_bound _).trans h8)
        (inv_nonneg.mpr (pow_nonneg hrp.le _))).trans_eq
      rw [mul_pow]
      field_simp
    · simp [E₁, inversePowerCut, hel]
  have hb2 (x : ScalarMomentum) :
      ‖E₂ x‖ ≤ (3*|h|^4) * inversePowerCut (Ioi L) 6 x := by
    have hx : |x 0| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
    by_cases hel : ‖x‖ ∈ Ioi L
    · have hr : L < ‖x‖ := hel
      have hrp : 0 < ‖x‖ := hL.trans hr
      have h1 : 1 ≤ |h| * ‖x‖ := by
        have hk := mul_le_mul_of_nonneg_left hr.le hh.le
        dsimp [L] at hk
        rwa [mul_inv_cancel₀ hh.ne'] at hk
      have hhx : |h*x 0| ≤ |h| * ‖x‖ := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
      dsimp [E₂, inversePowerCut]
      rw [Set.indicator_of_mem hel, Set.indicator_of_mem hel, abs_mul,
        abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hrp.le _))]
      apply (mul_le_mul_of_nonneg_right (stableCosRemainder_outer_bound _ _ h1 hhx)
        (inv_nonneg.mpr (pow_nonneg hrp.le _))).trans_eq
      rw [mul_pow]
      field_simp
    · simp [E₂, inversePowerCut, hel]
  have hbD (x : ScalarMomentum) : ‖D x‖ ≤ inversePowerCut (Ioc R L) 4 x := by
    have hx : |x 0| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
    by_cases hel : ‖x‖ ∈ Ioc R L
    · have hrp : 0 < ‖x‖ := hR.trans hel.1
      dsimp [D, inversePowerCut]
      rw [Set.indicator_of_mem hel, Set.indicator_of_mem hel, abs_mul, abs_pow,
        abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hrp.le _))]
      apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hx 6)
        (inv_nonneg.mpr (pow_nonneg hrp.le _))).trans_eq
      field_simp
    · simp [D, inversePowerCut, hel]
  have hI₁ := (inversePowerCut_annulus (L := L) hR 2).const_mul (|h|^8/5040)
  have hI₂ := (inversePowerCut_outer_six hL).1.const_mul (3*|h|^4)
  have h1 : Integrable E₁ := hI₁.mono' hE₁.aestronglyMeasurable (Filter.Eventually.of_forall hb1)
  have h2 : Integrable E₂ := hI₂.mono' hE₂.aestronglyMeasurable (Filter.Eventually.of_forall hb2)
  have hdi : Integrable D := (inversePowerCut_annulus (L := L) hR 4).mono'
    hDmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbD)
  have heq : J = fun x => E₁ x + E₂ x - (h^6 / 720) * D x := by
    funext x
    by_cases hr : R < ‖x‖
    · by_cases hl : L < ‖x‖
      · simp [J, E₁, E₂, D, inversePowerCut, hr, hl, not_le.mpr hl]
      · simp only [J, E₁, E₂, D, inversePowerCut,
          Set.indicator_of_mem (show ‖x‖ ∈ Ioi R from hr),
          Set.indicator_of_mem (show ‖x‖ ∈ Ioc R L from ⟨hr, le_of_not_gt hl⟩),
          Set.indicator_of_notMem (show ‖x‖ ∉ Ioi L from hl), mul_zero, add_zero,
          sixthCosRemainder]
        ring
    · simp [J, E₁, E₂, D, inversePowerCut, hr,
        show ¬ L < ‖x‖ from fun hlt => hr (hRh.trans_lt hlt)]
  have hdlog : (∫ x, D x) = (5 * π ^ 2 / 32) * log (L / R) := by
    rw [← stable_annular_sixth_log hR hRh]
    apply integral_congr_ae
    filter_upwards with x
    change D x = (Ioc R L).indicator (fun r => (x 0) ^ 6 / r ^ 10) ‖x‖
    by_cases hLx : ‖x‖ ∈ Ioc R L <;> simp [D, inversePowerCut, hLx, div_eq_mul_inv]
  refine ⟨by rw [heq]; exact (h1.add h2).sub (hdi.const_mul _), ?_⟩
  have heval : (∫ x, J x) =
      (∫ x, E₁ x) + (∫ x, E₂ x) - (h^6/720) * ((5*π^2/32) * log (L / R)) := by
    have hx := integral_sub (h1.add h2) (hdi.const_mul (h^6/720))
    rw [show (∫ x, (E₁ + E₂) x) = (∫ x, E₁ x) + ∫ x, E₂ x from integral_add h1 h2,
      integral_const_mul, hdlog] at hx
    rw [heq]
    exact hx
  rw [heval]
  have he : (∫ x, E₁ x) + (∫ x, E₂ x) -
      (h ^ 6 / 720) * (5 * π ^ 2 / 32 * log (L / R)) +
      h ^ 6 / 720 * (5 * π ^ 2 / 32) * log (|h|⁻¹ / R) =
      (∫ x, E₁ x) + (∫ x, E₂ x) := by dsimp [L]; ring
  rw [he]
  have hc1 : |∫ x, E₁ x| ≤ (π^2/5040) * |h|^6 := calc
    _ ≤ ∫ x, ‖E₁ x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (|h|^8/5040) * inversePowerCut (Ioc R L) 2 x := integral_mono h1.norm hI₁ hb1
    _ = (|h|^8/5040) * (π^2 * (L^2 - R^2)) := by
      rw [integral_const_mul, inversePowerCut_annulus_two hR hRh]
    _ ≤ (|h|^8/5040) * (π^2 * L^2) := by gcongr; linarith [sq_nonneg R]
    _ = _ := by dsimp [L]; field_simp
  have hc2 : |∫ x, E₂ x| ≤ 3 * π^2 * |h|^6 := calc
    _ ≤ ∫ x, ‖E₂ x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (3*|h|^4) * inversePowerCut (Ioi L) 6 x := integral_mono h2.norm hI₂ hb2
    _ = _ := by rw [integral_const_mul, (inversePowerCut_outer_six hL).2]; dsimp [L]; field_simp
  have hcoef : π^2/5040 + 3*π^2 ≤ 4*π^2 := by nlinarith [sq_nonneg π]
  exact (abs_add_le _ _).trans ((add_le_add hc1 hc2).trans (by
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg _) _)))


private theorem stableCosRemainder_sixth_bound (t : ℝ) : |stableCosRemainder t| ≤ 3 * |t| ^ 6 := by
  by_cases ht : 1 ≤ |t|
  · refine (stableCosRemainder_outer_bound _ _ ht le_rfl).trans ?_
    have h : |t|^4 ≤ |t|^6 := pow_le_pow_right₀ ht (by decide)
    linarith
  · have ht' : |t| ≤ 1 := le_of_not_ge ht
    have hpow : |t|^8 ≤ |t|^6 := pow_le_pow_of_le_one (abs_nonneg _) ht' (by decide)
    have hterm : |t^6/720| = |t|^6 / 720 := by
      rw [abs_div, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 720)]
    calc
      _ = |sixthCosRemainder t - t^6/720| := by unfold sixthCosRemainder; rw [add_sub_cancel_right]
      _ ≤ |sixthCosRemainder t| + |t^6/720| := abs_sub _ _
      _ ≤ |t|^8/5040 + |t|^6/720 := by rw [hterm]; exact add_le_add_right (sixthCosRemainder_bound t) _
      _ ≤ _ := by linarith [pow_nonneg (abs_nonneg t) 6]

/-- Integral of the literal covariance square with its first three even
cosine terms removed. The numerical logarithmic coefficient incorporates the
coordinate tail, exact unit-sphere moment, and sixth cosine Taylor term. -/
theorem stable_covariance_cosine_leading_log {a m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, 0 < |h| → |h| ≤ m →
      |(∫ x : ScalarMomentum, stableCosRemainder (h*x 0) * stableCoordinateCovariance a m x ^ 2) +
        (a ^ 2 / (8192 * π ^ 2 * m ^ 4)) * h ^ 6 * log (m / |h|)| ≤ K * |h| ^ 6 := by
  let C := stableCoordinateCovariance a m
  let c := 3 * a / (4 * π ^ 2 * m ^ 2)
  let S := fun x : ScalarMomentum => C x ^ 2 - stableCovarianceTailSquare a m x
  let kRes := (∫ x : ScalarMomentum, ‖x‖^6 * |S x|) / 120
  have hkRes : 0 ≤ kRes := div_nonneg (integral_nonneg fun _ => by positivity) (by norm_num)
  refine ⟨kRes + c^2 * (4*π^2), by positivity, fun h hh hhm => ?_⟩
  have hr : m⁻¹ ≤ |h|⁻¹ := inv_anti₀ hh hhm
  let J := fun x : ScalarMomentum => stableCosRemainder (h*x 0) * inversePowerCut (Ioi m⁻¹) 10 x
  have hJ := stable_square_tail_cosine_log (inv_pos.mpr hm) hh hr
  change Integrable J ∧
    |(∫ x, J x) + (h^6/720) * (5*π^2/32) * log (|h|⁻¹ / m⁻¹)| ≤ (4*π^2) * |h|^6 at hJ
  have hlog : log (|h|⁻¹ / m⁻¹) = log (m / |h|) := by
    congr 1
    field_simp
  rw [hlog] at hJ
  let E := fun x : ScalarMomentum => stableCosRemainder (h*x 0) * S x
  have hEb : |∫ x, E x| ≤ kRes * |h|^6 := by
    have hv := revised_stable_residual_cosine_error ha hm h
    convert hv using 1
    dsimp [kRes]
    ring
  have hS : Measurable S := by
    apply ((stableCoordinateCovariance_continuous ha hm).measurable.pow_const 2).sub _
    unfold stableCovarianceTailSquare
    exact Measurable.piecewise (s := {x : ScalarMomentum | m⁻¹ < ‖x‖})
      (measurableSet_lt measurable_const continuous_norm.measurable) (by fun_prop) measurable_const
  have hmom : Integrable (fun x : ScalarMomentum => ‖x‖^6 * |S x|) := by
    apply (revised_stable_square_tail_residual_sixth_moment ha hm).abs.congr
    filter_upwards with x
    rw [abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg x) _)]
  have hE : Integrable E := by
    apply (hmom.const_mul (3 * |h|^6)).mono'
    · exact ((show Continuous (fun x : ScalarMomentum => stableCosRemainder (h*x 0)) by
        unfold stableCosRemainder
        have hcoe := PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0
        fun_prop).measurable.mul hS).aestronglyMeasurable
    · filter_upwards with x
      have hx : |x 0| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
      change |stableCosRemainder (h*x 0) * S x| ≤ 3 * |h|^6 * (‖x‖^6 * |S x|)
      rw [abs_mul]
      refine (mul_le_mul_of_nonneg_right (stableCosRemainder_sixth_bound _) (abs_nonneg _)).trans ?_
      rw [abs_mul, mul_pow]
      calc
        _ ≤ 3 * (|h|^6 * ‖x‖^6) * |S x| := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hx 6) (by positivity))
            (by norm_num)) (abs_nonneg _)
        _ = _ := by ring
  have hsplit : (fun x : ScalarMomentum => stableCosRemainder (h*x 0) * C x ^ 2) =
      fun x => E x + c ^ 2 * J x := by
    funext x
    by_cases hx : ‖x‖ ∈ Ioi m⁻¹
    · have hx' : m⁻¹ < ‖x‖ := hx
      simp only [E, S, J, inversePowerCut, stableCovarianceTailSquare, if_pos hx',
        Set.indicator_of_mem hx, div_eq_mul_inv]
      ring
    · have hx' : ¬ m⁻¹ < ‖x‖ := hx
      simp [E, S, J, stableCovarianceTailSquare, inversePowerCut, hx, hx']
  rw [hsplit, integral_add hE (hJ.1.const_mul _), integral_const_mul]
  have hc : c^2 * ((h^6/720) * (5*π^2/32) * log (m/|h|)) =
      (a ^ 2 / (8192 * π ^ 2 * m ^ 4)) * h ^ 6 * log (m / |h|) := by
    dsimp [c]
    field_simp
    ring
  rw [← hc]
  rw [show (∫ x, E x) + c^2 * (∫ x, J x) +
        c^2 * (h^6/720 * (5*π^2/32) * log (m/|h|)) =
      (∫ x, E x) + c^2 * ((∫ x, J x) + h^6/720 * (5*π^2/32) * log (m/|h|)) by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg (sq_nonneg c)]
  exact (add_le_add hEb (mul_le_mul_of_nonneg_left hJ.2 (sq_nonneg c))).trans_eq (by ring)

end UV
