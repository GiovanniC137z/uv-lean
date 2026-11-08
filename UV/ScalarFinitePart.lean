import UV.DepthAsymptotics
import UV.DepthMonotonicity
import UV.TwoLoopLines
import UV.ExponentialIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option maxHeartbeats 800000

noncomputable section
open MeasureTheory Set Real Filter Metric
open scoped Topology ENNReal BigOperators

namespace UV

/-- The source's reference zero-mass kernel is the literal exponential in the
positive radial variable. -/
theorem scalar_zero_mass_kernel (a : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    kernel a 0 (r ^ 2) = Real.exp (-a * r) := by
  simp [kernel, depthProfile, Real.sqrt_sq hr]

theorem scalar_zero_mass_kernel_square (a : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    kernel a 0 (r ^ 2) ^ 2 = Real.exp (-2 * a * r) := by
  rw [scalar_zero_mass_kernel a hr, pow_two, ← Real.exp_add]
  congr 1
  ring

/-- The exact radial rescaling s=2am of the actual unsubtracted bubble. -/
theorem scalarBubble_zero_mass_scaled (a : ℝ) {m : ℝ} (hm : 0 < m) :
    (8 * Real.pi ^ 2) * scalarBubble a 0 m 0 =
      ∫ x : ℝ in Ioi 0, x ^ 3 * Real.exp (-(2 * a * m) * x) / (1 + x ^ 2) ^ 2 := by
  rw [scalarBubble_zero_transfer_radial]
  have hp : 8 * Real.pi ^ 2 ≠ 0 := by positivity
  rw [← mul_assoc, mul_inv_cancel₀ hp, one_mul]
  calc
    _ = ∫ r : ℝ in Ioi 0, r ^ 3 * Real.exp (-2 * a * r) / (r ^ 2 + m ^ 2) ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [scalar_zero_mass_kernel_square a hr.le]
    _ = m * ∫ x : ℝ in Ioi 0,
        (m * x) ^ 3 * Real.exp (-2 * a * (m * x)) / ((m * x) ^ 2 + m ^ 2) ^ 2 := by
      rw [integral_comp_mul_left_Ioi
        (fun r : ℝ => r ^ 3 * Real.exp (-2 * a * r) / (r ^ 2 + m ^ 2) ^ 2) 0 hm,
        smul_eq_mul, mul_zero, ← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul]
    _ = _ := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      dsimp only
      rw [show -2 * a * (m * x) = -(2 * a * m) * x by ring]
      field_simp
      ring

/-- The mass-dependent kernel can only enlarge this zero-transfer bubble,
and its entire effect is bounded by the source exponential sandwich. -/
theorem scalarBubble_kernel_mass_sandwich {a M m : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M) (hm : 0 < m) :
    0 ≤ scalarBubble a M m 0 - scalarBubble a 0 m 0 ∧
      scalarBubble a M m 0 - scalarBubble a 0 m 0 ≤
        (Real.exp (2 * a * M) - 1) * scalarBubble a 0 m 0 := by
  have hlo := scalarBubble_monotone_mass ha (by norm_num : (0 : ℝ) ≤ 0) hM hm 0
  have hline (q : ScalarMomentum) :
      scalarCovariance a M m q ≤ Real.exp (a * M) * scalarCovariance a 0 m q := by
    have hk := kernel_upper (a := a) (M := M) (u := ‖q‖ ^ 2) ha.le (sq_nonneg _)
    have h0 : kernel a 0 (‖q‖ ^ 2) = Real.exp (-a * Real.sqrt (‖q‖ ^ 2)) := by
      simp [kernel, depthProfile]
    rw [← h0] at hk
    unfold scalarCovariance
    exact (div_le_div_of_nonneg_right hk (by positivity)).trans_eq (by ring)
  have hpoint (q : ScalarMomentum) : scalarBubbleIntegrand a M m 0 q ≤
      Real.exp (2 * a * M) * scalarBubbleIntegrand a 0 m 0 q := by
    unfold scalarBubbleIntegrand
    simp only [add_zero]
    have h := mul_le_mul (hline q) (hline q) (scalarCovariance_nonneg q)
      (mul_nonneg (Real.exp_nonneg _) (scalarCovariance_nonneg q))
    have he : Real.exp (2 * a * M) = Real.exp (a * M) * Real.exp (a * M) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    nlinarith
  have hup : scalarBubble a M m 0 ≤ Real.exp (2 * a * M) * scalarBubble a 0 m 0 := by
    unfold scalarBubble
    calc
      _ ≤ (2 * Real.pi) ^ (-4 : ℤ) *
          ∫ q, Real.exp (2 * a * M) * scalarBubbleIntegrand a 0 m 0 q := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact integral_mono (scalarBubbleIntegrand_integrable ha hM hm 0)
          ((scalarBubbleIntegrand_integrable ha (by norm_num) hm 0).const_mul _) hpoint
      _ = _ := by rw [integral_const_mul]; ring
  constructor <;> linarith

def finitePartI (s : ℝ) : ℝ := ∫ x : ℝ in Ioi 0, Real.exp (-s * x) * x / (1 + x ^ 2)
def finitePartK (s : ℝ) : ℝ := ∫ x : ℝ in Ioi 0, Real.exp (-s * x) * x / (1 + x ^ 2) ^ 2

theorem finitePartI_integrable {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun x : ℝ => Real.exp (-s * x) * x / (1 + x ^ 2)) (Ioi 0) := by
  have he := integrableOn_exp_mul_Ioi (a := -s) (by linarith) 0
  refine he.mono' ((((continuous_exp.comp (continuous_const.mul continuous_id)).mul continuous_id).div (by fun_prop) (fun x => by positivity) : Continuous (fun x : ℝ => Real.exp (-s * x) * x / (1 + x ^ 2))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : 0 < x := hx
  rw [Real.norm_of_nonneg (by positivity)]
  have hden : 0 < 1 + x ^ 2 := by positivity
  have hf : x / (1 + x ^ 2) ≤ 1 := (div_le_one hden).mpr (by nlinarith [sq_nonneg (x - 1 / 2)])
  have h := mul_le_mul_of_nonneg_left hf (Real.exp_nonneg (-s * x))
  simpa only [mul_div_assoc, mul_one] using h

theorem finitePartK_integrable {s : ℝ} (hs : 0 ≤ s) :
    IntegrableOn (fun x : ℝ => Real.exp (-s * x) * x / (1 + x ^ 2) ^ 2) (Ioi 0) := by
  refine (powerRadialBase_integrable 0).mono' ((((continuous_exp.comp (continuous_const.mul continuous_id)).mul continuous_id).div (by fun_prop) (fun x => by positivity) : Continuous (fun x : ℝ => Real.exp (-s * x) * x / (1 + x ^ 2) ^ 2)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : 0 < x := hx
  rw [Real.norm_of_nonneg (by positivity)]
  have he : Real.exp (-s * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h := mul_le_mul_of_nonneg_right he (div_nonneg hx.le (sq_nonneg (1 + x ^ 2)))
  simpa [powerRadialBase, mul_div_assoc] using h

theorem finitePartK_zero : finitePartK 0 = 1 / 2 := by
  unfold finitePartK
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul]
  simpa [powerRadialBase] using powerRadialBase_integral 0

/-- The actual Jacobian pullback under x↦1/x on the positive half-line. -/
def finitePartInv (f : ℝ → ℝ) (x : ℝ) : ℝ := (x ^ 2)⁻¹ * f x⁻¹

lemma finitePartInv_rpow (f : ℝ → ℝ) {x : ℝ} (hx : 0 < x) :
    (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • f (x ^ (-1 : ℝ)) =
      finitePartInv f x := by
  norm_num [finitePartInv, Real.rpow_neg hx.le, Real.rpow_two, Real.rpow_neg_one]

theorem finitePartInv_integral (f : ℝ → ℝ) :
    (∫ x : ℝ in Ioi 0, finitePartInv f x) = ∫ x : ℝ in Ioi 0, f x := by
  rw [← integral_comp_rpow_Ioi f (p := -1) (by norm_num)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  exact (finitePartInv_rpow f hx).symm

theorem finitePartInv_integrable {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) :
    IntegrableOn (finitePartInv f) (Ioi 0) := by
  have h := (integrableOn_Ioi_comp_rpow_iff f (p := -1) (by norm_num)).mpr hf
  exact h.congr_fun (fun x hx => finitePartInv_rpow f hx) measurableSet_Ioi

lemma finitePart_rat_integrable (j : ℕ) (hj : j ≤ 2) :
    IntegrableOn (fun x : ℝ => x ^ j / (1 + x ^ 2) ^ 2) (Ioi 0) := by
  have hc : Continuous (fun x : ℝ => x ^ j / (1 + x ^ 2) ^ 2) :=
    (continuous_pow j).div (by fun_prop) (fun x => by positivity)
  refine integrable_inv_one_add_sq.integrableOn.mono' hc.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := hx.le
  rw [Real.norm_of_nonneg (by positivity)]
  have hd : 0 < 1 + x ^ 2 := by positivity
  have hn : x ^ j ≤ 1 + x ^ 2 := by
    interval_cases j <;> norm_num at * <;> nlinarith [sq_nonneg (x - 1)]
  calc
    x ^ j / (1 + x ^ 2) ^ 2 ≤ (1 + x ^ 2) / (1 + x ^ 2) ^ 2 :=
      div_le_div_of_nonneg_right hn (sq_nonneg _)
    _ = _ := by field_simp

theorem finitePart_quadratic_moment :
    (∫ x : ℝ in Ioi 0, x ^ 2 / (1 + x ^ 2) ^ 2) = Real.pi / 4 := by
  have h0 := finitePart_rat_integrable 0 (by norm_num)
  have h2 := finitePart_rat_integrable 2 (by norm_num)
  have heq : (∫ x : ℝ in Ioi 0, x ^ 2 / (1 + x ^ 2) ^ 2) =
      ∫ x : ℝ in Ioi 0, (1 + x ^ 2) ^ (-2 : ℤ) := by
    rw [← finitePartInv_integral (fun x : ℝ => (1 + x ^ 2) ^ (-2 : ℤ))]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp [finitePartInv]
    rw [zpow_neg]
    have hxn : x ≠ 0 := ne_of_gt hx
    field_simp [hxn]
    ring
  have hsum : (∫ x : ℝ in Ioi 0, (1 + x ^ 2) ^ (-2 : ℤ)) +
      (∫ x : ℝ in Ioi 0, x ^ 2 / (1 + x ^ 2) ^ 2) = Real.pi / 2 := by
    rw [← integral_add (by simpa using h0) h2]
    calc
      _ = ∫ x : ℝ in Ioi 0, (1 + x ^ 2)⁻¹ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x _
        dsimp only
        rw [zpow_neg]
        have hd : 1 + x ^ 2 ≠ 0 := by positivity
        field_simp
      _ = _ := by rw [integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero]
  linarith

/-- Exponential damping changes an integrable kernel by at most its first
absolute moment times s. All integrals here are actual Lebesgue integrals. -/
theorem finitePart_exponential_perturbation {w : ℝ → ℝ}
    (hw : IntegrableOn w (Ioi 0))
    (hw1 : IntegrableOn (fun x => x * |w x|) (Ioi 0))
    {s : ℝ} (hs : 0 ≤ s) :
    |(∫ x : ℝ in Ioi 0, Real.exp (-s * x) * w x) - ∫ x : ℝ in Ioi 0, w x| ≤
      s * ∫ x : ℝ in Ioi 0, x * |w x| := by
  have he : IntegrableOn (fun x => Real.exp (-s * x) * w x) (Ioi 0) := by
    refine hw.bdd_mul' (c := 1) (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hs hx.le])
  have hsub : (∫ x : ℝ in Ioi 0, Real.exp (-s * x) * w x) - (∫ x : ℝ in Ioi 0, w x) =
      ∫ x : ℝ in Ioi 0, Real.exp (-s * x) * w x - w x := (integral_sub he hw).symm
  rw [hsub, ← integral_const_mul]
  change ‖∫ x : ℝ in Ioi 0, Real.exp (-s * x) * w x - w x‖ ≤ _
  apply norm_integral_le_of_norm_le (hw1.const_mul s)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have ht : 0 ≤ s * x := mul_nonneg hs hx.le
  have he1 : Real.exp (-s * x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have he2 := Real.add_one_le_exp (-s * x)
  rw [show Real.exp (-s * x) * w x - w x = (Real.exp (-s * x) - 1) * w x by ring,
    Real.norm_eq_abs, abs_mul, abs_of_nonpos (sub_nonpos.mpr he1)]
  calc
    -(Real.exp (-s * x) - 1) * |w x| ≤ (s * x) * |w x| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ = _ := by ring

theorem finitePartK_error {s : ℝ} (hs : 0 ≤ s) :
    |finitePartK s - 1 / 2| ≤ Real.pi * s / 4 := by
  have h := finitePart_exponential_perturbation
    (w := fun x : ℝ => x / (1 + x ^ 2) ^ 2)
    (by simpa [powerRadialBase] using powerRadialBase_integrable 0)
    (by
      apply (finitePart_rat_integrable 2 (by norm_num)).congr_fun _ measurableSet_Ioi
      intro x hx
      dsimp only
      rw [abs_of_nonneg (div_nonneg hx.le (sq_nonneg _))]
      ring) hs
  have hmoment : (∫ x : ℝ in Ioi 0, x * |x / (1 + x ^ 2) ^ 2|) = Real.pi / 4 := by
    rw [← finitePart_quadratic_moment]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [abs_of_nonneg (div_nonneg hx.le (sq_nonneg _))]
    ring
  have hzero : (∫ x : ℝ in Ioi 0, x / (1 + x ^ 2) ^ 2) = 1 / 2 := by
    simpa [powerRadialBase] using powerRadialBase_integral 0
  rw [hzero, hmoment] at h
  simpa only [finitePartK, mul_div_assoc, mul_assoc, mul_comm s, div_eq_mul_inv] using h

local notation "finitePartHead" => (Set.indicator (Ioo (0 : ℝ) 1))

lemma finitePartHead_integrable {f : ℝ → ℝ} (hf : Continuous f) :
    IntegrableOn (finitePartHead f) (Ioi 0) := by
  classical
  have hcc : IntegrableOn f (Icc (0 : ℝ) 1) volume := hf.integrableOn_Icc
  have h : IntegrableOn f (Ioo (0 : ℝ) 1) volume :=
    hcc.mono_set (fun _ hx => ⟨hx.1.le, hx.2.le⟩)
  exact (h.integrable_indicator measurableSet_Ioo).integrableOn

def finitePartCompensator (x : ℝ) : ℝ :=
  finitePartHead (fun y : ℝ => y / (1 + y ^ 2)) x -
    finitePartInv (finitePartHead (fun y : ℝ => y / (1 + y ^ 2))) x

lemma finitePart_head_continuous (j : ℕ) : Continuous (fun x : ℝ => x ^ j / (1 + x ^ 2)) :=
  (continuous_pow j).div (by fun_prop) (fun x => by positivity)

theorem finitePartCompensator_integrable : IntegrableOn finitePartCompensator (Ioi 0) := by
  have h : IntegrableOn (finitePartHead (fun y : ℝ => y / (1 + y ^ 2))) (Ioi 0) := by
    simpa only [pow_one] using finitePartHead_integrable (finitePart_head_continuous 1)
  exact h.sub (finitePartInv_integrable h)

theorem finitePartCompensator_integral :
    (∫ x : ℝ in Ioi 0, finitePartCompensator x) = 0 := by
  have h : IntegrableOn (finitePartHead (fun y : ℝ => y / (1 + y ^ 2))) (Ioi 0) := by
    simpa only [pow_one] using finitePartHead_integrable (finitePart_head_continuous 1)
  unfold finitePartCompensator
  rw [integral_sub h (finitePartInv_integrable h), finitePartInv_integral, sub_self]

lemma finitePartCompensator_abs_moment_point {x : ℝ} (hx : 0 < x) :
    x * |finitePartCompensator x| =
      finitePartHead (fun y : ℝ => y ^ 2 / (1 + y ^ 2)) x +
        finitePartInv (finitePartHead (fun y : ℝ => 1 / (1 + y ^ 2))) x := by
  rcases lt_trichotomy x 1 with h | h | h
  · have hm : x ∈ Ioo (0 : ℝ) 1 := ⟨hx, h⟩
    have hi : x⁻¹ ∉ Ioo (0 : ℝ) 1 := fun hh =>
      (not_lt.mpr ((one_le_inv₀ hx).mpr h.le)) hh.2
    simp only [finitePartCompensator, finitePartInv,
      indicator_of_mem hm, indicator_of_notMem hi, mul_zero, sub_zero, add_zero]
    rw [abs_of_nonneg (div_nonneg hx.le (by positivity))]
    ring
  · subst x
    norm_num [finitePartCompensator, finitePartInv]
  · have hm : x ∉ Ioo (0 : ℝ) 1 := fun hh => (not_lt.mpr h.le) hh.2
    have hi : x⁻¹ ∈ Ioo (0 : ℝ) 1 := ⟨inv_pos.mpr hx, (inv_lt_one₀ hx).mpr h⟩
    simp only [finitePartCompensator, finitePartInv,
      indicator_of_notMem hm, indicator_of_mem hi, zero_sub, zero_add, abs_neg]
    rw [abs_of_nonneg (by positivity : 0 ≤ (x ^ 2)⁻¹ * (x⁻¹ / (1 + x⁻¹ ^ 2)))]
    field_simp [hx.ne']

theorem finitePartCompensator_abs_moment_integrable :
    IntegrableOn (fun x => x * |finitePartCompensator x|) (Ioi 0) := by
  have h2 := finitePartHead_integrable (finitePart_head_continuous 2)
  have h0 : IntegrableOn (finitePartHead (fun y : ℝ => 1 / (1 + y ^ 2))) (Ioi 0) := by
    simpa only [pow_zero] using finitePartHead_integrable (finitePart_head_continuous 0)
  have hsum : IntegrableOn (fun x => finitePartHead (fun y : ℝ => y ^ 2 / (1 + y ^ 2)) x +
      finitePartInv (finitePartHead (fun y : ℝ => 1 / (1 + y ^ 2))) x) (Ioi 0) :=
    h2.add (finitePartInv_integrable h0)
  exact hsum.congr_fun
    (fun x hx => (finitePartCompensator_abs_moment_point hx).symm) measurableSet_Ioi

theorem finitePartCompensator_abs_moment :
    (∫ x : ℝ in Ioi 0, x * |finitePartCompensator x|) = 1 := by
  have h2 := finitePartHead_integrable (finitePart_head_continuous 2)
  have h0 : IntegrableOn (finitePartHead (fun y : ℝ => 1 / (1 + y ^ 2))) (Ioi 0) := by
    simpa only [pow_zero] using finitePartHead_integrable (finitePart_head_continuous 0)
  calc
    _ = ∫ x : ℝ in Ioi 0,
        finitePartHead (fun y : ℝ => y ^ 2 / (1 + y ^ 2)) x +
          finitePartInv (finitePartHead (fun y : ℝ => 1 / (1 + y ^ 2))) x := by
      exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => finitePartCompensator_abs_moment_point hx)
    _ = (∫ x : ℝ in Ioi 0, finitePartHead (fun y : ℝ => y ^ 2 / (1 + y ^ 2)) x) +
        (∫ x : ℝ in Ioi 0, finitePartHead (fun y : ℝ => 1 / (1 + y ^ 2)) x) := by
      rw [integral_add h2 (finitePartInv_integrable h0), finitePartInv_integral]
    _ = ∫ x : ℝ in Ioi 0, finitePartHead (fun _ : ℝ => (1 : ℝ)) x := by
      rw [← integral_add h2 h0]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      dsimp
      by_cases hx : x ∈ Ioo (0 : ℝ) 1
      · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx]
        field_simp
        ring
      · simp [hx]
    _ = 1 := by
      rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo]
      have hi : Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo 0 1 := inter_eq_left.mpr (fun _ h => h.1)
      rw [hi]
      simp

lemma finitePartCompensator_decomposition {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    x / (1 + x ^ 2) = (Ioi (1 : ℝ)).indicator (fun y : ℝ => 1 / y) x +
      finitePartCompensator x := by
  rcases lt_or_gt_of_ne hx1 with h | h
  · have hm : x ∈ Ioo (0 : ℝ) 1 := ⟨hx, h⟩
    have hi : x⁻¹ ∉ Ioo (0 : ℝ) 1 := fun hh =>
      (not_lt.mpr ((one_le_inv₀ hx).mpr h.le)) hh.2
    have ht : x ∉ Ioi (1 : ℝ) := not_lt.mpr h.le
    simp only [finitePartCompensator, finitePartInv,
      indicator_of_mem hm, indicator_of_notMem hi, indicator_of_notMem ht,
      mul_zero, sub_zero, zero_add]
  · have hm : x ∉ Ioo (0 : ℝ) 1 := fun hh => (not_lt.mpr h.le) hh.2
    have hi : x⁻¹ ∈ Ioo (0 : ℝ) 1 := ⟨inv_pos.mpr hx, (inv_lt_one₀ hx).mpr h⟩
    simp only [finitePartCompensator, finitePartInv,
      indicator_of_notMem hm, indicator_of_mem hi, indicator_of_mem (s := Ioi (1 : ℝ)) h, zero_sub]
    field_simp [hx.ne']
    ring

lemma finitePart_tail_integrable {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun x : ℝ => Real.exp (-s * x) / x) (Ioi 1) := by
  have h := (integrableOn_Ioi_comp_mul_left_iff
    (fun t : ℝ => Real.exp (-t) / t) 1 hs).mpr
      (by simpa only [mul_one] using exponentialIntegral_integrable hs)
  have hsc : IntegrableOn (fun x : ℝ => s * (Real.exp (-(s * x)) / (s * x))) (Ioi 1) := h.const_mul s
  apply hsc.congr_fun _ measurableSet_Ioi
  intro x _
  dsimp only
  rw [neg_mul]
  field_simp

lemma finitePart_tail_integral {s : ℝ} (hs : 0 < s) :
    (∫ x : ℝ in Ioi 1, Real.exp (-s * x) / x) = exponentialIntegral s := by
  calc
    _ = s * ∫ x : ℝ in Ioi 1, Real.exp (-(s * x)) / (s * x) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      dsimp only
      rw [neg_mul]
      field_simp
    _ = _ := by
      rw [integral_comp_mul_left_Ioi (fun t : ℝ => Real.exp (-t) / t) 1 hs,
        smul_eq_mul, mul_one, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
      rfl

/-- The rational kernel differs from the E1 tail by an integrable compensator
of integral zero and first absolute moment one. -/
theorem finitePartI_exponentialIntegral_error {s : ℝ} (hs : 0 < s) :
    |finitePartI s - exponentialIntegral s| ≤ s := by
  have hg := finitePartCompensator_integrable
  have hge : IntegrableOn (fun x => Real.exp (-s * x) * finitePartCompensator x) (Ioi 0) := by
    refine hg.bdd_mul' (c := 1) (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hs.le hx.le])
  have ht : IntegrableOn ((Ioi (1 : ℝ)).indicator (fun x : ℝ => Real.exp (-s * x) / x))
      (Ioi 0) := (finitePart_tail_integrable hs).integrable_indicator measurableSet_Ioi |>.integrableOn
  have hsplit : finitePartI s = exponentialIntegral s +
      ∫ x : ℝ in Ioi 0, Real.exp (-s * x) * finitePartCompensator x := by
    calc
      _ = ∫ x : ℝ in Ioi 0,
          (Ioi (1 : ℝ)).indicator (fun x : ℝ => Real.exp (-s * x) / x) x +
            Real.exp (-s * x) * finitePartCompensator x := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi,
          (countable_singleton (1 : ℝ)).ae_notMem (volume.restrict (Ioi 0))] with x hx hx1
        have h := finitePartCompensator_decomposition hx (by simpa only [mem_singleton_iff] using hx1)
        by_cases hxgt : 1 < x
        · rw [indicator_of_mem (s := Ioi (1 : ℝ)) hxgt] at h ⊢
          calc
            _ = Real.exp (-s * x) * (x / (1 + x ^ 2)) := by ring
            _ = _ := by rw [h]; ring
        · rw [indicator_of_notMem (s := Ioi (1 : ℝ)) hxgt] at h ⊢
          rw [zero_add] at h
          rw [← h]
          ring
      _ = _ := by
        rw [integral_add ht hge, integral_indicator measurableSet_Ioi,
          Measure.restrict_restrict measurableSet_Ioi]
        have hi : Ioi (1 : ℝ) ∩ Ioi 0 = Ioi 1 := inter_eq_left.mpr (fun x hx => show 0 < x from lt_trans zero_lt_one hx)
        rw [hi, finitePart_tail_integral hs]
  have h := finitePart_exponential_perturbation hg finitePartCompensator_abs_moment_integrable hs.le
  rw [finitePartCompensator_integral, sub_zero, finitePartCompensator_abs_moment, mul_one] at h
  rw [hsplit]
  simpa only [add_sub_cancel_left] using h

/-- Source finite-part I estimate with the actual Euler–Mascheroni constant. -/
theorem finitePartI_error {s : ℝ} (hs : 0 < s) :
    |finitePartI s + Real.eulerMascheroniConstant + Real.log s| ≤ 2 * s := by
  have h1 := finitePartI_exponentialIntegral_error hs
  have h2 := exponentialIntegral_error_bound hs
  calc
    _ = |(finitePartI s - exponentialIntegral s) +
        (exponentialIntegral s + Real.eulerMascheroniConstant + Real.log s)| := by congr 1; ring
    _ ≤ |finitePartI s - exponentialIntegral s| +
        |exponentialIntegral s + Real.eulerMascheroniConstant + Real.log s| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem scalarBubble_zero_mass_decomposition {a m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    (8 * Real.pi ^ 2) * scalarBubble a 0 m 0 = finitePartI (2 * a * m) - finitePartK (2 * a * m) := by
  rw [scalarBubble_zero_mass_scaled a hm]
  have hs : 0 < 2 * a * m := by positivity
  unfold finitePartI finitePartK
  rw [← integral_sub (finitePartI_integrable hs) (finitePartK_integrable hs.le)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  dsimp only
  have hd : 1 + x ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The finite part in the convention of the source, including Euler's
constant and the finite term -1/2. -/
def scalarFinitePartLeading (a m : ℝ) : ℝ :=
  (Real.log (1 / (2 * a * m)) - Real.eulerMascheroniConstant - 1 / 2) / (8 * Real.pi ^ 2)

/-- Exact quantitative zero-mass finite part of the actual zero-transfer
bubble; no asymptotic identity is assumed. -/
theorem scalarBubble_zero_mass_finite_part {a m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    |scalarBubble a 0 m 0 - scalarFinitePartLeading a m| ≤
      ((2 + Real.pi / 4) * (2 * a * m)) / (8 * Real.pi ^ 2) := by
  let s := 2 * a * m
  have hs : 0 < s := by dsimp [s]; positivity
  have hi := finitePartI_error hs
  have hk := finitePartK_error hs.le
  have hscaled : |(8 * Real.pi ^ 2) * scalarBubble a 0 m 0 -
      (Real.log (1 / s) - Real.eulerMascheroniConstant - 1 / 2)| ≤ (2 + Real.pi / 4) * s := by
    rw [scalarBubble_zero_mass_decomposition ha hm]
    change |finitePartI s - finitePartK s - _| ≤ _
    rw [one_div, Real.log_inv]
    calc
      _ = |(finitePartI s + Real.eulerMascheroniConstant + Real.log s) - (finitePartK s - 1 / 2)| := by
        congr 1
        ring
      _ ≤ |finitePartI s + Real.eulerMascheroniConstant + Real.log s| + |finitePartK s - 1 / 2| := abs_sub _ _
      _ ≤ _ := by linarith
  have hd : 0 < 8 * Real.pi ^ 2 := by positivity
  have heq : scalarBubble a 0 m 0 - scalarFinitePartLeading a m =
      ((8 * Real.pi ^ 2) * scalarBubble a 0 m 0 -
        (Real.log (1 / s) - Real.eulerMascheroniConstant - 1 / 2)) / (8 * Real.pi ^ 2) := by
    unfold scalarFinitePartLeading
    dsimp [s]
    field_simp
  rw [heq, abs_div, abs_of_pos hd]
  exact div_le_div_of_nonneg_right hscaled hd.le

/-- A parameter-independent logarithmic bound on a compact positive mass interval. -/
def scalarFinitePartLogBound (mlo mhi : ℝ) : ℝ :=
  |Real.log (2 * mlo)| + |Real.log (2 * mhi)| + |Real.eulerMascheroniConstant| + 1 / 2

theorem scalarFinitePartLeading_abs_le {a m mlo mhi : ℝ}
    (ha : 0 < a) (hmlo : 0 < mlo) (hm : m ∈ Icc mlo mhi) :
    |scalarFinitePartLeading a m| ≤
      (|Real.log a| + scalarFinitePartLogBound mlo mhi) / (8 * Real.pi ^ 2) := by
  have hmpos : 0 < m := hmlo.trans_le hm.1
  have hlo : Real.log (2 * mlo) ≤ Real.log (2 * m) :=
    Real.log_le_log (by positivity) (by linarith [hm.1])
  have hhi : Real.log (2 * m) ≤ Real.log (2 * mhi) :=
    Real.log_le_log (by positivity) (by linarith [hm.2])
  have hlog : |Real.log (2 * m)| ≤ |Real.log (2 * mlo)| + |Real.log (2 * mhi)| := by
    apply abs_le.mpr
    constructor <;> linarith [neg_abs_le (Real.log (2 * mlo)), le_abs_self (Real.log (2 * mhi)),
      abs_nonneg (Real.log (2 * mlo)), abs_nonneg (Real.log (2 * mhi))]
  have heq : Real.log (1 / (2 * a * m)) = -Real.log a - Real.log (2 * m) := by
    rw [one_div, Real.log_inv, show 2 * a * m = a * (2 * m) by ring,
      Real.log_mul ha.ne' (by positivity)]
    ring
  unfold scalarFinitePartLeading
  rw [abs_div, abs_of_pos (by positivity : 0 < 8 * Real.pi ^ 2), heq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h1 := abs_sub (-Real.log a - Real.log (2 * m)) Real.eulerMascheroniConstant
  have h2 := abs_sub (-Real.log a) (Real.log (2 * m))
  have h3 := abs_sub (-Real.log a - Real.log (2 * m) - Real.eulerMascheroniConstant) (1 / 2 : ℝ)
  simp only [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h1 h2 h3
  dsimp [scalarFinitePartLogBound]
  linarith

lemma scalarFinitePart_exp_sub_one (t : ℝ) : Real.exp t - 1 ≤ t * Real.exp t := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-t)) (Real.exp_nonneg t)
  have hid : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [hid] at h
  nlinarith

/-- An explicit uniform error bound tending to zero, with no logarithmic
asymptotic taken as a premise. -/
def scalarFinitePartUniformError (a Mmax mlo mhi : ℝ) : ℝ :=
  ((2 + Real.pi / 4) * (2 * mhi) / (8 * Real.pi ^ 2)) * a +
    (2 * Mmax * Real.exp (2 * a * Mmax)) *
      ((a * |Real.log a| + a * scalarFinitePartLogBound mlo mhi) / (8 * Real.pi ^ 2) +
        ((2 + Real.pi / 4) * (2 * mhi) / (8 * Real.pi ^ 2)) * a ^ 2)

theorem scalarBubble_finite_part_uniform_bound {a M m Mmax mlo mhi : ℝ}
    (ha : 0 < a) (hM : M ∈ Icc (0 : ℝ) Mmax) (hmlo : 0 < mlo) (hm : m ∈ Icc mlo mhi) :
    |scalarBubble a M m 0 - scalarFinitePartLeading a m| ≤
      scalarFinitePartUniformError a Mmax mlo mhi := by
  have hmpos : 0 < m := hmlo.trans_le hm.1
  have hmax : 0 ≤ Mmax := hM.1.trans hM.2
  have hhi : 0 < mhi := hmpos.trans_le hm.2
  let D := 8 * Real.pi ^ 2
  let C := (2 + Real.pi / 4) * (2 * mhi) / D
  let L := (|Real.log a| + scalarFinitePartLogBound mlo mhi) / D
  have hd : 0 < D := by dsimp [D]; positivity
  have hc : 0 ≤ C := by dsimp [C]; positivity
  have hl : 0 ≤ L := by dsimp [L, scalarFinitePartLogBound]; positivity
  have hzero : |scalarBubble a 0 m 0 - scalarFinitePartLeading a m| ≤ C * a := by
    have h := scalarBubble_zero_mass_finite_part ha hmpos
    apply h.trans
    dsimp [C, D]
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hm.2
      (by positivity : 0 ≤ (2 + Real.pi / 4) * (2 * a))
    nlinarith
  have hleading : |scalarFinitePartLeading a m| ≤ L := scalarFinitePartLeading_abs_le ha hmlo hm
  have hb : scalarBubble a 0 m 0 ≤ L + C * a := by
    have hsub := le_abs_self (scalarBubble a 0 m 0 - scalarFinitePartLeading a m)
    have hlead := le_abs_self (scalarFinitePartLeading a m)
    linarith
  have hmass := scalarBubble_kernel_mass_sandwich ha hM.1 hmpos
  have hem : Real.exp (2 * a * M) - 1 ≤ Real.exp (2 * a * Mmax) - 1 := by
    have := Real.exp_le_exp.mpr (show 2 * a * M ≤ 2 * a * Mmax by nlinarith [hM.2])
    linarith
  have he0 : 0 ≤ Real.exp (2 * a * Mmax) - 1 := by
    apply sub_nonneg.mpr
    exact Real.one_le_exp_iff.mpr (by positivity)
  have hmass2 : scalarBubble a M m 0 - scalarBubble a 0 m 0 ≤
      (2 * a * Mmax * Real.exp (2 * a * Mmax)) * (L + C * a) := by
    calc
      _ ≤ (Real.exp (2 * a * Mmax) - 1) * scalarBubble a 0 m 0 :=
        hmass.2.trans (mul_le_mul_of_nonneg_right hem (scalarBubble_nonneg a 0 m 0))
      _ ≤ (Real.exp (2 * a * Mmax) - 1) * (L + C * a) := mul_le_mul_of_nonneg_left hb he0
      _ ≤ _ := mul_le_mul_of_nonneg_right (scalarFinitePart_exp_sub_one _) (by positivity)
  calc
    _ = |(scalarBubble a M m 0 - scalarBubble a 0 m 0) +
        (scalarBubble a 0 m 0 - scalarFinitePartLeading a m)| := by congr 1; ring
    _ ≤ |scalarBubble a M m 0 - scalarBubble a 0 m 0| +
        |scalarBubble a 0 m 0 - scalarFinitePartLeading a m| := abs_add_le _ _
    _ ≤ (2 * a * Mmax * Real.exp (2 * a * Mmax)) * (L + C * a) + C * a := by
      rw [abs_of_nonneg hmass.1]
      exact add_le_add hmass2 hzero
    _ = _ := by
      dsimp [scalarFinitePartUniformError, C, L, D]
      ring

theorem scalarFinitePartUniformError_tendsto (Mmax mlo mhi : ℝ) :
    Tendsto (fun a : ℝ => scalarFinitePartUniformError a Mmax mlo mhi) (𝓝[>] 0) (𝓝 0) := by
  have ha : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) := (tendsto_id : Tendsto (fun a : ℝ => a) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds
  have hlog : Tendsto (fun a : ℝ => |Real.log a * a|) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one, abs_zero] using (tendsto_log_mul_rpow_nhdsGT_zero (r := 1) zero_lt_one).abs
  have halog : Tendsto (fun a : ℝ => a * |Real.log a|) (𝓝[>] 0) (𝓝 0) := by
    apply hlog.congr'
    filter_upwards [eventually_mem_nhdsWithin] with a ha
    rw [abs_mul]
    rw [abs_of_pos (show 0 < a from ha)]
    ring
  have he := (Real.continuous_exp.tendsto (2 * (0 : ℝ) * Mmax)).comp ((ha.const_mul 2).mul_const Mmax)
  simp only [mul_zero, zero_mul, Real.exp_zero] at he
  let C := (2 + Real.pi / 4) * (2 * mhi) / (8 * Real.pi ^ 2)
  have h1 := ha.const_mul C
  have h2 := (halog.add (ha.mul_const (scalarFinitePartLogBound mlo mhi))).div_const (8 * Real.pi ^ 2)
  have h3 := (ha.pow 2).const_mul C
  have h := h1.add ((he.const_mul (2 * Mmax)).mul (h2.add h3))
  simpa only [scalarFinitePartUniformError, C, mul_zero, zero_mul, zero_div, zero_add,
    add_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h

/-- The source finite part is uniform in auxiliary masses on bounded intervals
and propagator masses on compact positive intervals. -/
theorem scalarBubble_finite_part_uniform {Mmax mlo mhi : ℝ}
    (hmlo : 0 < mlo) :
    TendstoUniformlyOn
      (fun a (p : ℝ × ℝ) => scalarBubble a p.1 p.2 0 - scalarFinitePartLeading a p.2)
      (fun _ => (0 : ℝ)) (𝓝[>] 0) ((Icc (0 : ℝ) Mmax) ×ˢ (Icc mlo mhi)) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have he := (scalarFinitePartUniformError_tendsto Mmax mlo mhi).eventually (gt_mem_nhds hε)
  filter_upwards [he, eventually_mem_nhdsWithin] with a he ha
  intro p hp
  rw [Real.dist_eq, zero_sub, abs_neg]
  exact (scalarBubble_finite_part_uniform_bound ha hp.1 hmlo hp.2).trans_lt he

/-- All three quantitative and uniform conclusions of the named source
finite-part proposition, for the actual scalar bubble. -/
theorem oqed_zero_depth_finite_part {a M m Mmax mlo mhi : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M) (hm : 0 < m) (hmlo : 0 < mlo) :
    |scalarBubble a 0 m 0 - scalarFinitePartLeading a m| ≤
      ((2 + Real.pi / 4) * (2 * a * m)) / (8 * Real.pi ^ 2) ∧
    (0 ≤ scalarBubble a M m 0 - scalarBubble a 0 m 0 ∧
      scalarBubble a M m 0 - scalarBubble a 0 m 0 ≤
        (Real.exp (2 * a * M) - 1) * scalarBubble a 0 m 0) ∧
    TendstoUniformlyOn
      (fun a (p : ℝ × ℝ) => scalarBubble a p.1 p.2 0 - scalarFinitePartLeading a p.2)
      (fun _ => (0 : ℝ)) (𝓝[>] 0) ((Icc (0 : ℝ) Mmax) ×ˢ (Icc mlo mhi)) :=
  ⟨scalarBubble_zero_mass_finite_part ha hm, scalarBubble_kernel_mass_sandwich ha hM hm,
    scalarBubble_finite_part_uniform hmlo⟩

end UV
