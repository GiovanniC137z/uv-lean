import UV.ContinueNormalHolonomyGamma
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! The pathwise quartic rescaling of the radial Brownian-bridge expression.
The path is represented on unit time; this module uses each bounded
measurable sample and proves the deterministic clock and killing limits. -/

noncomputable section

open Real Set Filter MeasureTheory
open scoped Topology

namespace UV.ContinueNormalHolonomy

private theorem normalRpow_tendsto_zero {p : ℝ} (hp : 0 < p) :
    Tendsto (fun t : ℝ => t ^ p) (𝓝[>] 0) (𝓝 0) := by
  have hc := (Real.continuousAt_rpow_const 0 p (.inr hp.le)).tendsto
  rw [Real.zero_rpow hp.ne'] at hc
  exact hc.mono_left nhdsWithin_le_nhds

/-- Rescaled radial path in the layer (r=t^{1/8}x). -/
def quarticBridgeRescaled (t x : ℝ) (B : ℝ → ℝ) (u : ℝ) : ℝ :=
  x + t ^ (3 / 8 : ℝ) * B u

/-- The actual radius represented on unit-duration bridge time. -/
def quarticBridgeRadius (t x : ℝ) (B : ℝ → ℝ) (u : ℝ) : ℝ :=
  t ^ (1 / 8 : ℝ) * quarticBridgeRescaled t x B u

private theorem quarticBridge_uniform {x K : ℝ} (hx : 0 < x)
    (B : ℝ → ℝ) (hb : ∀ u ∈ Icc (0 : ℝ) 1, |B u| ≤ K) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ u ∈ Icc (0 : ℝ) 1,
      x / 2 ≤ quarticBridgeRescaled t x B u ∧
        quarticBridgeRescaled t x B u ≤ 3 * x / 2 := by
  have h := ((normalRpow_tendsto_zero (by norm_num : (0 : ℝ) < 3 / 8)).abs.mul_const K)
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, |t ^ (3 / 8 : ℝ)| * K < x / 2 := by
    simpa using h.eventually (Iio_mem_nhds (show |(0 : ℝ)| * K < x / 2 by simpa using half_pos hx))
  filter_upwards [he] with t ht u hu
  have hh : |t ^ (3 / 8 : ℝ) * B u| < x / 2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hb u hu) (abs_nonneg _)).trans_lt ht
  have hbounds := abs_lt.mp hh
  unfold quarticBridgeRescaled
  constructor <;> linarith [hbounds.1, hbounds.2]

/-- Each bounded bridge sample eventually survives both collar boundaries
on the (t^{1/8}) radial layer. -/
theorem quarticBridge_survives_eventually {x K : ℝ} (hx : 0 < x)
    (B : ℝ → ℝ) (hb : ∀ u ∈ Icc (0 : ℝ) 1, |B u| ≤ K) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ u ∈ Icc (0 : ℝ) 1, quarticBridgeRadius t x B u ∈ Ioo 0 1 := by
  have ht : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hh := (normalRpow_tendsto_zero (by norm_num : (0 : ℝ) < 1 / 8)).mul_const (3 * x / 2)
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, t ^ (1 / 8 : ℝ) * (3 * x / 2) < 1 := by
    simpa using hh.eventually (Iio_mem_nhds (show (0 : ℝ) * (3 * x / 2) < 1 by simp))
  filter_upwards [quarticBridge_uniform hx B hb, ht, he] with t ht ht0 ht1 u hu
  have h := ht u hu
  have hp : 0 < t ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos ht0 _
  exact ⟨mul_pos hp ((half_pos hx).trans_le h.1), (mul_le_mul_of_nonneg_left h.2 hp.le).trans_lt ht1⟩

/-- Inverse radial clock on the rescaled unit-duration path. -/
def quarticBridgeInverseClock (n : ℕ) (t x : ℝ) (B : ℝ → ℝ) : ℝ :=
  ∫ u in Icc (0 : ℝ) 1, ((quarticBridgeRescaled t x B u) ^ n)⁻¹

/-- The deterministic continuity estimate used for (I) and for the
(2/r^2) killing weight after Brownian scaling. -/
theorem quarticBridgeInverseClock_tendsto {x K : ℝ} (hx : 0 < x)
    (B : ℝ → ℝ) (hB : Measurable B) (hb : ∀ u ∈ Icc (0 : ℝ) 1, |B u| ≤ K) (n : ℕ) :
    Tendsto (fun t => quarticBridgeInverseClock n t x B) (𝓝[>] 0) (𝓝 ((x ^ n)⁻¹)) := by
  let μ := (volume : Measure ℝ).restrict (Icc 0 1)
  letI : IsFiniteMeasure μ := ⟨by simp [μ, Real.volume_Icc]⟩
  have hlim := tendsto_integral_filter_of_norm_le_const (μ := μ)
    (F := fun t u => ((quarticBridgeRescaled t x B u) ^ n)⁻¹)
    (f := fun _ => (x ^ n)⁻¹) (l := 𝓝[>] (0 : ℝ)) ?_ ?_ ?_
  · have he : (∫ _ : ℝ, (x ^ n)⁻¹ ∂μ) = (x ^ n)⁻¹ := by
      simp [μ, Real.volume_Icc, measureReal_def]
    rw [he] at hlim
    exact hlim
  · exact Filter.Eventually.of_forall fun t => by
      unfold quarticBridgeRescaled
      exact (((measurable_const.add (measurable_const.mul hB)).pow_const n).inv).aestronglyMeasurable
  · refine ⟨((x / 2) ^ n)⁻¹, ?_⟩
    filter_upwards [quarticBridge_uniform hx B hb] with t ht
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have h0 := (half_pos hx).trans_le (ht u hu).1
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg h0.le n))]
    exact (inv_le_inv₀ (pow_pos h0 n) (pow_pos (half_pos hx) n)).mpr
      (pow_le_pow_left₀ (half_pos hx).le (ht u hu).1 n)
  · exact ae_of_all _ fun u => by
      have he : Tendsto (fun t => quarticBridgeRescaled t x B u) (𝓝[>] 0) (𝓝 x) := by
        have hh := (tendsto_const_nhds (x := x)).add
          ((normalRpow_tendsto_zero (by norm_num : (0 : ℝ) < 3 / 8)).mul_const (B u))
        simpa [quarticBridgeRescaled] using hh
      exact (he.pow n).inv₀ (pow_ne_zero n hx.ne')

/-- The radial (2/r^2) path weight tends to one on the quartic layer. -/
theorem quarticBridgeKilling_tendsto {x K : ℝ} (hx : 0 < x)
    (B : ℝ → ℝ) (hB : Measurable B) (hb : ∀ u ∈ Icc (0 : ℝ) 1, |B u| ≤ K) :
    Tendsto (fun t : ℝ => Real.exp (-(2 * t ^ (3 / 4 : ℝ) *
        quarticBridgeInverseClock 2 t x B))) (𝓝[>] 0) (𝓝 1) := by
  have h := ((normalRpow_tendsto_zero (by norm_num : (0 : ℝ) < 3 / 4)).const_mul (2 : ℝ)).mul
    (quarticBridgeInverseClock_tendsto hx B hB hb 2)
  simpa only [mul_zero, zero_mul, neg_zero, Real.exp_zero] using Real.continuous_exp.continuousAt.tendsto.comp h.neg

/-- The relative angular trace and radial killing factor on a surviving path. -/
def quarticRelativeBridgeWeight (a t x : ℝ) (B : ℝ → ℝ) : ℝ := by
  classical
  exact if ∀ u ∈ Icc (0 : ℝ) 1, quarticBridgeRadius t x B u ∈ Ioo 0 1 then
    Real.exp (-(2 * t ^ (3 / 4 : ℝ) * quarticBridgeInverseClock 2 t x B)) *
      relativeNormalTheta (quarticBridgeInverseClock 8 t x B) a
  else 0

theorem quarticRelativeBridgeWeight_tendsto {x K : ℝ} (hx : 0 < x)
    (B : ℝ → ℝ) (hB : Measurable B) (hb : ∀ u ∈ Icc (0 : ℝ) 1, |B u| ≤ K) (a : ℝ) :
    Tendsto (fun t => quarticRelativeBridgeWeight a t x B) (𝓝[>] 0)
      (𝓝 (relativeNormalTheta (x ^ (8 : ℕ))⁻¹ a)) := by
  have hθ := (relativeNormalTheta_continuousAt (inv_pos.mpr (pow_pos hx 8)) a).tendsto.comp
    (quarticBridgeInverseClock_tendsto hx B hB hb 8)
  have h := (quarticBridgeKilling_tendsto hx B hB hb).mul hθ
  rw [one_mul] at h
  refine h.congr' ?_
  filter_upwards [quarticBridge_survives_eventually hx B hb] with t ht
  simp only [quarticRelativeBridgeWeight, if_pos ht, Function.comp_apply]

private theorem quarticBridgeClock_nonneg (k : ℕ) (t x : ℝ) (B : ℝ → ℝ) :
    0 ≤ quarticBridgeInverseClock (2 * k) t x B := by
  unfold quarticBridgeInverseClock
  apply integral_nonneg
  intro u
  change 0 ≤ ((quarticBridgeRescaled t x B u) ^ (2 * k))⁻¹
  rw [pow_mul]
  positivity

private theorem relativeNormalTheta_zero_width (a : ℝ) : relativeNormalTheta 0 a = 0 := by
  simp [relativeNormalTheta, normalTheta]

/-- Global bound on the relative angular factor along every radial path. -/
theorem quarticRelativeBridgeWeight_bounded {C : ℝ} (hC : 0 ≤ C)
    (hθ : ∀ (v a : ℝ), 0 < v → relativeNormalTheta v a ≤ C)
    (a : ℝ) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) (B : ℝ → ℝ) :
    0 ≤ quarticRelativeBridgeWeight a t x B ∧ quarticRelativeBridgeWeight a t x B ≤ C := by
  unfold quarticRelativeBridgeWeight
  split_ifs
  · let v := quarticBridgeInverseClock 8 t x B
    have hv : 0 ≤ v := quarticBridgeClock_nonneg 4 t x B
    rcases hv.eq_or_lt with h | h
    · change 0 ≤ _ * relativeNormalTheta v a ∧ _ * relativeNormalTheta v a ≤ C
      rw [← h, relativeNormalTheta_zero_width, mul_zero]
      exact ⟨le_rfl, hC⟩
    · have hk : 0 ≤ quarticBridgeInverseClock 2 t x B := by
        simpa using quarticBridgeClock_nonneg 1 t x B
      have he : Real.exp (-(2 * t ^ (3 / 4 : ℝ) * quarticBridgeInverseClock 2 t x B)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
      have hn := relativeNormalTheta_nonnegative h a
      exact ⟨mul_nonneg (Real.exp_pos _).le hn, (mul_le_of_le_one_left hn he).trans (hθ v a h)⟩
  · exact ⟨le_rfl, hC⟩

/-- On a confined path the quartic inverse clock yields the exponential
envelope in the rescaled starting radius. -/
theorem quarticRelativeBridgeWeight_confined {C : ℝ} (hC : 0 ≤ C)
    (hθ : ∀ (v a : ℝ), 0 < v → v ≤ 1 →
      relativeNormalTheta v a ≤ C * Real.exp (-(Real.pi ^ 2 / (4 * v))))
    (a : ℝ) {t : ℝ} (ht : 0 ≤ t) {x : ℝ} (hx : 2 ≤ x) (B : ℝ → ℝ)
    (hconf : ∀ u ∈ Icc (0 : ℝ) 1, x / 2 ≤ quarticBridgeRescaled t x B u) :
    quarticRelativeBridgeWeight a t x B ≤
      C * Real.exp (-(Real.pi ^ 2 * (x / 2) ^ (8 : ℕ) / 4)) := by
  unfold quarticRelativeBridgeWeight
  split_ifs
  · let v := quarticBridgeInverseClock 8 t x B
    have hv : 0 ≤ v := quarticBridgeClock_nonneg 4 t x B
    rcases hv.eq_or_lt with h | h
    · change _ * relativeNormalTheta v a ≤ _
      rw [← h, relativeNormalTheta_zero_width, mul_zero]
      positivity
    have hx' : 0 < x / 2 := by linarith
    have hvU : v ≤ ((x / 2) ^ (8 : ℕ))⁻¹ := by
      unfold v quarticBridgeInverseClock
      have h := integral_mono_of_nonneg (μ := (volume : Measure ℝ).restrict (Icc 0 1))
        (f := fun u => ((quarticBridgeRescaled t x B u) ^ (8 : ℕ))⁻¹)
        (g := fun _ => ((x / 2) ^ (8 : ℕ))⁻¹)
        (ae_of_all _ fun u => by positivity) (integrable_const _) ?_
      · simpa [measureReal_def, Real.volume_Icc] using h
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
        apply inv_anti₀ (pow_pos hx' _)
        exact pow_le_pow_left₀ hx'.le (hconf u hu) 8
    have hU1 : ((x / 2) ^ (8 : ℕ))⁻¹ ≤ 1 := by
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith) (n := 8))
    have hk : 0 ≤ quarticBridgeInverseClock 2 t x B := by
      simpa using quarticBridgeClock_nonneg 1 t x B
    have he : Real.exp (-(2 * t ^ (3 / 4 : ℝ) * quarticBridgeInverseClock 2 t x B)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    apply (mul_le_of_le_one_left (relativeNormalTheta_nonnegative h a) he).trans
    apply (hθ v a h (hvU.trans hU1)).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.exp_le_exp.mpr
    have hcost := inv_anti₀ h hvU
    rw [inv_inv] at hcost
    have he₀ : Real.pi ^ 2 / (4 * v) = (Real.pi ^ 2 / 4) * v⁻¹ := by
      rw [div_mul_eq_div_div]
      exact div_eq_mul_inv _ _
    rw [he₀, show Real.pi ^ 2 * (x / 2) ^ (8 : ℕ) / 4 =
      (Real.pi ^ 2 / 4) * (x / 2) ^ (8 : ℕ) by ring]
    exact neg_le_neg (mul_le_mul_of_nonneg_left hcost (by positivity))
  · positivity

end UV.ContinueNormalHolonomy
