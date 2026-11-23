import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.IntermediateValue

/-! The two radii that determine the sign of the Wilson heat-link soft integral. -/

noncomputable section

namespace UV.HeatMaxwell

open Set Filter Function
open scoped Topology

/-- The radial squared heat symbol at unit width. -/
def heatRadius (u : ℝ) : ℝ := u * Real.exp (-2 * u)

def heatPeak : ℝ := heatRadius (1 / 2)

def signPolynomial (u : ℝ) : ℝ := 2 * u ^ 3 - 7 * u ^ 2 + 2 * u + 2

theorem heatRadius_hasDerivAt (u : ℝ) :
    HasDerivAt heatRadius (Real.exp (-2 * u) * (1 - 2 * u)) u := by
  unfold heatRadius
  convert (hasDerivAt_id u).mul (((hasDerivAt_id u).const_mul (-2 : ℝ)).exp) using 1
  simp
  ring

theorem heatRadius_continuous : Continuous heatRadius := by
  unfold heatRadius
  fun_prop

theorem heatRadius_pos {u : ℝ} (hu : 0 < u) : 0 < heatRadius u :=
  mul_pos hu (Real.exp_pos _)

theorem heatPeak_pos : 0 < heatPeak := heatRadius_pos (by norm_num)

theorem heatPeak_eq : heatPeak = Real.exp (-1) / 2 := by
  unfold heatPeak heatRadius
  norm_num
  ring

theorem heatRadius_increasing : StrictMonoOn heatRadius (Icc 0 (1 / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) heatRadius_continuous.continuousOn
  intro u hu
  rw [interior_Icc] at hu
  rw [(heatRadius_hasDerivAt _).deriv]
  exact mul_pos (Real.exp_pos _) (by linarith [hu.2])

theorem heatRadius_decreasing : StrictAntiOn heatRadius (Ici (1 / 2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _) heatRadius_continuous.continuousOn
  intro u hu
  rw [interior_Ici] at hu
  rw [(heatRadius_hasDerivAt _).deriv]
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) (by linarith [show (1 : ℝ) / 2 < u from hu])

theorem heatRadius_tendsto_zero : Tendsto heatRadius atTop (𝓝 0) := by
  apply (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 2 (by norm_num)).congr'
  exact Eventually.of_forall fun u => by change u ^ (1 : ℝ) * Real.exp (-2 * u) = _; simp [heatRadius]

theorem heatRadius_lower_image :
    heatRadius '' Ioo 0 (1 / 2) = Ioo 0 heatPeak := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨heatRadius_pos hu.1, heatRadius_increasing
      ⟨hu.1.le, hu.2.le⟩ (right_mem_Icc.mpr (by norm_num)) hu.2⟩
  · intro hy
    have hImg := intermediate_value_Icc (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      heatRadius_continuous.continuousOn
    have hzero : heatRadius 0 = 0 := by simp [heatRadius]
    obtain ⟨u, hu, he⟩ := hImg (show y ∈ Icc (heatRadius 0) (heatRadius (1 / 2)) from
      ⟨hzero.trans_le hy.1.le, hy.2.le⟩)
    refine ⟨u, ⟨hu.1.lt_of_ne ?_, hu.2.lt_of_ne ?_⟩, he⟩
    · rintro rfl
      exact hy.1.ne' (he.symm.trans hzero)
    · rintro rfl
      exact hy.2.ne (he.symm : y = heatPeak)

theorem heatRadius_upper_image :
    heatRadius '' Ioi (1 / 2) = Ioo 0 heatPeak := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨heatRadius_pos ((by norm_num : (0 : ℝ) < 1 / 2).trans hu),
      heatRadius_decreasing (left_mem_Ici) (show (1 : ℝ) / 2 ≤ u from hu.le) hu⟩
  · intro hy
    obtain ⟨u, hu, hval⟩ := ((eventually_ge_atTop (1 : ℝ)).and
      (heatRadius_tendsto_zero.eventually_lt_const hy.1)).exists
    have hwide : (1 : ℝ) / 2 ≤ u := by linarith
    have hImg := intermediate_value_Icc' hwide
      (f := heatRadius) heatRadius_continuous.continuousOn
    obtain ⟨b, hb, he⟩ := hImg (show y ∈ Icc (heatRadius u) heatPeak from
      ⟨hval.le, hy.2.le⟩)
    refine ⟨b, hb.1.lt_of_ne ?_, he⟩
    rintro rfl
    exact hy.2.ne (he.symm : y = heatPeak)

def heatLowerRadius : ℝ → ℝ := invFunOn heatRadius (Ioo 0 (1 / 2))
def heatUpperRadius : ℝ → ℝ := invFunOn heatRadius (Ioi (1 / 2))

theorem heatLowerRadius_spec {y : ℝ} (hy : y ∈ Ioo 0 heatPeak) :
    heatLowerRadius y ∈ Ioo 0 (1 / 2) ∧ heatRadius (heatLowerRadius y) = y := by
  rw [← heatRadius_lower_image] at hy
  exact invFunOn_pos hy

theorem heatUpperRadius_spec {y : ℝ} (hy : y ∈ Ioo 0 heatPeak) :
    heatUpperRadius y ∈ Ioi (1 / 2) ∧ heatRadius (heatUpperRadius y) = y := by
  rw [← heatRadius_upper_image] at hy
  exact invFunOn_pos hy

theorem heatLowerRadius_heatRadius {u : ℝ} (hu : u ∈ Ioo 0 (1 / 2)) :
    heatLowerRadius (heatRadius u) = u :=
  (heatRadius_increasing.injOn.mono Ioo_subset_Icc_self).leftInvOn_invFunOn hu

theorem heatUpperRadius_heatRadius {u : ℝ} (hu : u ∈ Ioi (1 / 2)) :
    heatUpperRadius (heatRadius u) = u :=
  (heatRadius_decreasing.injOn.mono Ioi_subset_Ici_self).leftInvOn_invFunOn hu

private theorem lower_bound {l : ℝ} (hl : 0 < l) (hl' : l < 1 / 2) :
    2 + 6 * l < signPolynomial l / (1 - 2 * l) := by
  apply (lt_div_iff₀ (by linarith)).mpr
  unfold signPolynomial
  nlinarith [mul_pos (sq_pos_of_pos hl) (by positivity : 0 < 2 * l + 5)]

private theorem upper_bound_outside {b : ℝ} (hb : 1 / 2 < b)
    (h : b ≤ 3 / 2 ∨ 2 ≤ b) :
    -2 ≤ signPolynomial b / (2 * b - 1) := by
  apply (le_div_iff₀ (by linarith)).mpr
  have hb₀ : 0 ≤ b := by linarith
  have hf : 0 ≤ b * ((2 * b - 3) * (b - 2)) := by
    rcases h with hl | hr
    · exact mul_nonneg hb₀ (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith))
    · exact mul_nonneg hb₀ (mul_nonneg (by linarith) (by linarith))
  unfold signPolynomial
  nlinarith

private theorem upper_bound_inside {b : ℝ} (h₁ : 3 / 2 < b) (h₂ : b < 2) :
    -2 - 3 / 32 ≤ signPolynomial b / (2 * b - 1) := by
  have hd : 0 < 2 * b - 1 := by linarith
  have hb : b / (2 * b - 1) ≤ 3 / 4 := (div_le_iff₀ hd).mpr (by linarith)
  have hq : (2 * b - 3) * (2 - b) ≤ 1 / 8 := by nlinarith [sq_nonneg (b - 7 / 4)]
  have hm : b / (2 * b - 1) * ((2 * b - 3) * (2 - b)) ≤ 3 / 32 := by
    have hh := mul_le_mul hb hq (mul_nonneg (show 0 ≤ 2*b-3 by linarith) (sub_nonneg.mpr h₂.le)) (by norm_num)
    norm_num at hh ⊢
    exact hh
  have he : signPolynomial b / (2 * b - 1) =
      -2 - b / (2 * b - 1) * ((2 * b - 3) * (2 - b)) := by
    unfold signPolynomial
    field_simp
    ring
  linarith

private theorem heat_exp_margin : (3 : ℝ) / 32 < 12 * Real.exp (-4) := by
  rw [show (-4 : ℝ) = -(↑(4 : ℕ) * 1) by norm_num, Real.exp_neg, Real.exp_nat_mul,
    ← div_eq_mul_inv]
  apply (lt_div_iff₀ (by positivity)).mpr
  have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have h := pow_lt_pow_left₀ he (Real.exp_pos _).le (show (4 : ℕ) ≠ 0 by decide)
  norm_num at h ⊢
  linarith

/-- At equal positive squared heat symbol, the sum of the two signed
Jacobian factors is strictly positive. -/
theorem heatTwoBranchFactor_pos {l b : ℝ} (hl : 0 < l) (hl' : l < 1 / 2)
    (hb : 1 / 2 < b) (hy : heatRadius l = heatRadius b) :
    0 < signPolynomial l / (1 - 2 * l) + signPolynomial b / (2 * b - 1) := by
  have hL := lower_bound hl hl'
  by_cases h₁ : b ≤ 3 / 2
  · have hB := upper_bound_outside hb (Or.inl h₁)
    linarith
  by_cases h₂ : 2 ≤ b
  · have hB := upper_bound_outside hb (Or.inr h₂)
    linarith
  have hB := upper_bound_inside (lt_of_not_ge h₁) (lt_of_not_ge h₂)
  have hmono : heatRadius 2 ≤ heatRadius b :=
    heatRadius_decreasing.antitoneOn hb.le (by norm_num) (le_of_not_ge h₂)
  have htip : heatRadius l < l := by
    unfold heatRadius
    exact mul_lt_of_lt_one_right hl
      (Real.exp_lt_one_iff.mpr (by linarith))
  have he : heatRadius 2 = 2 * Real.exp (-4) := by norm_num [heatRadius]
  rw [he, ← hy] at hmono
  linarith [heat_exp_margin]

def heatBranchFactor (y : ℝ) : ℝ :=
  signPolynomial (heatLowerRadius y) / (1 - 2 * heatLowerRadius y) +
    signPolynomial (heatUpperRadius y) / (2 * heatUpperRadius y - 1)

theorem heatBranchFactor_pos {y : ℝ} (hy : y ∈ Ioo 0 heatPeak) :
    0 < heatBranchFactor y := by
  obtain ⟨hl, hly⟩ := heatLowerRadius_spec hy
  obtain ⟨hb, hby⟩ := heatUpperRadius_spec hy
  exact heatTwoBranchFactor_pos hl.1 hl.2 hb (hly.trans hby.symm)

end UV.HeatMaxwell
