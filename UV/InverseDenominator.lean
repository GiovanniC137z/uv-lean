import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic

/-! Sharp first derivative and global second derivative estimates for the real
massive inverse denominator in the two-loop certificate. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology RealInnerProductSpace InnerProductSpace

namespace UV

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def inverseDenominator (u : E) : ℝ := (1 + ‖u‖ ^ 2)⁻¹

def inverseDenominatorGradient (u : E) : E := (-2 / (1 + ‖u‖ ^ 2) ^ 2 : ℝ) • u

def inverseDenominatorHessian (u : E) : E →L[ℝ] E :=
  (-2 / (1 + ‖u‖ ^ 2) ^ 2 : ℝ) • ContinuousLinearMap.id ℝ E +
    (8 / (1 + ‖u‖ ^ 2) ^ 3 : ℝ) • (innerSL ℝ u).smulRight u

def inverseDenominatorGradientBound : ℝ := 9 / (8 * Real.sqrt 3)

theorem inverseDenominatorGradientBound_pos : 0 < inverseDenominatorGradientBound := by
  unfold inverseDenominatorGradientBound
  positivity

theorem inverseDenominator_hasFDerivAt (u : E) :
    HasFDerivAt inverseDenominator (innerSL ℝ (inverseDenominatorGradient u)) u := by
  have hn := (hasStrictFDerivAt_norm_sq u).hasFDerivAt.const_add 1
  have hi := ((hasDerivAt_id (1 + ‖u‖ ^ 2)).inv
    (by change 1 + ‖u‖ ^ 2 ≠ 0; positivity)).comp_hasFDerivAt u hn
  convert hi using 1
  ext h
  simp [inverseDenominatorGradient]
  ring

theorem inverseDenominatorGradient_hasFDerivAt (u : E) :
    HasFDerivAt inverseDenominatorGradient (inverseDenominatorHessian u) u := by
  have hreal : HasDerivAt (fun t : ℝ => -2 / (1 + t) ^ 2)
      (4 / (1 + ‖u‖ ^ 2) ^ 3) (‖u‖ ^ 2) := by
    have ht := ((((hasDerivAt_id (‖u‖ ^ 2)).const_add 1).pow 2).inv
      (by change (1 + ‖u‖ ^ 2) ^ 2 ≠ 0; positivity)).const_mul (-2)
    convert ht using 1
    simp only [id_eq, Pi.pow_apply]
    field_simp
    ring
  have hc : HasFDerivAt (fun v : E => -2 / (1 + ‖v‖ ^ 2) ^ 2)
      ((8 / (1 + ‖u‖ ^ 2) ^ 3 : ℝ) • innerSL ℝ u) u := by
    convert hreal.comp_hasFDerivAt u (hasStrictFDerivAt_norm_sq u).hasFDerivAt using 1
    ext h
    simp
    ring
  convert hc.fun_smul (hasFDerivAt_id u) using 1
  ext h
  simp [inverseDenominatorHessian]
  module

theorem inverseDenominatorGradient_norm (u : E) :
    ‖inverseDenominatorGradient u‖ = 2 * ‖u‖ / (1 + ‖u‖ ^ 2) ^ 2 := by
  have hd : 0 < 1 + ‖u‖ ^ 2 := by positivity
  unfold inverseDenominatorGradient
  rw [norm_smul]
  simp [Real.norm_eq_abs, abs_of_pos hd]
  ring

theorem inverseDenominatorGradient_sharp_scalar {r : ℝ} (hr : 0 ≤ r) :
    2 * r / (1 + r ^ 2) ^ 2 ≤ inverseDenominatorGradientBound := by
  let s := Real.sqrt 3 * r
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs2 : s ^ 2 = 3 * r ^ 2 := by
    dsimp [s]
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  have hs4 : s ^ 4 = 9 * r ^ 4 := by
    calc
      _ = (s ^ 2) ^ 2 := by ring
      _ = (3 * r ^ 2) ^ 2 := by rw [hs2]
      _ = _ := by ring
  have hp : 0 ≤ (s - 1) ^ 2 * (s ^ 2 + 2 * s + 9) := by positivity
  have hpoly : 0 ≤ s ^ 4 + 6 * s ^ 2 - 16 * s + 9 := by nlinarith [hp]
  rw [hs4, hs2] at hpoly
  dsimp [s] at hpoly
  unfold inverseDenominatorGradientBound
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [hpoly]

theorem inverseDenominatorGradient_norm_le (u : E) :
    ‖inverseDenominatorGradient u‖ ≤ inverseDenominatorGradientBound := by
  rw [inverseDenominatorGradient_norm]
  exact inverseDenominatorGradient_sharp_scalar (norm_nonneg u)

theorem inverseDenominatorHessian_apply (u h : E) :
    inverseDenominatorHessian u h = (-2 / (1 + ‖u‖ ^ 2) ^ 2 : ℝ) • h +
      (8 * ⟪u, h⟫_ℝ / (1 + ‖u‖ ^ 2) ^ 3 : ℝ) • u := by
  simp [inverseDenominatorHessian, smul_smul]
  module

/-- The rank-one cancellation gives the sharp uniform Hessian operator bound. -/
theorem inverseDenominatorHessian_norm_apply_le (u h : E) :
    ‖inverseDenominatorHessian u h‖ ≤ 2 * ‖h‖ := by
  let t := ‖u‖ ^ 2
  let s := ⟪u, h⟫_ℝ
  let q := ‖h‖ ^ 2
  have ht : 0 ≤ t := sq_nonneg _
  have hq : 0 ≤ q := sq_nonneg _
  have hD : 0 < 1 + t := by positivity
  have hD3 : 0 < (1 + t) ^ 3 := by positivity
  have hc : s ^ 2 ≤ t * q := by
    simpa only [s, t, q, ← pow_two, real_inner_self_eq_norm_sq] using real_inner_mul_inner_self_le u h
  let N : E := (-2 * (1 + t) : ℝ) • h + (8 * s : ℝ) • u
  have he : inverseDenominatorHessian u h = ((1 + t) ^ 3)⁻¹ • N := by
    rw [inverseDenominatorHessian_apply]
    have hA : (-2 / (1 + t) ^ 2 : ℝ) = ((1 + t) ^ 3)⁻¹ * (-2 * (1 + t)) := by
      field_simp
    have hB : (8 * s / (1 + t) ^ 3 : ℝ) = ((1 + t) ^ 3)⁻¹ * (8 * s) := by ring
    change (-2 / (1 + t) ^ 2 : ℝ) • h + (8 * s / (1 + t) ^ 3 : ℝ) • u = _
    rw [hA, hB]
    simp only [N, smul_add, smul_smul]
  have hNsq : ‖N‖ ^ 2 = 4 * (1 + t) ^ 2 * q + 32 * (t - 1) * s ^ 2 := by
    dsimp only [N]
    rw [norm_add_sq_real]
    simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_smul_left,
      inner_smul_right]
    dsimp [t, s, q]
    rw [real_inner_comm h u]
    ring
  have hsq : ‖N‖ ^ 2 ≤ (2 * (1 + t) ^ 3 * ‖h‖) ^ 2 := by
    rw [hNsq]
    have hright : (2 * (1 + t) ^ 3 * ‖h‖) ^ 2 = 4 * (1 + t) ^ 6 * q := by dsimp [q]; ring
    rw [hright]
    by_cases ht1 : t ≤ 1
    · have hn : 32 * (t - 1) * s ^ 2 ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg s)
      have hp : (1 + t) ^ 2 ≤ (1 + t) ^ 6 := pow_le_pow_right₀ (by linarith) (by decide)
      nlinarith [mul_le_mul_of_nonneg_right hp hq]
    · have h1 : 1 ≤ t := le_of_lt (lt_of_not_ge ht1)
      have hp : (3 * t - 1) ^ 2 ≤ (1 + t) ^ 6 := by
        have hp' : 3 * t - 1 ≤ (1 + t) ^ 3 := by nlinarith [pow_nonneg ht 3, sq_nonneg t]
        have hh := pow_le_pow_left₀ (by linarith : 0 ≤ 3 * t - 1) hp' 2
        simpa only [← pow_mul] using hh
      have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 32 * (t - 1) by linarith)
      have hn := mul_le_mul_of_nonneg_right hp hq
      nlinarith [hm, hn]
  have hN : ‖N‖ ≤ 2 * (1 + t) ^ 3 * ‖h‖ := by
    have hn0 := norm_nonneg N
    have hr0 : 0 ≤ 2 * (1 + t) ^ 3 * ‖h‖ := by positivity
    nlinarith
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hD3)]
  calc
    _ ≤ ((1 + t) ^ 3)⁻¹ * (2 * (1 + t) ^ 3 * ‖h‖) :=
      mul_le_mul_of_nonneg_left hN (inv_pos.mpr hD3).le
    _ = _ := by field_simp

theorem inverseDenominatorHessian_norm_le (u : E) : ‖inverseDenominatorHessian u‖ ≤ 2 :=
  (inverseDenominatorHessian u).opNorm_le_bound (by norm_num)
    (inverseDenominatorHessian_norm_apply_le u)

theorem inverseDenominator_hasGradientAt [CompleteSpace E] (u : E) :
    HasGradientAt inverseDenominator (inverseDenominatorGradient u) u := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have he : InnerProductSpace.toDual ℝ E (inverseDenominatorGradient u) =
      innerSL ℝ (inverseDenominatorGradient u) := by
    ext h
    simp only [InnerProductSpace.toDual_apply, innerSL_apply]
  rw [he]
  exact inverseDenominator_hasFDerivAt u

theorem inverseDenominator_fderiv_norm_le (u : E) :
    ‖fderiv ℝ inverseDenominator u‖ ≤ inverseDenominatorGradientBound := by
  rw [(inverseDenominator_hasFDerivAt u).fderiv, innerSL_apply_norm]
  exact inverseDenominatorGradient_norm_le u

theorem inverseDenominator_sub_abs_le (u v : E) :
    |inverseDenominator u - inverseDenominator v| ≤ inverseDenominatorGradientBound * ‖u - v‖ := by
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (s := (univ : Set E))
    (f := inverseDenominator) (x := v) (y := u)
    (fun x _ => (inverseDenominator_hasFDerivAt x).differentiableAt)
    (fun x _ => inverseDenominator_fderiv_norm_le x) convex_univ (mem_univ _) (mem_univ _)
  simpa only [Real.norm_eq_abs] using h

theorem inverseDenominatorGradient_sub_norm_le (u v : E) :
    ‖inverseDenominatorGradient u - inverseDenominatorGradient v‖ ≤ 2 * ‖u - v‖ := by
  apply Convex.norm_image_sub_le_of_norm_fderiv_le (s := (univ : Set E)) (x := v) (y := u)
    (fun x _ => (inverseDenominatorGradient_hasFDerivAt x).differentiableAt)
    (fun x _ => ?_) convex_univ (mem_univ _) (mem_univ _)
  rw [(inverseDenominatorGradient_hasFDerivAt _).fderiv]
  exact inverseDenominatorHessian_norm_le _

theorem inverseDenominatorGradient_lipschitzWith : LipschitzWith 2 (inverseDenominatorGradient : E → E) :=
  LipschitzWith.of_dist_le_mul (fun u v => by
    simpa only [dist_eq_norm, NNReal.coe_ofNat] using inverseDenominatorGradient_sub_norm_le u v)

/-- The factor one in the quadratic remainder comes from Cauchy's mean-value
theorem applied to the remainder and `t²`, using the proved Lipschitz gradient. -/
theorem inverseDenominator_taylor_error (u h : E) :
    |inverseDenominator (u + h) - inverseDenominator u - ⟪inverseDenominatorGradient u, h⟫_ℝ| ≤
      ‖h‖ ^ 2 := by
  let R : ℝ → ℝ := fun t => inverseDenominator (u + t • h) - inverseDenominator u -
    t * ⟪inverseDenominatorGradient u, h⟫_ℝ
  let R' : ℝ → ℝ := fun t => ⟪inverseDenominatorGradient (u + t • h) - inverseDenominatorGradient u, h⟫_ℝ
  have hd : ∀ t, HasDerivAt R (R' t) t := by
    intro t
    have hcurve : HasDerivAt (fun s : ℝ => u + s • h) h t := by
      simpa only [one_smul] using ((hasDerivAt_id t).smul_const h).const_add u
    have hg := ((inverseDenominator_hasFDerivAt (u + t • h)).comp_hasDerivAt t hcurve).sub_const
      (inverseDenominator u)
    convert hg.sub ((hasDerivAt_id t).mul_const ⟪inverseDenominatorGradient u, h⟫_ℝ) using 1
    simp only [R', innerSL_apply, inner_sub_left, one_mul]
  have hb : ∀ t ∈ Ioo (0 : ℝ) 1, |R' t| ≤ 2 * t * ‖h‖ ^ 2 := by
    intro t ht
    calc
      _ ≤ ‖inverseDenominatorGradient (u + t • h) - inverseDenominatorGradient u‖ * ‖h‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (2 * ‖(u + t • h) - u‖) * ‖h‖ :=
        mul_le_mul_of_nonneg_right (inverseDenominatorGradient_sub_norm_le _ _) (norm_nonneg _)
      _ = _ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
        ring
  obtain ⟨c, hc, heq⟩ := exists_ratio_hasDerivAt_eq_ratio_slope R R' (by norm_num : (0 : ℝ) < 1)
    (fun t _ => (hd t).continuousAt.continuousWithinAt) (fun t _ => hd t)
    (fun t : ℝ => t ^ 2) (fun t : ℝ => 2 * t) (by fun_prop)
    (fun t _ => by simpa using (hasDerivAt_id t).pow 2)
  have heq' : R' c =
      (inverseDenominator (u + h) - inverseDenominator u - ⟪inverseDenominatorGradient u, h⟫_ℝ) * (2 * c) := by
    simpa [R] using heq
  have hc0 : 0 < 2 * c := by linarith [hc.1]
  apply (mul_le_mul_iff_left₀ hc0).mp
  calc
    _ = |R' c| := by rw [heq', abs_mul, abs_of_pos hc0]
    _ ≤ 2 * c * ‖h‖ ^ 2 := hb c hc
    _ = _ := by ring

theorem inverseDenominator_lipschitz (u v : E) :
    |inverseDenominator u - inverseDenominator v| ≤ inverseDenominatorGradientBound * ‖u - v‖ :=
  inverseDenominator_sub_abs_le u v

theorem inverseDenominatorGradient_lipschitz (u v : E) :
    ‖inverseDenominatorGradient u - inverseDenominatorGradient v‖ ≤ 2 * ‖u - v‖ :=
  inverseDenominatorGradient_sub_norm_le u v

@[fun_prop] theorem inverseDenominator_continuous : Continuous (inverseDenominator : E → ℝ) :=
  continuous_iff_continuousAt.mpr (fun u => (inverseDenominator_hasFDerivAt u).continuousAt)

@[fun_prop] theorem inverseDenominatorGradient_continuous : Continuous (inverseDenominatorGradient : E → E) :=
  continuous_iff_continuousAt.mpr (fun u => (inverseDenominatorGradient_hasFDerivAt u).continuousAt)

@[fun_prop] theorem inverseDenominatorHessian_continuous : Continuous (inverseDenominatorHessian : E → E →L[ℝ] E) := by
  have hrank : Continuous (fun u : E => (innerSL ℝ u).smulRight u) :=
    (ContinuousLinearMap.smulRightL ℝ E E).continuous₂.comp
      ((innerSL ℝ (E := E)).continuous.prodMk continuous_id)
  unfold inverseDenominatorHessian
  apply Continuous.add
  · apply Continuous.smul
    · exact continuous_const.div (by fun_prop) (fun x => by positivity)
    · exact continuous_const
  · apply Continuous.smul
    · exact continuous_const.div (by fun_prop) (fun x => by positivity)
    · exact hrank

end UV
