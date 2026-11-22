import UV.RevisionLegacyCosine
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Literal stable-half bubble on the fixed unit spatial coordinate axis. -/

noncomputable section

open MeasureTheory Filter Real
open scoped Topology

namespace UV

/-- The scalar bubble on the same Euclidean unit coordinate axis used in the
sixth-difference obstruction. -/
def stableAxisBubble (a m h : ℝ) : ℝ :=
  scalarBubble a 0 m (scalarAxis h)

theorem stableAxisBubble_cosine {a m : ℝ} (ha : 0 < a) (hm : 0 < m) (h : ℝ) :
    stableAxisBubble a m h =
      ∫ x : ScalarMomentum, Real.cos (h * x 0) * stableCoordinateCovariance a m x ^ 2 := by
  have he := congrArg Complex.re (scalarBubble_stable_coordinate_square ha hm (scalarAxis h))
  rw [Complex.ofReal_re, coordinateSquareFourier_axis_re
    (stableCoordinateCovariance_continuous ha hm).measurable
    (stableCoordinateCovariance_square_integrable ha hm), coordinateProjectionMeasure_cosine
    (stableCoordinateCovariance_continuous ha hm).measurable] at he
  exact he

/-- Derivative density with respect to the scalar axis parameter, including
its exact coordinate-power factor. -/
def stableAxisDerivativeDensity (a m : ℝ) (n : ℕ) (h : ℝ) (x : ScalarMomentum) : ℝ :=
  (x 0) ^ n * iteratedDeriv n Real.cos (h * x 0) * stableCoordinateCovariance a m x ^ 2

private theorem stableAxisDerivativeDensity_continuous {a m : ℝ} (ha : 0 < a) (hm : 0 < m)
    (n : ℕ) (h : ℝ) : Continuous (stableAxisDerivativeDensity a m n h) := by
  let co := PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0
  have h1 := ((Real.differentiable_iteratedDeriv_cos n).continuous.comp
    (continuous_const.mul co : Continuous (fun x : ScalarMomentum => h * x 0)))
  exact ((co.pow n).mul h1).mul ((stableCoordinateCovariance_continuous ha hm).pow 2)

private theorem stableAxisDerivativeDensity_bound (a m : ℝ) (n : ℕ) (h : ℝ) (x : ScalarMomentum) :
    ‖stableAxisDerivativeDensity a m n h x‖ ≤
      ‖x‖ ^ n * stableCoordinateCovariance a m x ^ 2 := by
  have hx : |x 0| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
  rw [stableAxisDerivativeDensity, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
    abs_of_nonneg (sq_nonneg (stableCoordinateCovariance a m x))]
  exact mul_le_mul_of_nonneg_right
    ((mul_le_of_le_one_right (pow_nonneg (abs_nonneg _) _) (Real.abs_iteratedDeriv_cos_le_one _ _)).trans
      (pow_le_pow_left₀ (abs_nonneg _) hx _)) (sq_nonneg _)

private theorem stableAxisDerivativeDensity_hasDerivAt (a m : ℝ) (n : ℕ) (h : ℝ) (x : ScalarMomentum) :
    HasDerivAt (fun u => stableAxisDerivativeDensity a m n u x)
      (stableAxisDerivativeDensity a m (n + 1) h x) h := by
  have hd := (((Real.differentiable_iteratedDeriv_cos n (h * x 0)).hasDerivAt).comp h
    ((hasDerivAt_id h).mul_const (x 0))).const_mul ((x 0) ^ n)
  have he := hd.mul_const (stableCoordinateCovariance a m x ^ 2)
  convert he using 1
  simp only [stableAxisDerivativeDensity, iteratedDeriv_succ, pow_succ]
  ring

private theorem stableAxisIntegral_hasDerivAt {a m : ℝ} (ha : 0 < a) (hm : 0 < m) {n : ℕ}
    (hn : n + 1 ≤ 5) (h : ℝ) :
    HasDerivAt (fun u => ∫ x, stableAxisDerivativeDensity a m n u x)
      (∫ x, stableAxisDerivativeDensity a m (n+1) h x) h := by
  have hmom {k : ℕ} (hk : k ≤ 5) :
      Integrable (fun x : ScalarMomentum => ‖x‖^k * stableCoordinateCovariance a m x ^ 2) :=
    stableConvolution_square_moment_integrable ha hm k hk
  have hcont (k : ℕ) (u : ℝ) :
      AEStronglyMeasurable (stableAxisDerivativeDensity a m k u) volume :=
    (stableAxisDerivativeDensity_continuous ha hm k u).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := stableAxisDerivativeDensity a m n) (F' := stableAxisDerivativeDensity a m (n+1))
    (x₀ := h) (ε := 1) (μ := volume)
    (bound := fun x : ScalarMomentum => ‖x‖^(n+1) * stableCoordinateCovariance a m x ^ 2)
    zero_lt_one (Eventually.of_forall (hcont n))
    ((hmom (by omega : n ≤ 5)).mono' (hcont n h)
      (Eventually.of_forall (stableAxisDerivativeDensity_bound a m n h)))
    (hcont (n+1) h)
    (Eventually.of_forall fun x u _ => stableAxisDerivativeDensity_bound a m (n+1) u x)
    (hmom hn) (Eventually.of_forall fun x u _ => stableAxisDerivativeDensity_hasDerivAt a m n u x)).2

/-- Differentiation under the literal cosine integral through the highest
finite integer moment. -/
theorem stableAxisBubble_iteratedDeriv {a m : ℝ} (ha : 0 < a) (hm : 0 < m) {n : ℕ} (hn : n ≤ 5) :
    iteratedDeriv n (stableAxisBubble a m) = fun h => ∫ x, stableAxisDerivativeDensity a m n h x := by
  induction n with
  | zero =>
      funext h
      rw [iteratedDeriv_zero, stableAxisBubble_cosine ha hm]
      simp only [stableAxisDerivativeDensity, pow_zero, iteratedDeriv_zero, one_mul]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih (by omega)]
      funext h
      exact (stableAxisIntegral_hasDerivAt ha hm hn h).deriv

/-- The scalar cosine remainder after subtracting the actual Taylor
coefficients of the literal momentum-space bubble. -/
theorem stableAxisBubble_taylor_four_integral {a m : ℝ} (ha : 0 < a) (hm : 0 < m) (h : ℝ) :
    stableAxisBubble a m h - stableAxisBubble a m 0 -
      (iteratedDeriv 2 (stableAxisBubble a m) 0 / 2) * h ^ 2 -
      (iteratedDeriv 4 (stableAxisBubble a m) 0 / 24) * h ^ 4 =
      ∫ x : ScalarMomentum, stableCosRemainder (h * x 0) * stableCoordinateCovariance a m x ^ 2 := by
  let C := stableCoordinateCovariance a m
  have hC : Continuous C := stableCoordinateCovariance_continuous ha hm
  let co := PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0
  have hM {n : ℕ} (hn : n ≤ 5) : Integrable (fun x : ScalarMomentum => (x 0)^n * C x^2) := by
    apply (stableConvolution_square_moment_integrable ha hm n hn).mono' ((co.pow n).mul
      (hC.pow 2)).aestronglyMeasurable
    filter_upwards with x
    have hx : |x 0| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
    rw [norm_mul, Real.norm_eq_abs, abs_pow, Real.norm_of_nonneg (sq_nonneg (C x))]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hx _) (sq_nonneg _)
  have h0 : Integrable (fun x : ScalarMomentum => C x^2) := stableCoordinateCovariance_square_integrable ha hm
  have hcos : Integrable (fun x : ScalarMomentum => cos (h * x 0) * C x^2) := by
    apply h0.mono' ((Real.continuous_cos.comp (continuous_const.mul co)).mul (hC.pow 2)).aestronglyMeasurable
    filter_upwards with x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (sq_nonneg (C x))]
    exact mul_le_of_le_one_left (sq_nonneg _) (abs_cos_le_one _)
  have h2 : iteratedDeriv 2 (stableAxisBubble a m) 0 = -(∫ x : ScalarMomentum, (x 0)^2 * C x^2) := by
    rw [stableAxisBubble_iteratedDeriv ha hm (by decide), ← integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    simp [stableAxisDerivativeDensity, C]
  have h4 : iteratedDeriv 4 (stableAxisBubble a m) 0 = ∫ x : ScalarMomentum, (x 0)^4 * C x^2 := by
    rw [stableAxisBubble_iteratedDeriv ha hm (by decide)]
    apply integral_congr_ae
    filter_upwards with x
    simp [stableAxisDerivativeDensity, C]
  rw [stableAxisBubble_cosine ha hm h, stableAxisBubble_cosine ha hm 0, h2, h4]
  simp only [zero_mul, cos_zero, one_mul]
  have he :
      (fun x : ScalarMomentum => stableCosRemainder (h * x 0) * C x^2) =
      fun x => cos (h * x 0) * C x^2 - C x^2 + (h^2/2) * ((x 0)^2 * C x^2) -
        (h^4/24) * ((x 0)^4 * C x^2) := by
    funext x
    unfold stableCosRemainder
    ring
  change _ = ∫ x, stableCosRemainder (h * x 0) * C x^2
  rw [he]
  let f0 := fun x : ScalarMomentum => C x ^ 2
  let fc := fun x : ScalarMomentum => cos (h * x 0) * C x ^ 2
  let f2 := fun x : ScalarMomentum => h ^ 2 / 2 * ((x 0) ^ 2 * C x ^ 2)
  let f4 := fun x : ScalarMomentum => h ^ 4 / 24 * ((x 0) ^ 4 * C x ^ 2)
  change _ = ∫ x, (((fc - f0) + f2) - f4) x
  have hi2 : Integrable f2 := (hM (by decide : 2 ≤ 5)).const_mul _
  have hi4 : Integrable f4 := (hM (by decide : 4 ≤ 5)).const_mul _
  have hc0 : Integrable (fc - f0) := hcos.sub h0
  have heval := integral_sub (hc0.add hi2) hi4
  change _ = ∫ x, ((fc-f0)+f2) x - f4 x
  rw [heval]
  rw [show (∫ x, ((fc-f0)+f2) x) = (∫ x, (fc-f0) x) + ∫ x, f2 x from integral_add hc0 hi2]
  have he0 := integral_sub hcos h0
  change _ = (∫ x, fc x - f0 x) + (∫ x, f2 x) - ∫ x, f4 x
  rw [he0]
  unfold f2 f4
  rw [integral_const_mul, integral_const_mul]
  ring

end UV
