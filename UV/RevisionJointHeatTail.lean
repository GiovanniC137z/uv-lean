import UV.RevisionJointHeatSelector
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-! Gaussian scaling of the exact Schläfli integral at large argument. -/

noncomputable section
open MeasureTheory Set Real Filter Asymptotics
open scoped Topology

namespace UV.RevisionJointHeat

private def besselGaussianWeight (v x : ℝ) : ℝ :=
  exp (2 * v * arsinh x) / sqrt (1 + x ^ 2)

private theorem besselGaussianWeight_nonneg (v x : ℝ) : 0 ≤ besselGaussianWeight v x := by
  unfold besselGaussianWeight
  positivity

private theorem continuous_besselGaussianWeight (v : ℝ) : Continuous (besselGaussianWeight v) := by
  unfold besselGaussianWeight
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro x
  exact (sqrt_pos.mpr (by positivity : 0 < 1 + x ^ 2)).ne'

/-- Exact change of variables from the positive Schläfli radial variable to
the whole real line. The exponential factor is an exact Gaussian. -/
private theorem bessel_gaussian_integral (v z : ℝ) :
    modifiedBesselK v z = exp (-z) * ∫ x : ℝ, besselGaussianWeight v x * exp (-(2 * z) * x ^ 2) := by
  let h : ℝ → ℝ := fun x => exp (2 * arsinh x)
  let g : ℝ → ℝ := fun t => t ^ (v - 1) * exp (-(z / 2) * (t + t⁻¹))
  have hderiv (x : ℝ) : HasDerivAt h (2 * h x / sqrt (1 + x ^ 2)) x := by
    have hd := ((hasDerivAt_arsinh x).const_mul 2).exp
    convert hd using 1
    simp only [h, div_eq_mul_inv]
    ring
  have himg : h '' (univ : Set ℝ) = Ioi 0 := by
    ext t
    constructor
    · rintro ⟨x, _, rfl⟩
      exact exp_pos _
    · intro ht
      refine ⟨sinh (log t / 2), mem_univ _, ?_⟩
      simp only [h, arsinh_sinh]
      rw [show 2 * (log t / 2) = log t by ring, exp_log ht]
  have hi := integral_image_eq_integral_abs_deriv_smul (s := (univ : Set ℝ))
    MeasurableSet.univ (fun x _ => (hderiv x).hasDerivWithinAt)
    ((exp_injective.comp (mul_right_injective₀ (two_ne_zero' ℝ))).comp arsinh_injective).injOn g
  rw [himg, setIntegral_univ] at hi
  unfold modifiedBesselK
  change (1 / 2 : ℝ) * (∫ t in Ioi 0, g t) = _
  rw [hi, ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  simp only [smul_eq_mul]
  rw [abs_of_nonneg (by dsimp [h]; positivity : 0 ≤ 2 * h x / sqrt (1 + x ^ 2))]
  have hc : h x + (h x)⁻¹ = 2 * (1 + 2 * x ^ 2) := by
    have hcosh : 2 * cosh (2 * arsinh x) = exp (2 * arsinh x) + exp (-(2 * arsinh x)) := by
      rw [cosh_eq]
      ring
    rw [show h x + (h x)⁻¹ = 2 * cosh (2 * arsinh x) by
      simp only [h, ← exp_neg, hcosh], cosh_two_mul, cosh_sq', sinh_arsinh]
    ring
  unfold g besselGaussianWeight
  rw [hc]
  change 1 / 2 * (2 * exp (2 * arsinh x) / sqrt (1 + x ^ 2) *
    (exp (2 * arsinh x) ^ (v - 1) * exp (-(z / 2) * (2 * (1 + 2 * x ^ 2))))) = _
  rw [← exp_mul]
  have he : exp (-(z / 2) * (2 * (1 + 2 * x ^ 2))) = exp (-z) * exp (-(2 * z) * x ^ 2) := by
    rw [← exp_add]
    congr 1
    ring
  rw [he]
  have hr : exp (2 * arsinh x) * exp ((2 * arsinh x) * (v - 1)) = exp (2 * v * arsinh x) := by
    rw [← exp_add]
    congr 1
    ring
  calc
    _ = (exp (2 * arsinh x) * exp ((2 * arsinh x) * (v - 1))) /
        sqrt (1 + x ^ 2) * (exp (-z) * exp (-(2 * z) * x ^ 2)) := by ring
    _ = _ := by rw [hr]; ring

private theorem abs_arsinh_le_abs (x : ℝ) : |arsinh x| ≤ |x| := by
  have hnonneg (a : ℝ) (ha : 0 ≤ a) : arsinh a ≤ a := by
    rw [← sinh_le_sinh, sinh_arsinh, self_le_sinh_iff]
    exact ha
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, abs_of_nonneg (arsinh_nonneg_iff.mpr hx)]
    exact hnonneg x hx
  · rw [abs_of_nonpos hx, abs_of_nonpos (arsinh_nonpos_iff.mpr hx), ← arsinh_neg]
    exact hnonneg (-x) (neg_nonneg.mpr hx)

private theorem sqrt_atTop : Tendsto Real.sqrt atTop atTop := by
  rw [show Real.sqrt = (fun x : ℝ => x ^ (1 / 2 : ℝ)) from funext Real.sqrt_eq_rpow]
  exact tendsto_rpow_atTop (by norm_num)

/-- Derived directly by dominated convergence on the scaled Gaussian.
No asymptotic assertion about the Bessel function is assumed. -/
theorem besselK_scaled_tendsto (v : ℝ) :
    Tendsto (fun z => sqrt (2 * z) * exp z * modifiedBesselK v z) atTop (𝓝 (sqrt π)) := by
  let G : ℝ → ℝ → ℝ := fun z x => besselGaussianWeight v ((sqrt (2 * z))⁻¹ * x) * exp (-x ^ 2)
  have hnormalized : (fun z : ℝ => sqrt (2 * z) * exp z * modifiedBesselK v z) =ᶠ[atTop]
      (fun z => ∫ x : ℝ, G z x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    have hs : 0 < sqrt (2 * z) := sqrt_pos.mpr (by positivity)
    have hscale (x : ℝ) : -(2 * z) * ((sqrt (2 * z))⁻¹ * x) ^ 2 = -x ^ 2 := by
      rw [mul_pow, inv_pow, sq_sqrt (by positivity : 0 ≤ 2 * z)]
      field_simp
    have hG : G z = (fun x => (fun y => besselGaussianWeight v y * exp (-(2 * z) * y ^ 2))
        ((sqrt (2 * z))⁻¹ * x)) := by
      ext x
      simp only [G, hscale]
    rw [hG, Measure.integral_comp_mul_left, inv_inv, abs_of_pos hs, smul_eq_mul, bessel_gaussian_integral]
    have he : exp z * exp (-z) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
    rw [show sqrt (2 * z) * exp z * (exp (-z) * ∫ x : ℝ,
      besselGaussianWeight v x * exp (-(2 * z) * x ^ 2)) =
      (exp z * exp (-z)) * (sqrt (2 * z) * ∫ x : ℝ,
        besselGaussianWeight v x * exp (-(2 * z) * x ^ 2)) by ring,
      he, one_mul]
  refine Tendsto.congr' hnormalized.symm ?_
  rw [← show (∫ x : ℝ, exp (-x ^ 2)) = sqrt π by simpa using integral_gaussian (1 : ℝ)]
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x : ℝ => exp (2 * v ^ 2) * exp (-(1 / 2 : ℝ) * x ^ 2))
  · exact Eventually.of_forall fun z =>
      ((continuous_besselGaussianWeight v).comp (by fun_prop : Continuous (fun x : ℝ =>
        (sqrt (2 * z))⁻¹ * x))).mul (by fun_prop) |>.aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
    apply Eventually.of_forall
    intro x
    let y := (sqrt (2 * z))⁻¹ * x
    have hs : 1 ≤ sqrt (2 * z) := by
      rw [le_sqrt (by norm_num) (by linarith)]
      linarith
    have hy : |y| ≤ |x| := by
      dsimp [y]
      rw [abs_mul, abs_inv, abs_of_pos (by linarith : 0 < sqrt (2 * z))]
      exact mul_le_of_le_one_left (abs_nonneg _) (inv_le_one_of_one_le₀ hs)
    have hv : 2 * v * arsinh y ≤ 2 * |v| * |x| := by
      calc
        _ ≤ |2 * v * arsinh y| := le_abs_self _
        _ = 2 * |v| * |arsinh y| := by simp [abs_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left ((abs_arsinh_le_abs y).trans hy) (by positivity)
    have hbound : 2 * v * arsinh y - x ^ 2 ≤ 2 * v ^ 2 - (1 / 2 : ℝ) * x ^ 2 := by
      nlinarith [sq_nonneg (|x| - 2 * |v|), sq_abs x, sq_abs v]
    change ‖besselGaussianWeight v y * exp (-x ^ 2)‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (besselGaussianWeight_nonneg v y) (exp_nonneg _))]
    unfold besselGaussianWeight
    have hden : 1 ≤ sqrt (1 + y ^ 2) := by
      rw [le_sqrt (by norm_num) (by positivity)]
      nlinarith [sq_nonneg y]
    refine (mul_le_mul_of_nonneg_right
      (div_le_self (exp_nonneg _) hden) (exp_nonneg _)).trans ?_
    rw [← exp_add, ← exp_add]
    apply exp_le_exp.mpr
    linarith
  · apply Integrable.const_mul
    exact integrable_exp_neg_mul_sq (by norm_num)
  · apply Eventually.of_forall
    intro x
    have hsq : Tendsto (fun z : ℝ => sqrt (2 * z)) atTop atTop :=
      sqrt_atTop.comp (Tendsto.const_mul_atTop two_pos tendsto_id)
    have hy : Tendsto (fun z : ℝ => (sqrt (2 * z))⁻¹ * x) atTop (𝓝 0) := by
      simpa only [zero_mul] using hsq.inv_tendsto_atTop.mul_const x
    have hw := (continuous_besselGaussianWeight v).continuousAt.tendsto.comp hy
    have h0 : besselGaussianWeight v 0 = 1 := by simp [besselGaussianWeight]
    rw [h0] at hw
    simpa only [G, Function.comp_def, one_mul] using hw.mul_const (exp (-x ^ 2))

/-- The coefficient of the selector's asymptotic Laplace multiplier. -/
def selectorTailConstant (A B v : ℝ) : ℝ := sqrt π * B ^ (v / 2 - 1 / 4) / selectorZ A B v

private theorem selectorTailConstant_pos {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (v : ℝ) :
    0 < selectorTailConstant A B v := by
  unfold selectorTailConstant
  exact div_pos (mul_pos (sqrt_pos.mpr pi_pos) (Real.rpow_pos_of_pos hB _)) (selectorZ_pos hA hB v)

/-- Exact reduction of the selector multiplier to its large-argument Bessel
factor. This identity also pins the power and constant in the limit. -/
private theorem selectorTransform_tail_factor {A B ω : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hω : 0 ≤ ω) (v : ℝ) :
    selectorTransform A B v ω =
      let X := A + ω
      let z := 2 * sqrt (B * X)
      (selectorTailConstant A B v * X ^ (-v / 2 - 1 / 4) * exp (-z)) *
        (sqrt (2 * z) * exp z * modifiedBesselK v z / sqrt π) := by
  let X := A + ω
  let z := 2 * sqrt (B * X)
  change selectorTransform A B v ω =
    (selectorTailConstant A B v * X ^ (-v / 2 - 1 / 4) * exp (-z)) *
      (sqrt (2 * z) * exp z * modifiedBesselK v z / sqrt π)
  have hX : 0 < X := by dsimp [X]; linarith
  have hs : sqrt (2 * z) = 2 * (B ^ (1 / 4 : ℝ) * X ^ (1 / 4 : ℝ)) := by
    dsimp [z]
    rw [show 2 * (2 * sqrt (B * X)) = 4 * sqrt (B * X) by ring,
      sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show sqrt (4 : ℝ) = 2 by norm_num]
    congr 1
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (mul_nonneg hB.le hX.le),
      show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num,
      Real.mul_rpow hB.le hX.le]
  have hx : (B / X) ^ (v / 2) = (B ^ (v / 2 - 1 / 4) * B ^ (1 / 4 : ℝ)) *
      (X ^ (-v / 2 - 1 / 4) * X ^ (1 / 4 : ℝ)) := by
    rw [← Real.rpow_add hB, ← Real.rpow_add hX,
      Real.div_rpow hB.le hX.le, div_eq_mul_inv, ← Real.rpow_neg hX.le]
    congr 2 <;> ring
  have he : exp (-z) * exp z = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
  rw [selectorTransform_Z hA hB hω, selectorZ_bessel hX hB, mul_comm X B]
  change 2 * (B / X) ^ (v / 2) * modifiedBesselK v z / selectorZ A B v = _
  rw [hs, hx]
  unfold selectorTailConstant
  rw [show (sqrt π * B ^ (v / 2 - 1 / 4) / selectorZ A B v * X ^ (-v / 2 - 1 / 4) * exp (-z)) *
      (2 * (B ^ (1 / 4 : ℝ) * X ^ (1 / 4 : ℝ)) * exp z * modifiedBesselK v z / sqrt π) =
      (exp (-z) * exp z) * (sqrt π / sqrt π) *
        (2 * ((B ^ (v / 2 - 1 / 4) * B ^ (1 / 4 : ℝ)) *
          (X ^ (-v / 2 - 1 / 4) * X ^ (1 / 4 : ℝ))) * modifiedBesselK v z / selectorZ A B v) by ring]
  rw [he, div_self (sqrt_pos.mpr pi_pos).ne', one_mul, one_mul]

/-- The first large-argument equivalence in the selector proposition. -/
theorem selectorTransform_asymptotic {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (v : ℝ) :
    selectorTransform A B v ~[atTop] (fun ω => selectorTailConstant A B v *
      (A + ω) ^ (-v / 2 - 1 / 4) * exp (-2 * sqrt (B * (A + ω)))) := by
  let z := fun ω : ℝ => 2 * sqrt (B * (A + ω))
  have hz : Tendsto z atTop atTop := by
    dsimp [z]
    exact Tendsto.const_mul_atTop two_pos (sqrt_atTop.comp (Tendsto.const_mul_atTop hB
      (tendsto_atTop_add_const_left atTop A tendsto_id)))
  have ht := (besselK_scaled_tendsto v).comp hz
  have ht' := ht.div_const (sqrt π)
  rw [div_self (sqrt_pos.mpr pi_pos).ne'] at ht'
  have he : ∀ᶠ ω : ℝ in atTop,
      selectorTailConstant A B v * (A + ω) ^ (-v / 2 - 1 / 4) * exp (-2 * sqrt (B * (A + ω))) ≠ 0 := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with ω hω
    exact (mul_pos (mul_pos (selectorTailConstant_pos hA hB v)
      (Real.rpow_pos_of_pos (by linarith) _)) (exp_pos _)).ne'
  apply (isEquivalent_iff_tendsto_one he).mpr
  refine ht'.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ), he] with ω hω hne
  have h := selectorTransform_tail_factor hA hB hω v
  dsimp only [z, Function.comp_apply, Pi.div_apply] at *
  rw [h]
  simp only [neg_mul] at hne ⊢
  exact (mul_div_cancel_left₀ _ hne).symm

private theorem bounded_over_atTop {f g : ℝ → ℝ} {C : ℝ}
    (hC : ∀ᶠ x in atTop, |f x| ≤ C) (hg : Tendsto g atTop atTop) :
    Tendsto (fun x => f x / g x) atTop (𝓝 0) := by
  have hu : Tendsto (fun x => C / g x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hg.inv_tendsto_atTop.const_mul C
  have hl : Tendsto (fun x => -C / g x) atTop (𝓝 0) := by
    simpa only [neg_div, neg_zero] using hu.neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [hC, hg.eventually_gt_atTop (0 : ℝ)] with x hx hgx
    exact div_le_div_of_nonneg_right (abs_le.mp hx).1 hgx.le
  · filter_upwards [hC, hg.eventually_gt_atTop (0 : ℝ)] with x hx hgx
    exact div_le_div_of_nonneg_right (abs_le.mp hx).2 hgx.le

/-- The precise stretched-exponential ultraviolet rate after composing the
selector with the internal square-root profile at fixed mass. -/
theorem selectorInternal_asymptotic {A B M : ℝ} (hA : 0 < A) (hB : 0 < B) (hM : 0 ≤ M) (v : ℝ) :
    (fun x => selectorTransform A B v (2 * depthProfile M x)) ~[atTop]
      (fun x => selectorTailConstant A B v * (2 : ℝ) ^ (-v / 2 - 1 / 4) *
        x ^ (-v / 4 - 1 / 8) * exp (-2 * sqrt (2 * B) * x ^ (1 / 4 : ℝ))) := by
  let Y : ℝ → ℝ := fun x => 2 * depthProfile M x
  let X : ℝ → ℝ := fun x => A + Y x
  let X0 : ℝ → ℝ := fun x => 2 * sqrt x
  let a : ℝ := -v / 2 - 1 / 4
  let C := selectorTailConstant A B v
  have hX0 : Tendsto X0 atTop atTop := Tendsto.const_mul_atTop two_pos sqrt_atTop
  have hY : Tendsto Y atTop atTop := by
    apply tendsto_atTop_mono' _ _ (tendsto_atTop_add_const_right atTop (-2 * M) hX0)
    apply Eventually.of_forall
    intro x
    dsimp [Y, X0]
    linarith [sqrt_sub_le_depthProfile M x]
  have hX : Tendsto X atTop atTop := tendsto_atTop_add_const_left atTop A hY
  have hdiff : ∀ᶠ x : ℝ in atTop, |X x - X0 x| ≤ A + 2 * M := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    apply abs_le.mpr
    dsimp [X, Y, X0]
    constructor
    · linarith [sqrt_sub_le_depthProfile M x]
    · linarith [depthProfile_le_sqrt hM hx]
  have hratio : Tendsto (fun x => X x / X0 x) atTop (𝓝 1) := by
    have hh := (bounded_over_atTop hdiff hX0).const_add (1 : ℝ)
    rw [add_zero] at hh
    refine hh.congr' ?_
    filter_upwards [hX0.eventually_gt_atTop (0 : ℝ)] with x hx
    have hn := hx.ne'
    field_simp
    ring
  have hp := hratio.rpow_const (p := a) (Or.inl one_ne_zero)
  rw [Real.one_rpow] at hp
  have hdif : Tendsto (fun x => sqrt (B * X x) - sqrt (B * X0 x)) atTop (𝓝 0) := by
    have hsum : Tendsto (fun x => sqrt (B * X x) + sqrt (B * X0 x)) atTop atTop := by
      apply tendsto_atTop_mono _ (sqrt_atTop.comp (Tendsto.const_mul_atTop hB hX0))
      intro x
      exact le_add_of_nonneg_left (sqrt_nonneg _)
    have hbd : ∀ᶠ x : ℝ in atTop, |B * (X x - X0 x)| ≤ B * (A + 2 * M) := by
      filter_upwards [hdiff] with x hx
      rw [abs_mul, abs_of_pos hB]
      exact mul_le_mul_of_nonneg_left hx hB.le
    refine (bounded_over_atTop hbd hsum).congr' ?_
    filter_upwards [hX.eventually_gt_atTop (0 : ℝ), hX0.eventually_gt_atTop (0 : ℝ)] with x hx hy
    have hs₁ := sqrt_pos.mpr (mul_pos hB hx)
    have hs₂ := sqrt_pos.mpr (mul_pos hB hy)
    apply (div_eq_iff (add_pos hs₁ hs₂).ne').mpr
    rw [show ∀ a b : ℝ, (a - b) * (a + b) = a ^ 2 - b ^ 2 by intros; ring,
      sq_sqrt (mul_nonneg hB.le hx.le), sq_sqrt (mul_nonneg hB.le hy.le)]
    ring
  have hdif' : Tendsto (fun x => (-2 : ℝ) * (sqrt (B * X x) - sqrt (B * X0 x))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (Filter.Tendsto.const_mul (-2 : ℝ) hdif)
  have hex : Tendsto (fun x => exp ((-2 : ℝ) * (sqrt (B * X x) - sqrt (B * X0 x)))) atTop (𝓝 1) := by
    simpa only [exp_zero, Function.comp_apply] using
      (Real.continuous_exp.continuousAt (x := 0).tendsto.comp hdif')
  have hr := hp.mul hex
  rw [one_mul] at hr
  have he₀ : ∀ᶠ x : ℝ in atTop, C * X0 x ^ a * exp (-2 * sqrt (B * X0 x)) ≠ 0 := by
    filter_upwards [hX0.eventually_gt_atTop (0 : ℝ)] with x hx
    exact (mul_pos (mul_pos (selectorTailConstant_pos hA hB v) (Real.rpow_pos_of_pos hx _)) (exp_pos _)).ne'
  have hasym : (fun x => C * X x ^ a * exp (-2 * sqrt (B * X x))) ~[atTop]
      (fun x => C * X0 x ^ a * exp (-2 * sqrt (B * X0 x))) := by
    apply (isEquivalent_iff_tendsto_one he₀).mpr
    refine hr.congr' ?_
    filter_upwards [hX.eventually_gt_atTop (0 : ℝ), hX0.eventually_gt_atTop (0 : ℝ)] with x hx hy
    change (X x / X0 x) ^ a * exp (-2 * (sqrt (B * X x) - sqrt (B * X0 x))) =
      (C * X x ^ a * exp (-2 * sqrt (B * X x))) / (C * X0 x ^ a * exp (-2 * sqrt (B * X0 x)))
    rw [Real.div_rpow hx.le hy.le, mul_sub, exp_sub]
    field_simp [(selectorTailConstant_pos hA hB v).ne', (Real.rpow_pos_of_pos hy a).ne', (exp_pos _).ne']
    exact (div_self (show C ≠ 0 from (selectorTailConstant_pos hA hB v).ne')).symm
  have h0eq : (fun x => C * X0 x ^ a * exp (-2 * sqrt (B * X0 x))) =ᶠ[atTop]
      (fun x => C * (2 : ℝ) ^ a * x ^ (-v / 4 - 1 / 8) * exp (-2 * sqrt (2 * B) * x ^ (1 / 4 : ℝ))) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have hpow : X0 x ^ a = (2 : ℝ) ^ a * x ^ (-v / 4 - 1 / 8) := by
      dsimp [X0]
      rw [Real.mul_rpow two_pos.le (sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
      dsimp [a]
      congr 2
      ring
    have hsqrt : sqrt (B * X0 x) = sqrt (2 * B) * x ^ (1 / 4 : ℝ) := by
      dsimp [X0]
      rw [show B * (2 * sqrt x) = (2 * B) * sqrt x by ring, sqrt_mul (by positivity),
        Real.sqrt_eq_rpow (sqrt x), Real.sqrt_eq_rpow x, ← Real.rpow_mul hx]
      norm_num
    rw [hpow, hsqrt]
    ring_nf
  exact ((selectorTransform_asymptotic hA hB v).comp_tendsto hY).trans
    (hasym.congr_right h0eq)

end UV.RevisionJointHeat
