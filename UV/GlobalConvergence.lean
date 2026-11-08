import UV.Convergence
import UV.KernelMeasure
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal BigOperators

namespace UV

abbrev LoopMomentum := EuclideanSpace ℝ (Fin 4)

/-- The four-dimensional radial Gaussian appearing after the selected massless
line denominator is retained. The value at the origin is irrelevant to volume. -/
theorem massless_gaussian_integrable {d b : ℝ} (hd : 0 ≤ d) (hb : 0 < b) :
    Integrable (fun q : LoopMomentum => ‖q‖ ^ (d - 2) * exp (-b * ‖q‖ ^ 2)) := by
  apply (integrable_fun_norm_addHaar (E := LoopMomentum) volume
    (f := fun r : ℝ => r ^ (d - 2) * exp (-b * r ^ 2))).mpr
  have h := integrableOn_rpow_mul_exp_neg_mul_sq hb (show -1 < d + 1 by linarith)
  apply h.congr_fun _ measurableSet_Ioi
  intro r hr
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
  simp only [← mul_assoc]
  rw [← Real.rpow_natCast r 3, ← Real.rpow_add hr]
  congr 2
  norm_num
  ring

theorem massless_gaussian_integral {d b : ℝ} (hd : 0 ≤ d) (hb : 0 < b) :
    (∫ q : LoopMomentum, ‖q‖ ^ (d - 2) * exp (-b * ‖q‖ ^ 2)) =
      π ^ 2 * b ^ (-(1 + d / 2)) * Gamma (1 + d / 2) := by
  rw [integral_fun_norm_addHaar (E := LoopMomentum) volume
    (fun r : ℝ => r ^ (d - 2) * exp (-b * r ^ 2))]
  have hrad : (∫ r : ℝ in Ioi 0,
      r ^ (Module.finrank ℝ LoopMomentum - 1) • (r ^ (d - 2) * exp (-b * r ^ 2))) =
      ∫ r : ℝ in Ioi 0, r ^ (d + 1) * exp (-b * r ^ 2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
    simp only [← mul_assoc]
    rw [← Real.rpow_natCast r 3, ← Real.rpow_add hr]
    congr 2
    norm_num
    ring
  rw [hrad]
  have hradval := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := d + 1)
    (by norm_num) (by linarith) hb
  simp only [Real.rpow_two] at hradval
  rw [hradval]
  have hball : volume.real (Metric.ball (0 : LoopMomentum) 1) = π ^ 2 / 2 := by
    rw [measureReal_def, EuclideanSpace.volume_ball]
    norm_num [Real.Gamma_nat_eq_factorial, Real.sq_sqrt (Real.pi_nonneg)]
    rw [ENNReal.toReal_ofReal (by positivity)]
    congr 1
    nlinarith [Real.sq_sqrt Real.pi_nonneg]
  simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
  rw [hball]
  have he : -(d + 1 + 1) / 2 = -(1 + d / 2) := by ring
  have he' : (d + 1 + 1) / 2 = 1 + d / 2 := by ring
  rw [he, he']
  ring

/-- Nonnegative Laplace mixture on strictly positive proper times. The source's
separate support and no-atom conditions identify this with its full mixture. -/
def positiveLaplace (ρ : Measure ℝ) (z : ℝ) : ℝ≥0∞ :=
  ∫⁻ τ in Ioi 0, ENNReal.ofReal (exp (-τ * z)) ∂ρ

theorem massless_gaussian_lintegral {d b : ℝ} (hd : 0 ≤ d) (hb : 0 < b) :
    (∫⁻ q : LoopMomentum, ENNReal.ofReal (‖q‖ ^ (d - 2)) *
      ENNReal.ofReal (exp (-b * ‖q‖ ^ 2))) =
      ENNReal.ofReal (π ^ 2 * b ^ (-(1 + d / 2)) * Gamma (1 + d / 2)) := by
  simp_rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]
  rw [← ofReal_integral_eq_lintegral_ofReal (massless_gaussian_integrable hd hb)
    (Filter.Eventually.of_forall fun q => by positivity)]
  rw [massless_gaussian_integral hd hb]

theorem massless_laplace_moment (ρ : Measure ℝ) [SFinite ρ]
    {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d) :
    (∫⁻ q : LoopMomentum, ENNReal.ofReal (‖q‖ ^ (d - 2)) *
      positiveLaplace ρ (a ^ 2 * ‖q‖ ^ 2)) =
      ENNReal.ofReal (π ^ 2 * Gamma (1 + d / 2) * a ^ (-2 - d)) *
        inverseMoment ρ (1 + d / 2) := by
  unfold positiveLaplace
  simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_lintegral_swap (by fun_prop)]
  have hpoint : ∀ τ ∈ Ioi (0 : ℝ),
      (∫⁻ q : LoopMomentum, ENNReal.ofReal (‖q‖ ^ (d - 2)) *
        ENNReal.ofReal (exp (-τ * (a ^ 2 * ‖q‖ ^ 2)))) =
        ENNReal.ofReal (π ^ 2 * Gamma (1 + d / 2) * a ^ (-2 - d)) *
          ENNReal.ofReal (τ ^ (-(1 + d / 2))) := by
    intro τ hτ
    have he : ∀ q : LoopMomentum, -τ * (a ^ 2 * ‖q‖ ^ 2) =
        -(a ^ 2 * τ) * ‖q‖ ^ 2 := by intro q; ring
    simp_rw [he]
    rw [massless_gaussian_lintegral hd (mul_pos (sq_pos_of_pos ha) hτ)]
    have hpow : (a ^ 2 * τ) ^ (-(1 + d / 2)) =
        a ^ (-2 - d) * τ ^ (-(1 + d / 2)) := by
      rw [Real.mul_rpow (sq_nonneg a) hτ.le, ← Real.rpow_natCast a 2,
        ← Real.rpow_mul ha.le]
      congr 2
      norm_num
      ring
    rw [hpow, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  calc
    _ = ∫⁻ τ in Ioi 0,
        ENNReal.ofReal (π ^ 2 * Gamma (1 + d / 2) * a ^ (-2 - d)) *
        ENNReal.ofReal (τ ^ (-(1 + d / 2))) ∂ρ := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      exact hpoint
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl

theorem positiveLaplace_le_mass (ρ : Measure ℝ) {z : ℝ} (hz : 0 ≤ z) :
    positiveLaplace ρ z ≤ ρ (Ioi 0) := by
  unfold positiveLaplace
  calc
    _ ≤ ∫⁻ _ in Ioi (0 : ℝ), (1 : ℝ≥0∞) ∂ρ := by
      apply setLIntegral_mono' measurableSet_Ioi
      intro τ hτ
      have h : exp (-τ * z) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_of_lt hτ)) hz)
      simpa using ENNReal.ofReal_le_ofReal h
    _ = _ := by simp

theorem positiveLaplace_ne_top (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {z : ℝ} (hz : 0 ≤ z) : positiveLaplace ρ z ≠ ⊤ :=
  ne_top_of_le_ne_top (measure_ne_top ρ _) (positiveLaplace_le_mass ρ hz)

/-- The actual selected virtual line, including its massless denominator. -/
def selectedLine (ρ : Measure ℝ) (a m : ℝ) (q : LoopMomentum) : ℝ :=
  (positiveLaplace ρ (a ^ 2 * ‖q‖ ^ 2)).toReal / (‖q‖ ^ 2 + m ^ 2)

theorem selectedLine_nonneg (ρ : Measure ℝ) (a m : ℝ) (q : LoopMomentum) :
    0 ≤ selectedLine ρ a m q := by unfold selectedLine; positivity

theorem selectedLine_measurable (ρ : Measure ℝ) [SFinite ρ] (a m : ℝ) :
    Measurable (selectedLine ρ a m) := by
  unfold selectedLine positiveLaplace
  fun_prop

theorem massless_selectedLine_ae (ρ : Measure ℝ) (a d : ℝ) :
    (fun q : LoopMomentum => ‖q‖ ^ d * selectedLine ρ a 0 q) =ᵐ[volume]
      fun q => ‖q‖ ^ (d - 2) * (positiveLaplace ρ (a ^ 2 * ‖q‖ ^ 2)).toReal := by
  have hq : ∀ᵐ q : LoopMomentum, q ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [hq] with q hq
  have hp : 0 < ‖q‖ := norm_pos_iff.mpr hq
  unfold selectedLine
  simp only [sq, zero_mul, add_zero]
  rw [Real.rpow_sub hp, Real.rpow_two]
  ring

theorem massless_selectedLine_lintegral (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d) :
    (∫⁻ q : LoopMomentum, ENNReal.ofReal (‖q‖ ^ d * selectedLine ρ a 0 q)) =
      ENNReal.ofReal (π ^ 2 * Gamma (1 + d / 2) * a ^ (-2 - d)) *
        inverseMoment ρ (1 + d / 2) := by
  have h := massless_selectedLine_ae ρ a d
  have hh := lintegral_congr_ae (h.fun_comp ENNReal.ofReal)
  dsimp only [Function.comp_def] at hh
  rw [hh]
  calc
    _ = ∫⁻ q : LoopMomentum, ENNReal.ofReal (‖q‖ ^ (d - 2)) *
        positiveLaplace ρ (a ^ 2 * ‖q‖ ^ 2) := by
      apply lintegral_congr
      intro q
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _),
        ENNReal.ofReal_toReal (positiveLaplace_ne_top ρ (show 0 ≤ a ^ 2 * ‖q‖ ^ 2 by positivity))]
    _ = _ := massless_laplace_moment ρ ha hd

theorem massless_selectedLine_integrable_iff (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d) :
    Integrable (fun q : LoopMomentum => ‖q‖ ^ d * selectedLine ρ a 0 q) ↔
      inverseMoment ρ (1 + d / 2) < ⊤ := by
  have hm : AEStronglyMeasurable
      (fun q : LoopMomentum => ‖q‖ ^ d * selectedLine ρ a 0 q) volume :=
    ((continuous_norm.rpow_const fun _ => Or.inr hd).measurable.mul
      (selectedLine_measurable ρ a 0)).aestronglyMeasurable
  have hn : ∀ᵐ q : LoopMomentum, 0 ≤ ‖q‖ ^ d * selectedLine ρ a 0 q :=
    Filter.Eventually.of_forall fun q =>
      mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (selectedLine_nonneg ρ a 0 q)
  rw [← lintegral_ofReal_ne_top_iff_integrable hm hn]
  rw [massless_selectedLine_lintegral ρ ha hd]
  have hc : (0 : ℝ) < π ^ 2 * Gamma (1 + d / 2) * a ^ (-2 - d) := by
    apply mul_pos (mul_pos (sq_pos_of_pos Real.pi_pos) (Real.Gamma_pos_of_pos (by linarith)))
    exact Real.rpow_pos_of_pos ha _
  constructor
  · intro h
    apply lt_top_iff_ne_top.mpr
    intro hm
    rw [hm, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hc)] at h
    exact h rfl
  · intro h
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h.ne

theorem selectedLine_le_massless (ρ : Measure ℝ) (a m : ℝ)
    {q : LoopMomentum} (hq : q ≠ 0) : selectedLine ρ a m q ≤ selectedLine ρ a 0 q := by
  unfold selectedLine
  simp only [zero_pow two_ne_zero, add_zero]
  apply div_le_div_of_nonneg_left ENNReal.toReal_nonneg
    (sq_pos_of_pos (norm_pos_iff.mpr hq))
  nlinarith [sq_nonneg m]

theorem selectedLine_weight_integrable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d)
    (hM : inverseMoment ρ (1 + d / 2) < ⊤) (m : ℝ) :
    Integrable (fun q : LoopMomentum => ‖q‖ ^ d * selectedLine ρ a m q) := by
  apply ((massless_selectedLine_integrable_iff ρ ha hd).mpr hM).mono'
    (((continuous_norm.rpow_const fun _ => Or.inr hd).measurable.mul
      (selectedLine_measurable ρ a m)).aestronglyMeasurable)
  have hq : ∀ᵐ q : LoopMomentum, q ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [hq] with q hq
  rw [Real.norm_of_nonneg
    (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (selectedLine_nonneg ρ a m q))]
  exact mul_le_mul_of_nonneg_left (selectedLine_le_massless ρ a m hq)
    (Real.rpow_nonneg (norm_nonneg _) _)

theorem massless_selectedLine_integral (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d)
    (hM : inverseMoment ρ (1 + d / 2) < ⊤) :
    (∫ q : LoopMomentum, ‖q‖ ^ d * selectedLine ρ a 0 q) =
      π ^ 2 * Gamma (1 + d / 2) * a ^ (-2 - d) *
        (inverseMoment ρ (1 + d / 2)).toReal := by
  have hi := (massless_selectedLine_integrable_iff ρ ha hd).mpr hM
  have hn : ∀ᵐ q : LoopMomentum, 0 ≤ ‖q‖ ^ d * selectedLine ρ a 0 q :=
    Filter.Eventually.of_forall fun q =>
      mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (selectedLine_nonneg ρ a 0 q)
  have he := ofReal_integral_eq_lintegral_ofReal hi hn
  rw [massless_selectedLine_lintegral ρ ha hd] at he
  have he' := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hn), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)] at he'
  exact he'

theorem selectedLine_integral_le (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d)
    (hM : inverseMoment ρ (1 + d / 2) < ⊤) (m : ℝ) :
    (∫ q : LoopMomentum, ‖q‖ ^ d * selectedLine ρ a m q) ≤
      π ^ 2 * Gamma (1 + d / 2) * a ^ (-2 - d) *
        (inverseMoment ρ (1 + d / 2)).toReal := by
  rw [← massless_selectedLine_integral ρ ha hd hM]
  apply integral_mono_ae (selectedLine_weight_integrable ρ ha hd hM m)
    ((massless_selectedLine_integrable_iff ρ ha hd).mpr hM)
  have hq : ∀ᵐ q : LoopMomentum, q ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [hq] with q hq
  exact mul_le_mul_of_nonneg_left (selectedLine_le_massless ρ a m hq)
    (Real.rpow_nonneg (norm_nonneg _) _)

theorem ae_positive_of_support_no_atom (ρ : Measure ℝ)
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0) : ∀ᵐ τ ∂ρ, 0 < τ := by
  rw [ae_iff]
  have hs : {τ : ℝ | ¬ 0 < τ} = Iio 0 ∪ {0} := by
    ext τ
    simp only [mem_setOf_eq, not_lt, mem_union, mem_Iio, mem_singleton_iff]
    exact le_iff_lt_or_eq
  rw [hs]
  exact measure_union_null hneg hzero

theorem positiveLaplace_eq_ofReal_laplace (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0) {z : ℝ} (hz : 0 ≤ z) :
    positiveLaplace ρ z = ENNReal.ofReal (laplace ρ z) := by
  have hp := ae_positive_of_support_no_atom ρ hneg hzero
  have hr : ρ.restrict (Ioi 0) = ρ := Measure.restrict_eq_self_of_ae_mem hp
  have hi : Integrable (fun τ : ℝ => exp (-τ * z)) ρ := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    filter_upwards [hp] with τ hτ
    rw [Real.norm_of_nonneg (exp_nonneg _)]
    exact exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hτ.le) hz)
  unfold positiveLaplace laplace
  rw [hr]
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun τ => exp_nonneg _)).symm

theorem positiveLaplace_toReal_eq_laplace (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0) {z : ℝ} (hz : 0 ≤ z) :
    (positiveLaplace ρ z).toReal = laplace ρ z := by
  rw [positiveLaplace_eq_ofReal_laplace ρ hneg hzero hz]
  exact ENNReal.toReal_ofReal (integral_nonneg fun τ => exp_nonneg _)

/-- Source-format one-line result: the kernel here is the full Laplace transform
on the measure space, not a supplied decay envelope or a truncated profile. -/
theorem actual_selected_line_integrable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0)
    {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d)
    (hM : inverseMoment ρ (1 + d / 2) < ⊤) (m : ℝ) :
    Integrable (fun q : LoopMomentum =>
      ‖q‖ ^ d * laplace ρ (a ^ 2 * ‖q‖ ^ 2) / (‖q‖ ^ 2 + m ^ 2)) := by
  convert selectedLine_weight_integrable ρ ha hd hM m using 1
  ext q
  unfold selectedLine
  rw [positiveLaplace_toReal_eq_laplace ρ hneg hzero (by positivity)]
  ring

theorem actual_selected_line_integral_le (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0)
    {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d)
    (hM : inverseMoment ρ (1 + d / 2) < ⊤) (m : ℝ) :
    (∫ q : LoopMomentum,
      ‖q‖ ^ d * laplace ρ (a ^ 2 * ‖q‖ ^ 2) / (‖q‖ ^ 2 + m ^ 2)) ≤
      π ^ 2 * Gamma (1 + d / 2) * a ^ (-2 - d) *
        (inverseMoment ρ (1 + d / 2)).toReal := by
  convert selectedLine_integral_le ρ ha hd hM m using 1
  congr 1
  ext q
  unfold selectedLine
  rw [positiveLaplace_toReal_eq_laplace ρ hneg hzero (by positivity)]
  ring

/-- The explicit massless upper bound for a selected line of degree `d`. -/
def lineMomentBound (ρ : Measure ℝ) (a d : ℝ) : ℝ :=
  π ^ 2 * Gamma (1 + d / 2) * a ^ (-2 - d) *
    (inverseMoment ρ (1 + d / 2)).toReal

/-- One highest inverse moment controls every lower nonnegative line degree. -/
theorem selectedLine_integrable_of_highest_moment
    (ρ : Measure ℝ) [IsFiniteMeasure ρ] {a d D : ℝ}
    (ha : 0 < a) (hd : 0 ≤ d) (hdD : d ≤ D)
    (hM : inverseMoment ρ (1 + D / 2) < ⊤) (m : ℝ) :
    Integrable (fun q : LoopMomentum => ‖q‖ ^ d * selectedLine ρ a m q) := by
  apply selectedLine_weight_integrable ρ ha hd _ m
  exact inverseMoment_lower_order_finite ρ (by linarith) (by linarith) hM

/-- A line carrying one polynomial term and its constant term. -/
def selectedWeight (ρ : Measure ℝ) (a m d : ℝ) (q : LoopMomentum) : ℝ :=
  (1 + ‖q‖ ^ d) * selectedLine ρ a m q

theorem selectedWeight_nonneg (ρ : Measure ℝ) (a m d : ℝ) (q : LoopMomentum) :
    0 ≤ selectedWeight ρ a m d q :=
  mul_nonneg (by positivity) (selectedLine_nonneg ρ a m q)

theorem selectedWeight_integrable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {a d D : ℝ} (ha : 0 < a) (hd : 0 ≤ d) (hdD : d ≤ D)
    (hM : inverseMoment ρ (1 + D / 2) < ⊤) (m : ℝ) :
    Integrable (selectedWeight ρ a m d) := by
  have h0 := selectedLine_integrable_of_highest_moment ρ ha (le_refl 0)
    (hd.trans hdD) hM m
  have hd' := selectedLine_integrable_of_highest_moment ρ ha hd hdD hM m
  convert h0.add hd' using 1
  ext q
  simp [selectedWeight, add_mul]

theorem selectedWeight_integral_le (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {a d D : ℝ} (ha : 0 < a) (hd : 0 ≤ d) (hdD : d ≤ D)
    (hM : inverseMoment ρ (1 + D / 2) < ⊤) (m : ℝ) :
    (∫ q, selectedWeight ρ a m d q) ≤
      lineMomentBound ρ a 0 + lineMomentBound ρ a d := by
  have hM0 : inverseMoment ρ (1 + 0 / 2) < ⊤ :=
    inverseMoment_lower_order_finite ρ (by norm_num) (by linarith) hM
  have hMd : inverseMoment ρ (1 + d / 2) < ⊤ :=
    inverseMoment_lower_order_finite ρ (by linarith) (by linarith) hM
  have h0 := selectedLine_weight_integrable ρ ha (le_refl 0) hM0 m
  have hd' := selectedLine_weight_integrable ρ ha hd hMd m
  have he : selectedWeight ρ a m d =
      (fun q => ‖q‖ ^ (0 : ℝ) * selectedLine ρ a m q +
        ‖q‖ ^ d * selectedLine ρ a m q) := by
    ext q
    simp [selectedWeight, add_mul]
  rw [he, integral_add h0 hd']
  exact add_le_add (selectedLine_integral_le ρ ha (le_refl 0) hM0 m)
    (selectedLine_integral_le ρ ha hd hMd m)

/-- Anisotropic selected-line convergence from actual line measures and their
highest required inverse moments. The finite polynomial bound may depend on
all line variables, and the same estimate holds for every external parameter. -/
theorem anisotropic_selected_lines
    {ι A P F : Type*} [Fintype ι] [Fintype A]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ι → Measure ℝ) [∀ j, IsFiniteMeasure (ρ j)]
    (a m D : ι → ℝ) (d : A → ι → ℝ) (c : A → ℝ)
    (ha : ∀ j, 0 < a j)
    (hd : ∀ α j, 0 ≤ d α j) (hdD : ∀ α j, d α j ≤ D j)
    (hc : ∀ α, 0 ≤ c α)
    (hM : ∀ j, inverseMoment (ρ j) (1 + D j / 2) < ⊤)
    (f : P → (ι → LoopMomentum) → F)
    (hf : ∀ p, AEStronglyMeasurable (f p) (Measure.pi fun _ : ι => volume))
    (hb : ∀ p ℓ, ‖f p ℓ‖ ≤ ∑ α, c α *
      ∏ j, selectedWeight (ρ j) (a j) (m j) (d α j) (ℓ j)) :
    ∀ p, Integrable (f p) (Measure.pi fun _ : ι => volume) ∧
      (∫ ℓ, ‖f p ℓ‖ ∂(Measure.pi fun _ : ι => volume)) ≤
        ∑ α, c α * ∏ j,
          (lineMomentBound (ρ j) (a j) 0 + lineMomentBound (ρ j) (a j) (d α j)) := by
  classical
  have hi (α : A) (j : ι) :
      Integrable (selectedWeight (ρ j) (a j) (m j) (d α j)) :=
    selectedWeight_integrable (ρ j) (ha j) (hd α j) (hdD α j) (hM j) (m j)
  have hp (α : A) : Integrable
      (fun ℓ : ι → LoopMomentum => ∏ j,
        selectedWeight (ρ j) (a j) (m j) (d α j) (ℓ j))
      (Measure.pi fun _ : ι => volume) := Integrable.fintype_prod (hi α)
  have hs : Integrable (fun ℓ : ι → LoopMomentum => ∑ α, c α *
      ∏ j, selectedWeight (ρ j) (a j) (m j) (d α j) (ℓ j))
      (Measure.pi fun _ : ι => volume) :=
    integrable_finset_sum _ fun α _ => (hp α).const_mul (c α)
  intro p
  have hfp := hs.mono' (hf p) (Filter.Eventually.of_forall (hb p))
  refine ⟨hfp, ?_⟩
  calc
    (∫ ℓ, ‖f p ℓ‖ ∂(Measure.pi fun _ : ι => volume)) ≤
        ∫ ℓ, (∑ α, c α * ∏ j,
          selectedWeight (ρ j) (a j) (m j) (d α j) (ℓ j))
          ∂(Measure.pi fun _ : ι => volume) :=
      integral_mono_ae hfp.norm hs (Filter.Eventually.of_forall (hb p))
    _ = ∑ α, c α * ∏ j,
        ∫ q, selectedWeight (ρ j) (a j) (m j) (d α j) q := by
      rw [integral_finset_sum _ fun α _ => (hp α).const_mul (c α)]
      apply Finset.sum_congr rfl
      intro α _
      rw [integral_const_mul, integral_fintype_prod_eq_prod]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro α _
      apply mul_le_mul_of_nonneg_left _ (hc α)
      apply Finset.prod_le_prod
      · intro j _
        exact integral_nonneg (selectedWeight_nonneg (ρ j) (a j) (m j) (d α j))
      · intro j _
        exact selectedWeight_integral_le (ρ j) (ha j) (hd α j) (hdD α j) (hM j) (m j)

/-- The nonnegative selected factor is the document's full Laplace factor when
its representing measure is supported on positive depths. -/
theorem selectedWeight_eq_full_laplace (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0) (a m d : ℝ)
    (q : LoopMomentum) :
    selectedWeight ρ a m d q =
      (1 + ‖q‖ ^ d) * laplace ρ (a ^ 2 * ‖q‖ ^ 2) /
        (‖q‖ ^ 2 + m ^ 2) := by
  unfold selectedWeight selectedLine
  rw [positiveLaplace_toReal_eq_laplace ρ hneg hzero (by positivity)]
  ring

/-- Necessity and sufficiency for the actual massless selected factor, with the
separate support and no-atom assumptions of the document made explicit. -/
theorem actual_massless_selected_line_integrable_iff
    (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0)
    {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d) :
    Integrable (fun q : LoopMomentum =>
      ‖q‖ ^ d * laplace ρ (a ^ 2 * ‖q‖ ^ 2) / ‖q‖ ^ 2) ↔
        inverseMoment ρ (1 + d / 2) < ⊤ := by
  have he : (fun q : LoopMomentum =>
      ‖q‖ ^ d * laplace ρ (a ^ 2 * ‖q‖ ^ 2) / ‖q‖ ^ 2) =
      (fun q => ‖q‖ ^ d * selectedLine ρ a 0 q) := by
    ext q
    unfold selectedLine
    rw [positiveLaplace_toReal_eq_laplace ρ hneg hzero (by positivity)]
    simp [mul_div_assoc]
  rw [he]
  exact massless_selectedLine_integrable_iff ρ ha hd

/-- The full extended-valued equality, including divergent inverse moments. -/
theorem actual_massless_selected_line_lintegral
    (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0)
    {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d) :
    (∫⁻ q : LoopMomentum, ENNReal.ofReal
      (‖q‖ ^ d * laplace ρ (a ^ 2 * ‖q‖ ^ 2) / ‖q‖ ^ 2)) =
      ENNReal.ofReal (π ^ 2 * Gamma (1 + d / 2) * a ^ (-2 - d)) *
        inverseMoment ρ (1 + d / 2) := by
  convert massless_selectedLine_lintegral ρ ha hd using 1
  congr 1
  ext q
  unfold selectedLine
  rw [positiveLaplace_toReal_eq_laplace ρ hneg hzero (by positivity)]
  simp [mul_div_assoc]

/-- The affine routing Jacobian is derived from the determinant of the actual
continuous linear equivalence, using Haar measure scaling. -/
theorem routing_integrable
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (e : E ≃L[ℝ] E) (b : E) {g : E → F} (hg : Integrable g μ) :
    Integrable (fun k => g (e k + b)) μ := by
  have hdet : LinearMap.det e.toLinearMap ≠ 0 :=
    e.toLinearEquiv.isUnit_det'.ne_zero
  apply (integrable_map_equiv e.toHomeomorph.toMeasurableEquiv
    (fun y => g (y + b))).mp
  change Integrable (fun y => g (y + b)) (Measure.map e.toLinearMap μ)
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet]
  exact (hg.comp_add_right b).smul_measure ENNReal.ofReal_ne_top

theorem routing_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (e : E ≃L[ℝ] E) (b : E) (g : E → ℝ) :
    (∫ k, g (e k + b) ∂μ) =
      |(LinearMap.det e.toLinearMap)⁻¹| * ∫ y, g y ∂μ := by
  have hdet : LinearMap.det e.toLinearMap ≠ 0 :=
    e.toLinearEquiv.isUnit_det'.ne_zero
  have he := integral_map_equiv (μ := μ) e.toHomeomorph.toMeasurableEquiv
    (fun y => g (y + b))
  change (∫ y, g (y + b) ∂Measure.map e.toLinearMap μ) =
    (∫ k, g (e k + b) ∂μ) at he
  rw [← he]
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul, integral_add_right_eq_self]

/-- Full selected-line convergence in routed variables, with the document's
actual full Laplace factors, anisotropic degree budget, and explicit Jacobian.
No one-line integrability or decay envelope is assumed in this theorem. -/
theorem anisotropic_routed_full_laplace
    {ι A P F : Type*} [Fintype ι] [Fintype A]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ι → Measure ℝ) [∀ j, IsFiniteMeasure (ρ j)]
    (hneg : ∀ j, ρ j (Iio 0) = 0) (hzero : ∀ j, ρ j {0} = 0)
    (a m D : ι → ℝ) (d : A → ι → ℝ) (c : A → ℝ)
    (ha : ∀ j, 0 < a j)
    (hd : ∀ α j, 0 ≤ d α j) (hdD : ∀ α j, d α j ≤ D j)
    (hc : ∀ α, 0 ≤ c α)
    (hM : ∀ j, inverseMoment (ρ j) (1 + D j / 2) < ⊤)
    (e : (ι → LoopMomentum) ≃L[ℝ] (ι → LoopMomentum))
    (b : P → (ι → LoopMomentum))
    (f : P → (ι → LoopMomentum) → F)
    (hf : ∀ p, AEStronglyMeasurable (f p) (Measure.pi fun _ : ι => volume))
    (hb : ∀ p ℓ, ‖f p ℓ‖ ≤ ∑ α, c α * ∏ j,
      ((1 + ‖ℓ j‖ ^ d α j) * laplace (ρ j) ((a j) ^ 2 * ‖ℓ j‖ ^ 2) /
        (‖ℓ j‖ ^ 2 + (m j) ^ 2))) :
    ∀ p, Integrable (fun k => f p (e k + b p)) (Measure.pi fun _ : ι => volume) ∧
      (∫ k, ‖f p (e k + b p)‖ ∂(Measure.pi fun _ : ι => volume)) ≤
        |(LinearMap.det e.toLinearMap)⁻¹| *
          ∑ α, c α * ∏ j,
            (lineMomentBound (ρ j) (a j) 0 +
              lineMomentBound (ρ j) (a j) (d α j)) := by
  have hb' : ∀ p ℓ, ‖f p ℓ‖ ≤ ∑ α, c α *
      ∏ j, selectedWeight (ρ j) (a j) (m j) (d α j) (ℓ j) := by
    intro p ℓ
    simpa only [selectedWeight_eq_full_laplace _ (hneg _) (hzero _)] using hb p ℓ
  have h := anisotropic_selected_lines ρ a m D d c ha hd hdD hc hM f hf hb'
  intro p
  refine ⟨routing_integrable (Measure.pi fun _ : ι => volume) e (b p) (h p).1, ?_⟩
  rw [routing_integral (Measure.pi fun _ : ι => volume) e (b p) (fun ℓ => ‖f p ℓ‖)]
  exact mul_le_mul_of_nonneg_left (h p).2 (abs_nonneg _)

/-- The four real coordinates give the fourth power of the selected routing
matrix determinant. This is the Kronecker matrix used in the document. -/
theorem four_dimensional_routing_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) :
    Matrix.det (Matrix.kronecker C (1 : Matrix (Fin 4) (Fin 4) ℝ)) =
      Matrix.det C ^ 4 := by
  rw [Matrix.kronecker, Matrix.det_kronecker]
  simp

/-- The Jacobian of a routing represented by `C ⊗ I₄` has the factor appearing
in the selected-line comparison bound. -/
theorem four_dimensional_routing_jacobian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) :
    |(Matrix.det (Matrix.kronecker C (1 : Matrix (Fin 4) (Fin 4) ℝ)))⁻¹| =
      |Matrix.det C| ^ (-4 : ℝ) := by
  rw [four_dimensional_routing_det, abs_inv, abs_pow]
  rw [Real.rpow_neg (abs_nonneg _)]
  norm_num

/-- The Fourier-normalized selected-line theorem for a routing whose coefficient
matrix is `C ⊗ I₄`. A basis records that coefficient representation explicitly;
the determinant and Fourier factors are derived, rather than assumed. -/
theorem optimized_selected_lines
    {ι A P F : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ι → Measure ℝ) [∀ j, IsFiniteMeasure (ρ j)]
    (hneg : ∀ j, ρ j (Iio 0) = 0) (hzero : ∀ j, ρ j {0} = 0)
    (a m D : ι → ℝ) (d : A → ι → ℝ) (c : A → ℝ)
    (ha : ∀ j, 0 < a j)
    (hd : ∀ α j, 0 ≤ d α j) (hdD : ∀ α j, d α j ≤ D j)
    (hc : ∀ α, 0 ≤ c α)
    (hM : ∀ j, inverseMoment (ρ j) (1 + D j / 2) < ⊤)
    (C : Matrix ι ι ℝ)
    (B : Module.Basis (ι × Fin 4) ℝ (ι → LoopMomentum))
    (e : (ι → LoopMomentum) ≃L[ℝ] (ι → LoopMomentum))
    (hroute : LinearMap.toMatrix B B e.toLinearMap =
      Matrix.kronecker C (1 : Matrix (Fin 4) (Fin 4) ℝ))
    (b : P → (ι → LoopMomentum))
    (f : P → (ι → LoopMomentum) → F)
    (hf : ∀ p, AEStronglyMeasurable (f p) (Measure.pi fun _ : ι => volume))
    (hb : ∀ p ℓ, ‖f p ℓ‖ ≤ ∑ α, c α * ∏ j,
      ((1 + ‖ℓ j‖ ^ d α j) * laplace (ρ j) ((a j) ^ 2 * ‖ℓ j‖ ^ 2) /
        (‖ℓ j‖ ^ 2 + (m j) ^ 2))) :
    ∀ p, Integrable (fun k => f p (e k + b p)) (Measure.pi fun _ : ι => volume) ∧
      (∫ k, ‖f p (e k + b p)‖ / (2 * π) ^ (4 * Fintype.card ι)
        ∂(Measure.pi fun _ : ι => volume)) ≤
        |Matrix.det C| ^ (-4 : ℝ) / (2 * π) ^ (4 * Fintype.card ι) *
          ∑ α, c α * ∏ j,
            (lineMomentBound (ρ j) (a j) 0 +
              lineMomentBound (ρ j) (a j) (d α j)) := by
  have h := anisotropic_routed_full_laplace ρ hneg hzero a m D d c ha hd hdD hc hM
    e b f hf hb
  have hdet : LinearMap.det e.toLinearMap =
      Matrix.det (Matrix.kronecker C (1 : Matrix (Fin 4) (Fin 4) ℝ)) := by
    rw [← LinearMap.det_toMatrix B, hroute]
  have hJ : |(LinearMap.det e.toLinearMap)⁻¹| = |Matrix.det C| ^ (-4 : ℝ) := by
    rw [hdet, four_dimensional_routing_jacobian]
  intro p
  refine ⟨(h p).1, ?_⟩
  have hbound := (h p).2
  rw [hJ] at hbound
  rw [integral_div]
  calc
    _ ≤ (|Matrix.det C| ^ (-4 : ℝ) * ∑ α, c α * ∏ j,
        (lineMomentBound (ρ j) (a j) 0 +
          lineMomentBound (ρ j) (a j) (d α j))) /
            (2 * π) ^ (4 * Fintype.card ι) :=
      div_le_div_of_nonneg_right hbound (by positivity)
    _ = _ := by ring

/-- A bare full-rank selected routing constructs the actual continuous linear
equivalence required above. -/
theorem exists_four_dimensional_routing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Module.Basis (ι × Fin 4) ℝ (ι → LoopMomentum))
    (C : Matrix ι ι ℝ) (hC : Matrix.det C ≠ 0) :
    ∃ e : (ι → LoopMomentum) ≃L[ℝ] (ι → LoopMomentum),
      LinearMap.toMatrix B B e.toLinearMap =
        Matrix.kronecker C (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  let A := Matrix.kronecker C (1 : Matrix (Fin 4) (Fin 4) ℝ)
  have hA : IsUnit (Matrix.det A) := by
    apply isUnit_iff_ne_zero.mpr
    change Matrix.det (Matrix.kronecker C (1 : Matrix (Fin 4) (Fin 4) ℝ)) ≠ 0
    rw [four_dimensional_routing_det]
    exact pow_ne_zero _ hC
  let e := (Matrix.toLinearEquiv B A hA).toContinuousLinearEquiv
  refine ⟨e, ?_⟩
  change LinearMap.toMatrix B B (Matrix.toLin B B A) = A
  exact LinearMap.toMatrix_toLin B B A

/-- Canonical line-by-coordinate basis for four-dimensional loop momenta. -/
def loopProductBasis (ι : Type*) [Fintype ι] :
    Module.Basis (ι × Fin 4) ℝ (ι → LoopMomentum) :=
  (Pi.basis fun _ : ι => (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis).reindex
    (Equiv.sigmaEquivProd _ _)

theorem loopProductBasis_repr {ι : Type*} [Fintype ι]
    (k : ι → LoopMomentum) (i : ι) (ν : Fin 4) :
    (loopProductBasis ι).repr k (i, ν) = k i ν := by
  simp [loopProductBasis, Pi.basis_repr,
    EuclideanSpace.basisFun_repr]

theorem exists_selected_routing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : Matrix.det C ≠ 0) :
    ∃ e : (ι → LoopMomentum) ≃L[ℝ] (ι → LoopMomentum),
      LinearMap.toMatrix (loopProductBasis ι) (loopProductBasis ι) e.toLinearMap =
        Matrix.kronecker C (1 : Matrix (Fin 4) (Fin 4) ℝ) :=
  exists_four_dimensional_routing (loopProductBasis ι) C hC

/-- Multiplying the source's complete numerator/unselected-line envelope by
the actual selected comparison factors gives the anisotropic majorant. -/
theorem complete_envelope_selected_bound
    {ι A F : Type*} [Fintype ι] [Fintype A]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ι → Measure ℝ) (a m : ι → ℝ) (d : A → ι → ℝ) (c : A → ℝ)
    (ℓ : ι → LoopMomentum) (remaining : F)
    (hb : ‖remaining‖ ≤ ∑ α, c α * ∏ j, (1 + ‖ℓ j‖ ^ d α j)) :
    ‖(∏ j, selectedLine (ρ j) (a j) (m j) (ℓ j)) • remaining‖ ≤
      ∑ α, c α * ∏ j, selectedWeight (ρ j) (a j) (m j) (d α j) (ℓ j) := by
  classical
  have hn : 0 ≤ ∏ j, selectedLine (ρ j) (a j) (m j) (ℓ j) :=
    Finset.prod_nonneg fun j _ => selectedLine_nonneg (ρ j) (a j) (m j) (ℓ j)
  rw [norm_smul, Real.norm_of_nonneg hn]
  calc
    _ ≤ (∏ j, selectedLine (ρ j) (a j) (m j) (ℓ j)) *
        ∑ α, c α * ∏ j, (1 + ‖ℓ j‖ ^ d α j) :=
      mul_le_mul_of_nonneg_left hb hn
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro α _
      simp_rw [selectedWeight, Finset.prod_mul_distrib]
      ring

/-- The canonical Kronecker representation is precisely the selected routing
`ℓᵢ = ∑ⱼ Cᵢⱼ kⱼ` on each of the four real coordinates. -/
theorem selected_routing_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ)
    (e : (ι → LoopMomentum) ≃L[ℝ] (ι → LoopMomentum))
    (hroute : LinearMap.toMatrix (loopProductBasis ι) (loopProductBasis ι)
      e.toLinearMap = Matrix.kronecker C (1 : Matrix (Fin 4) (Fin 4) ℝ))
    (k : ι → LoopMomentum) (i : ι) (ν : Fin 4) :
    e k i ν = ∑ j, C i j * k j ν := by
  have h := e.toLinearMap.toMatrix_mulVec_repr (loopProductBasis ι) (loopProductBasis ι) k
  rw [hroute] at h
  have hi := congrFun h (i, ν)
  simpa [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, loopProductBasis_repr,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply] using hi.symm

end UV
