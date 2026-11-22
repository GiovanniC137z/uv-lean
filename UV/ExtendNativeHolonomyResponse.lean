import UV.Frullani
import UV.NextNativeBridgeResponse
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The nonconstant normal holonomy comparison on one fixed sector plane.
The same (q)-independent contact is kept in both Hessians before taking
their difference. The temperature and loop momentum are real Euclidean
variables. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace UV.ExtendNativeHolonomy

structure NormalCircle (E : Type) [NormedAddCommGroup E] where
  plane : UV.SectorPlane.Plane E
  evolution : UV.SectorPlane.Evolution
  mass : ℝ
  mass_pos : 0 < mass
  length : ℝ
  length_pos : 0 < length

variable {E : Type} [NormedAddCommGroup E]

def modeNumber (C : NormalCircle E) (n : ℤ) : ℝ := 2 * Real.pi * n / C.length

def curvedFeynmanWidth (q : UV.ScalarMomentum) (u : ℝ) : ℝ :=
  u * (1 - u) * ‖q‖ ^ 2

theorem curvedFeynmanWidth_nonneg (q : UV.ScalarMomentum) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ curvedFeynmanWidth q u :=
  mul_nonneg (mul_nonneg hu.1 (sub_nonneg.mpr hu.2)) (sq_nonneg _)

private theorem curvedFeynmanWidth_le (q : UV.ScalarMomentum) (u : ℝ) :
    curvedFeynmanWidth q u ≤ ‖q‖ ^ 2 := by
  unfold curvedFeynmanWidth
  have h₁ : u * (1 - u) ≤ 1 := by nlinarith [sq_nonneg (u - 1 / 2)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h₁ (sq_nonneg ‖q‖)

theorem integral_curvedFeynmanWidth (q : UV.ScalarMomentum) :
    (∫ u in 0..1, curvedFeynmanWidth q u) = ‖q‖ ^ 2 / 6 := by
  unfold curvedFeynmanWidth
  rw [intervalIntegral.integral_mul_const]
  have he : (fun u : ℝ => u * (1 - u)) = fun u => u - u ^ 2 := by
    funext u; ring
  rw [he, intervalIntegral.integral_sub (f := fun u : ℝ => u) (g := fun u : ℝ => u ^ 2)
    (continuous_id.intervalIntegrable _ _) ((continuous_id.pow 2).intervalIntegrable _ _)]
  rw [integral_id, integral_pow]
  norm_num
  ring

def holonomyFactor (C : NormalCircle E) : ℝ := 4 / (C.length ^ 2 * (4 * Real.pi) ^ 2)

def responseModeProper (C : NormalCircle E) (q : UV.ScalarMomentum) (n : ℤ) : ℝ :=
  holonomyFactor C * modeNumber C n ^ 2 * ∫ u in 0..1,
    ∫ t in Ioi (0 : ℝ), UV.frullaniIntegrand (C.mass ^ 2 + modeNumber C n ^ 2)
      (curvedFeynmanWidth q u) t

def responseModeLog (C : NormalCircle E) (q : UV.ScalarMomentum) (X : ℝ) : ℝ :=
  holonomyFactor C * X *
    ∫ u in 0..1, Real.log (1 + curvedFeynmanWidth q u / (C.mass ^ 2 + X))

theorem responseMode_proper_eq_log (C : NormalCircle E) (q : UV.ScalarMomentum) (n : ℤ) :
    responseModeProper C q n = responseModeLog C q (modeNumber C n ^ 2) := by
  unfold responseModeProper responseModeLog
  congr 1
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  exact UV.frullani_integral
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos C.mass_pos) (sq_nonneg _))
    (curvedFeynmanWidth_nonneg q ⟨hu.1.le, hu.2⟩)

private theorem log_bounds {x : ℝ} (hx : 0 ≤ x) :
    x / (1 + x) ≤ Real.log (1 + x) ∧ Real.log (1 + x) ≤ x := by
  constructor
  · apply le_trans _ (Real.le_log_one_add_of_nonneg hx)
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [sq_nonneg x]
  · have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + x)
    linarith

private theorem response_log_bounds (C : NormalCircle E) (q : UV.ScalarMomentum) {X : ℝ}
    (hX : 0 ≤ X) :
    (holonomyFactor C * (‖q‖ ^ 2 / 6)) * (X / (C.mass ^ 2 + ‖q‖ ^ 2 + X)) ≤
      responseModeLog C q X ∧
      responseModeLog C q X ≤ holonomyFactor C * (‖q‖ ^ 2 / 6) := by
  let A := C.mass ^ 2 + X
  have hA : 0 < A := add_pos_of_pos_of_nonneg (sq_pos_of_pos C.mass_pos) hX
  have hF : 0 ≤ holonomyFactor C := by unfold holonomyFactor; positivity
  have hv : Continuous (curvedFeynmanWidth q) := by unfold curvedFeynmanWidth; fun_prop
  have hlog : IntervalIntegrable (fun u => Real.log (1 + curvedFeynmanWidth q u / A)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    apply (continuousOn_const.add ((hv.div_const A).continuousOn)).log
    intro u hu
    exact (by linarith [div_nonneg (curvedFeynmanWidth_nonneg q hu) hA.le] :
      0 < 1 + curvedFeynmanWidth q u / A).ne'
  have hiLow := (hv.div_const (A + ‖q‖ ^ 2)).intervalIntegrable (μ := volume) 0 1
  have hiHigh := (hv.div_const A).intervalIntegrable (μ := volume) 0 1
  have hl := intervalIntegral.integral_mono_on zero_le_one hiLow hlog
    (fun u hu => by
      have hb := curvedFeynmanWidth_nonneg q hu
      have hs := curvedFeynmanWidth_le q u
      calc
        _ ≤ curvedFeynmanWidth q u / (A + curvedFeynmanWidth q u) :=
          div_le_div_of_nonneg_left hb (by positivity) (add_le_add_left hs A)
        _ = (curvedFeynmanWidth q u / A) / (1 + curvedFeynmanWidth q u / A) := by
          field_simp [hA.ne', (add_pos_of_pos_of_nonneg hA hb).ne']
        _ ≤ _ := (log_bounds (div_nonneg hb hA.le)).1)
  have hh := intervalIntegral.integral_mono_on zero_le_one hlog hiHigh
    (fun u hu => (log_bounds (div_nonneg (curvedFeynmanWidth_nonneg q hu) hA.le)).2)
  rw [intervalIntegral.integral_div, integral_curvedFeynmanWidth] at hl hh
  have hl' := mul_le_mul_of_nonneg_left hl (mul_nonneg hF hX)
  have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg hF hX)
  unfold responseModeLog
  constructor
  · convert hl' using 1
    dsimp [A]
    ring
  · apply hh'.trans
    have ht : X / A ≤ 1 := (div_le_iff₀ hA).2 (by dsimp [A]; linarith [sq_nonneg C.mass])
    calc
      holonomyFactor C * X * (‖q‖ ^ 2 / 6 / A) =
          (holonomyFactor C * (‖q‖ ^ 2 / 6)) * (X / A) := by ring
      _ ≤ holonomyFactor C * (‖q‖ ^ 2 / 6) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left ht (by positivity)

theorem response_modeLog_tendsto (C : NormalCircle E) (q : UV.ScalarMomentum) :
    Tendsto (responseModeLog C q) atTop
      (𝓝 (‖q‖ ^ 2 / (24 * Real.pi ^ 2 * C.length ^ 2))) := by
  let A := C.mass ^ 2 + ‖q‖ ^ 2
  have hratio : Tendsto (fun X : ℝ => X / (A + X)) atTop (𝓝 1) := by
    have ht : Tendsto (fun X : ℝ => (1 + A * X⁻¹)⁻¹) atTop (𝓝 1) := by
      have h := (tendsto_inv_atTop_zero.const_mul A).const_add 1
      simpa only [mul_zero, add_zero, inv_one] using h.inv₀ (by norm_num : (1 + A * 0) ≠ 0)
    refine ht.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have he : 1 + A * X⁻¹ = (A + X) / X := by
      field_simp [hX.ne']
      ring
    rw [he, inv_div]
  have hlimit := hratio.const_mul (holonomyFactor C * (‖q‖ ^ 2 / 6))
  have hT : Tendsto (responseModeLog C q) atTop (𝓝 (holonomyFactor C * (‖q‖ ^ 2 / 6))) := by
    have hlim : Tendsto (fun X : ℝ => (holonomyFactor C * (‖q‖ ^ 2 / 6)) *
      (X / (A + X))) atTop (𝓝 (holonomyFactor C * (‖q‖ ^ 2 / 6))) := by
      simpa only [mul_one] using hlimit
    refine hlim.squeeze' (g := _) (f := responseModeLog C q)
      (h := fun _ => holonomyFactor C * (‖q‖ ^ 2 / 6)) tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
      exact (response_log_bounds C q hX).1
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
      exact (response_log_bounds C q hX).2
  convert hT using 2
  unfold holonomyFactor
  ring

theorem response_modeProper_tendsto_nat (C : NormalCircle E) (q : UV.ScalarMomentum) :
    Tendsto (fun n : ℕ => responseModeProper C q (n : ℤ)) atTop
      (𝓝 (‖q‖ ^ 2 / (24 * Real.pi ^ 2 * C.length ^ 2))) := by
  have hc : 0 < 2 * Real.pi / C.length := div_pos (mul_pos two_pos Real.pi_pos) C.length_pos
  have hint : Tendsto (fun n : ℕ => modeNumber C (n : ℤ)) atTop atTop := by
    have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hc
    convert ht using 1
    funext n
    unfold modeNumber
    push_cast
    ring
  have hs := hint.atTop_mul_atTop₀ hint
  have ht := (response_modeLog_tendsto C q).comp hs
  simpa only [Function.comp_def, responseMode_proper_eq_log, pow_two] using ht

theorem response_comparison_not_summable (C : NormalCircle E) {q : UV.ScalarMomentum} (hq : q ≠ 0) :
    ¬ Summable (responseModeProper C q) := by
  intro h
  have hn := (summable_int_iff_summable_nat_and_neg.mp h).1
  have he := tendsto_nhds_unique (response_modeProper_tendsto_nat C q) hn.tendsto_atTop_zero
  have hp : 0 < ‖q‖ ^ 2 / (24 * Real.pi ^ 2 * C.length ^ 2) :=
    div_pos (sq_pos_of_pos (norm_pos_iff.mpr hq))
      (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos Real.pi_pos)) (sq_pos_of_pos C.length_pos))
  exact hp.ne' he

end UV.ExtendNativeHolonomy
