import UV.ContinueHeatMaxwellSignAngular
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! The straight-chord shifts in genuine Euclidean unit directions. -/

noncomputable section

namespace UV.HeatMaxwell

open UV.RelativeSoft UV.SectorPlane MeasureTheory
open scoped RealInnerProductSpace

def heatSymbol (k : EuclideanPlaneMomentum) : EuclideanPlaneMomentum :=
  Real.exp (-‖k‖ ^ 2) • k

def heatShiftFactor (j s : ℝ) : ℝ := Real.exp (-2 * j * s - s ^ 2)

theorem heatSymbol_two_unit_shifts (k : EuclideanPlaneMomentum) (s t : ℝ) :
    heatSymbol (k + s • softLongitudinal.val + t • softTransverse.val) =
      (Real.exp (-‖k‖ ^ 2) * heatShiftFactor ⟪k, softLongitudinal.val⟫ s *
        heatShiftFactor ⟪k, softTransverse.val⟫ t) •
        (k + s • softLongitudinal.val + t • softTransverse.val) := by
  have h := heatGram_eq_inner k (1, s, t) (1, s, t)
  simp only [heatCarrierVector, one_smul, real_inner_self_eq_norm_sq, heatGram] at h
  unfold heatSymbol heatShiftFactor
  rw [h, ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

theorem heatShiftFactor_hasDerivAt (j s : ℝ) :
    HasDerivAt (heatShiftFactor j) ((-2 * j - 2 * s) * heatShiftFactor j s) s := by
  have h := (((hasDerivAt_id s).const_mul (-2 * j)).sub (hasDerivAt_pow 2 s)).exp
  convert h using 1
  simp [heatShiftFactor]
  ring

private theorem heatShiftFactor_second_general (j s : ℝ) :
    HasDerivAt (deriv (heatShiftFactor j))
      (((-2 * j - 2 * s) ^ 2 - 2) * heatShiftFactor j s) s := by
  have he : deriv (heatShiftFactor j) = fun v => (-2 * j - 2 * v) * heatShiftFactor j v :=
    funext fun v => (heatShiftFactor_hasDerivAt j v).deriv
  rw [he]
  have hl := ((hasDerivAt_id s).const_mul 2).const_sub (-2 * j)
  convert hl.mul (heatShiftFactor_hasDerivAt j s) using 1
  simp
  ring

theorem heatShiftFactor_at_zero (j : ℝ) : heatShiftFactor j 0 = 1 := by
  simp [heatShiftFactor]

theorem heatShiftFactor_first (j : ℝ) : deriv (heatShiftFactor j) 0 = -2 * j := by
  simp [(heatShiftFactor_hasDerivAt j 0).deriv, heatShiftFactor_at_zero]

theorem heatShiftFactor_second (j : ℝ) :
    deriv (deriv (heatShiftFactor j)) 0 = 4 * j ^ 2 - 2 := by
  rw [(heatShiftFactor_second_general j 0).deriv, heatShiftFactor_at_zero]
  ring

private theorem heatShiftVector_first (j : ℝ) (v w : EuclideanPlaneMomentum) :
    deriv (fun s => heatShiftFactor j s • (v + s • w)) 0 = (-2 * j) • v + w := by
  have h := (heatShiftFactor_hasDerivAt j 0).smul
    (((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v)
  change HasDerivAt (fun s : ℝ => heatShiftFactor j s • (v + s • w)) _ 0 at h
  simpa [heatShiftFactor_at_zero, add_comm] using h.deriv

private theorem heatShiftVector_second (j : ℝ) (v w : EuclideanPlaneMomentum) :
    deriv (deriv (fun s => heatShiftFactor j s • (v + s • w))) 0 =
      (4 * j ^ 2 - 2) • v + (-4 * j) • w := by
  have he : deriv (fun s => heatShiftFactor j s • (v + s • w)) =
      fun s => deriv (heatShiftFactor j) s • (v + s • w) + heatShiftFactor j s • w := by
    funext s
    have h := (heatShiftFactor_hasDerivAt j s).smul
      (((hasDerivAt_id s).smul_const w).const_add v)
    change HasDerivAt (fun t : ℝ => heatShiftFactor j t • (v + t • w)) _ s at h
    simpa [(heatShiftFactor_hasDerivAt j s).deriv, add_comm, add_left_comm] using h.deriv
  rw [he]
  have hd := ((heatShiftFactor_second_general j 0).smul
    (((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v)).add
      ((heatShiftFactor_hasDerivAt j 0).smul_const w)
  change HasDerivAt (fun s : ℝ => deriv (heatShiftFactor j) s • (v + s • w) +
    heatShiftFactor j s • w) _ 0 at hd
  rw [hd.deriv]
  simp only [heatShiftFactor_at_zero, heatShiftFactor_first, mul_zero, sub_zero, mul_one, id_eq,
    zero_smul, add_zero, one_smul]
  module

/-- The actual first and second longitudinal derivatives of the heat symbol. -/
theorem heatSymbol_longitudinal_derivatives (k : EuclideanPlaneMomentum) :
    let u := ‖k‖ ^ 2
    let j := ⟪k, softLongitudinal.val⟫
    let f := fun s : ℝ => heatSymbol (k + s • softLongitudinal.val)
    deriv f 0 = Real.exp (-u) • heatCarrierVector k (heatH₁ j) ∧
      deriv (deriv f) 0 = Real.exp (-u) • heatCarrierVector k (heatH₁₁ j) := by
  dsimp only
  let j := ⟪k, softLongitudinal.val⟫
  let c := Real.exp (-‖k‖ ^ 2)
  have hf : (fun s : ℝ => heatSymbol (k + s • softLongitudinal.val)) =
      fun s => heatShiftFactor j s • (c • k + s • (c • softLongitudinal.val)) := by
    funext s
    have h := heatSymbol_two_unit_shifts k s 0
    simp only [zero_smul, add_zero, heatShiftFactor_at_zero, mul_one] at h
    rw [h]
    simp only [j, c]
    module
  rw [hf, heatShiftVector_first, heatShiftVector_second]
  simp only [heatCarrierVector, heatH₁, heatH₁₁, one_smul, zero_smul, add_zero, smul_add,
    smul_smul, j, c]
  constructor <;> module

/-- Transverse derivatives at an arbitrary longitudinal chord shift. -/
theorem heatSymbol_transverse_derivatives (k : EuclideanPlaneMomentum) (s : ℝ) :
    let j := ⟪k, softTransverse.val⟫
    let v := k + s • softLongitudinal.val
    let c := Real.exp (-‖k‖ ^ 2) * heatShiftFactor ⟪k, softLongitudinal.val⟫ s
    let f := fun t : ℝ => heatSymbol (v + t • softTransverse.val)
    deriv f 0 = c • ((-2 * j) • v + softTransverse.val) ∧
      deriv (deriv f) 0 = c • ((4 * j ^ 2 - 2) • v + (-4 * j) • softTransverse.val) := by
  dsimp only
  let j := ⟪k, softTransverse.val⟫
  let v := k + s • softLongitudinal.val
  let c := Real.exp (-‖k‖ ^ 2) * heatShiftFactor ⟪k, softLongitudinal.val⟫ s
  have hf : (fun t : ℝ => heatSymbol (v + t • softTransverse.val)) =
      fun t => heatShiftFactor j t • (c • v + t • (c • softTransverse.val)) := by
    funext t
    have h := heatSymbol_two_unit_shifts k s t
    change heatSymbol (v + t • softTransverse.val) =
      (c * heatShiftFactor j t) • (v + t • softTransverse.val) at h
    rw [h]
    module
  change deriv (fun t : ℝ => heatSymbol (v + t • softTransverse.val)) 0 = _ ∧
    deriv (deriv (fun t : ℝ => heatSymbol (v + t • softTransverse.val))) 0 = _
  rw [hf, heatShiftVector_first, heatShiftVector_second]
  constructor <;> module

/-- The mixed derivatives used by the centered first mark and direct contact. -/
theorem heatSymbol_mixed_mark_derivatives (k : EuclideanPlaneMomentum) :
    let j := ⟪k, softLongitudinal.val⟫
    let h := ⟪k, softTransverse.val⟫
    let f := fun (s t : ℝ) => heatSymbol (k + s • softLongitudinal.val + t • softTransverse.val)
    deriv (deriv (fun s => deriv (f s) 0)) 0 =
        Real.exp (-‖k‖ ^ 2) • heatCarrierVector k (heatH₁₁₂ j h) ∧
      deriv (deriv (fun s => deriv (deriv (f s)) 0)) 0 =
        Real.exp (-‖k‖ ^ 2) • heatCarrierVector k (heatH₁₁₂₂ j h) := by
  dsimp only
  let j := ⟪k, softLongitudinal.val⟫
  let h := ⟪k, softTransverse.val⟫
  let c := Real.exp (-‖k‖ ^ 2)
  have hf : (fun s : ℝ => deriv (fun t : ℝ =>
        heatSymbol (k + s • softLongitudinal.val + t • softTransverse.val)) 0) =
      fun s => heatShiftFactor j s • (c • ((-2 * h) • k + softTransverse.val) +
        s • (c • ((-2 * h) • softLongitudinal.val))) := by
    funext s
    rw [(heatSymbol_transverse_derivatives k s).1]
    change (c * heatShiftFactor j s) • ((-2 * h) • (k + s • softLongitudinal.val) +
      softTransverse.val) = _
    module
  have hg : (fun s : ℝ => deriv (deriv (fun t : ℝ =>
        heatSymbol (k + s • softLongitudinal.val + t • softTransverse.val))) 0) =
      fun s => heatShiftFactor j s • (c • ((4 * h ^ 2 - 2) • k + (-4 * h) • softTransverse.val) +
        s • (c • ((4 * h ^ 2 - 2) • softLongitudinal.val))) := by
    funext s
    rw [(heatSymbol_transverse_derivatives k s).2]
    change (c * heatShiftFactor j s) • ((4 * h ^ 2 - 2) • (k + s • softLongitudinal.val) +
      (-4 * h) • softTransverse.val) = _
    module
  rw [hf, hg, heatShiftVector_second, heatShiftVector_second]
  simp only [heatCarrierVector, heatH₁₁₂, heatH₁₁₂₂, j, h, c]
  constructor <;> module

/-- The exact second moment of the centered first-mark chord parameter. -/
theorem heatFirstMark_parameter_moment :
    (∫ s in (-1/2 : ℝ)..(1/2 : ℝ), s ^ 2) = 1 / 12 := by
  rw [integral_pow]
  norm_num

private theorem heatSecondMark_inner_moment (s : ℝ) :
    (∫ v in (0 : ℝ)..1, (s - v) ^ 2) = s ^ 2 - s + 1 / 3 := by
  have he (v : ℝ) : (s - v) ^ 2 = s ^ 2 - (2 * s) * v + v ^ 2 := by ring
  simp_rw [he]
  have ha : IntervalIntegrable (fun _ : ℝ => s ^ 2) volume 0 1 :=
    continuous_const.intervalIntegrable _ _
  have hb : IntervalIntegrable (fun v : ℝ => (2 * s) * v) volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hc : IntervalIntegrable (fun v : ℝ => v ^ 2) volume 0 1 :=
    (continuous_id.pow _).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (ha.sub hb) hc, intervalIntegral.integral_sub ha hb,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id, integral_pow]
  norm_num
  ring

/-- The second moment of the actual difference of the two contact parameters. -/
theorem heatSecondMark_parameter_moment :
    (∫ s in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, (s - v) ^ 2) = 1 / 6 := by
  simp_rw [heatSecondMark_inner_moment]
  have ha : IntervalIntegrable (fun s : ℝ => s ^ 2) volume 0 1 :=
    (continuous_id.pow _).intervalIntegrable _ _
  have hb : IntervalIntegrable (fun s : ℝ => s) volume 0 1 :=
    continuous_id.intervalIntegrable _ _
  have hc : IntervalIntegrable (fun _ : ℝ => (1/3 : ℝ)) volume 0 1 :=
    continuous_const.intervalIntegrable _ _
  rw [intervalIntegral.integral_add (ha.sub hb) hc, intervalIntegral.integral_sub ha hb,
    intervalIntegral.integral_const, integral_id, integral_pow]
  norm_num

end UV.HeatMaxwell
