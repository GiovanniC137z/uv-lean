import UV.GlobalConvergence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The literal massless power-law selected factors in the two-loop example.
Each line uses the Euclidean norm on R^4 and ordinary Lebesgue volume.
Fourier normalization is inserted only in the final two-line weight. -/

noncomputable section
open MeasureTheory Set Real Filter Metric
open scoped Topology

namespace UV

def powerSelectedLine (ν d : ℕ) (q : LoopMomentum) : ℝ :=
  ‖q‖ ^ d / (‖q‖ ^ 2 * (1 + ‖q‖ ^ 2) ^ ν)

theorem powerSelectedLine_nonneg (ν d : ℕ) (q : LoopMomentum) :
    0 ≤ powerSelectedLine ν d q := by unfold powerSelectedLine; positivity

theorem powerSelectedLine_measurable (ν d : ℕ) : Measurable (powerSelectedLine ν d) := by
  unfold powerSelectedLine
  fun_prop

/-- Elementary radial base moments, with a convergent primitive at infinity. -/
def powerRadialBase (n : ℕ) (r : ℝ) : ℝ := r / (1 + r ^ 2) ^ (n + 2)

def powerRadialPrimitive (n : ℕ) (r : ℝ) : ℝ :=
  -((1 + r ^ 2)⁻¹ ^ (n + 1)) / (2 * ((n + 1 : ℕ) : ℝ))

theorem powerRadialPrimitive_hasDerivAt (n : ℕ) (r : ℝ) :
    HasDerivAt (powerRadialPrimitive n) (powerRadialBase n r) r := by
  have hb : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * r) r := by
    simpa using ((hasDerivAt_id r).pow 2).const_add 1
  have hbase : (1 + r ^ 2) ≠ 0 := by positivity
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h := (((hb.inv hbase).pow (n + 1)).neg).div_const (2 * ((n + 1 : ℕ) : ℝ))
  convert h using 1
  dsimp only [powerRadialBase]
  simp only [Nat.add_sub_cancel, Pi.inv_apply, inv_pow, pow_succ]
  field_simp

theorem powerRadialPrimitive_tendsto_zero (n : ℕ) :
    Tendsto (powerRadialPrimitive n) atTop (𝓝 0) := by
  have hb : Tendsto (fun r : ℝ => 1 + r ^ 2) atTop atTop :=
    tendsto_const_nhds.add_atTop (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))
  have hi := tendsto_inv_atTop_zero.comp hb
  simpa only [powerRadialPrimitive, zero_pow (by omega : n + 1 ≠ 0), neg_zero, zero_div] using
    ((hi.pow (n + 1)).neg.div_const (2 * ((n + 1 : ℕ) : ℝ)))

theorem powerRadialBase_integrable (n : ℕ) : IntegrableOn (powerRadialBase n) (Ioi 0) := by
  apply integrableOn_Ioi_deriv_of_nonneg'
    (fun r _ => powerRadialPrimitive_hasDerivAt n r) _ (powerRadialPrimitive_tendsto_zero n)
  intro r hr
  exact div_nonneg hr.le (by positivity)

theorem powerRadialBase_integral (n : ℕ) :
    (∫ r : ℝ in Ioi 0, powerRadialBase n r) = 1 / (2 * ((n + 1 : ℕ) : ℝ)) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun r _ => powerRadialPrimitive_hasDerivAt n r)
    (fun r hr => show 0 ≤ powerRadialBase n r from div_nonneg hr.le (by positivity))
    (powerRadialPrimitive_tendsto_zero n)
  simpa only [powerRadialPrimitive, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero,
    inv_one, one_pow, zero_sub, neg_div, neg_neg] using h

theorem powerSelectedLine_integrable_iff_radial (ν d : ℕ) :
    Integrable (powerSelectedLine ν d) ↔
      IntegrableOn (fun r : ℝ => r ^ (d + 1) / (1 + r ^ 2) ^ ν) (Ioi 0) := by
  unfold powerSelectedLine
  rw [integrable_fun_norm_addHaar (E := LoopMomentum) volume
    (f := fun r : ℝ => r ^ d / (r ^ 2 * (1 + r ^ 2) ^ ν))]
  apply integrableOn_congr_fun _ measurableSet_Ioi
  intro r hr
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
  have hbase : 1 + r ^ 2 ≠ 0 := by positivity
  field_simp [ne_of_gt (show (0 : ℝ) < r from hr), pow_succ]
  ring

theorem loopMomentum_unitBall_volume :
    volume.real (ball (0 : LoopMomentum) 1) = Real.pi ^ 2 / 2 := by
  rw [measureReal_def, EuclideanSpace.volume_ball]
  norm_num [Real.Gamma_nat_eq_factorial, Real.sq_sqrt Real.pi_nonneg]
  rw [ENNReal.toReal_ofReal (by positivity)]
  congr 1
  nlinarith [Real.sq_sqrt Real.pi_nonneg]

theorem powerSelectedLine_integral_radial (ν d : ℕ) :
    (∫ q : LoopMomentum, powerSelectedLine ν d q) =
      2 * Real.pi ^ 2 * ∫ r : ℝ in Ioi 0, r ^ (d + 1) / (1 + r ^ 2) ^ ν := by
  unfold powerSelectedLine
  rw [integral_fun_norm_addHaar (E := LoopMomentum) volume
    (fun r : ℝ => r ^ d / (r ^ 2 * (1 + r ^ 2) ^ ν))]
  have he : (∫ r : ℝ in Ioi 0,
      r ^ (Module.finrank ℝ LoopMomentum - 1) • (r ^ d / (r ^ 2 * (1 + r ^ 2) ^ ν))) =
      ∫ r : ℝ in Ioi 0, r ^ (d + 1) / (1 + r ^ 2) ^ ν := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
    have hbase : 1 + r ^ 2 ≠ 0 := by positivity
    field_simp [ne_of_gt (show (0 : ℝ) < r from hr), pow_succ]
    ring
  rw [he, loopMomentum_unitBall_volume]
  simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
  ring

theorem powerSelectedLine_zero_integrable (n : ℕ) : Integrable (powerSelectedLine (n + 2) 0) := by
  apply (powerSelectedLine_integrable_iff_radial _ _).mpr
  simpa only [powerRadialBase, Nat.zero_add, pow_one] using powerRadialBase_integrable n

theorem powerSelectedLine_zero_integral (n : ℕ) :
    (∫ q : LoopMomentum, powerSelectedLine (n + 2) 0 q) = Real.pi ^ 2 / ((n + 1 : ℕ) : ℝ) := by
  rw [powerSelectedLine_integral_radial]
  simp only [Nat.zero_add, pow_one]
  change 2 * Real.pi ^ 2 * (∫ r : ℝ in Ioi 0, powerRadialBase n r) = _
  rw [powerRadialBase_integral]
  ring

theorem powerRadial32_eq (r : ℝ) :
    r ^ 3 / (1 + r ^ 2) ^ 3 = powerRadialBase 0 r - powerRadialBase 1 r := by
  unfold powerRadialBase
  norm_num only [Nat.reduceAdd]
  have hbase : 1 + r ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem powerRadial44_eq (r : ℝ) :
    r ^ 5 / (1 + r ^ 2) ^ 4 =
      powerRadialBase 0 r - 2 * powerRadialBase 1 r + powerRadialBase 2 r := by
  unfold powerRadialBase
  norm_num only [Nat.reduceAdd]
  have hbase : 1 + r ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem powerSelectedLine_30_integrable : Integrable (powerSelectedLine 3 0) :=
  powerSelectedLine_zero_integrable 1

theorem powerSelectedLine_32_integrable : Integrable (powerSelectedLine 3 2) := by
  apply (powerSelectedLine_integrable_iff_radial 3 2).mpr
  have hi : IntegrableOn (fun r => powerRadialBase 0 r - powerRadialBase 1 r) (Ioi 0) :=
    (powerRadialBase_integrable 0).sub (powerRadialBase_integrable 1)
  apply hi.congr_fun _ measurableSet_Ioi
  intro r _
  exact (powerRadial32_eq r).symm

theorem powerSelectedLine_40_integrable : Integrable (powerSelectedLine 4 0) :=
  powerSelectedLine_zero_integrable 2

theorem powerSelectedLine_44_integrable : Integrable (powerSelectedLine 4 4) := by
  apply (powerSelectedLine_integrable_iff_radial 4 4).mpr
  have hi : IntegrableOn
      (fun r => powerRadialBase 0 r - 2 * powerRadialBase 1 r + powerRadialBase 2 r) (Ioi 0) :=
    ((powerRadialBase_integrable 0).sub
      ((powerRadialBase_integrable 1).const_mul 2)).add (powerRadialBase_integrable 2)
  apply hi.congr_fun _ measurableSet_Ioi
  intro r _
  exact (powerRadial44_eq r).symm

theorem powerSelectedLine_30_integral :
    (∫ q : LoopMomentum, powerSelectedLine 3 0 q) = Real.pi ^ 2 / 2 :=
  powerSelectedLine_zero_integral 1

theorem powerSelectedLine_32_integral :
    (∫ q : LoopMomentum, powerSelectedLine 3 2 q) = Real.pi ^ 2 / 2 := by
  rw [powerSelectedLine_integral_radial]
  simp only [Nat.reduceAdd]
  simp_rw [powerRadial32_eq]
  rw [integral_sub (powerRadialBase_integrable 0) (powerRadialBase_integrable 1),
    powerRadialBase_integral, powerRadialBase_integral]
  norm_num
  ring

theorem powerSelectedLine_40_integral :
    (∫ q : LoopMomentum, powerSelectedLine 4 0 q) = Real.pi ^ 2 / 3 :=
  powerSelectedLine_zero_integral 2

theorem powerSelectedLine_44_integral :
    (∫ q : LoopMomentum, powerSelectedLine 4 4 q) = Real.pi ^ 2 / 3 := by
  rw [powerSelectedLine_integral_radial]
  simp only [Nat.reduceAdd]
  simp_rw [powerRadial44_eq]
  have hsub : IntegrableOn (fun r => powerRadialBase 0 r - 2 * powerRadialBase 1 r) (Ioi 0) :=
    (powerRadialBase_integrable 0).sub ((powerRadialBase_integrable 1).const_mul 2)
  have haddval : (∫ r : ℝ in Ioi 0,
      powerRadialBase 0 r - 2 * powerRadialBase 1 r + powerRadialBase 2 r) =
      (∫ r : ℝ in Ioi 0, powerRadialBase 0 r - 2 * powerRadialBase 1 r) +
        ∫ r : ℝ in Ioi 0, powerRadialBase 2 r := integral_add hsub (powerRadialBase_integrable 2)
  have hsubval : (∫ r : ℝ in Ioi 0, powerRadialBase 0 r - 2 * powerRadialBase 1 r) =
      (∫ r : ℝ in Ioi 0, powerRadialBase 0 r) - ∫ r : ℝ in Ioi 0, 2 * powerRadialBase 1 r :=
    integral_sub (powerRadialBase_integrable 0) ((powerRadialBase_integrable 1).const_mul 2)
  rw [haddval, hsubval, integral_const_mul,
    powerRadialBase_integral, powerRadialBase_integral, powerRadialBase_integral]
  norm_num
  ring

/-- The source's literal two-selected-line absolute weight, including the
eight-dimensional Fourier normalization. -/
def twoLoopSelectedWeight (k : LoopMomentum × LoopMomentum) : ℝ :=
  (powerSelectedLine 3 0 k.1 * powerSelectedLine 4 0 k.2 +
    powerSelectedLine 3 2 k.1 * powerSelectedLine 4 4 k.2) / (2 * Real.pi) ^ 8

theorem twoLoopSelectedWeight_nonneg (k : LoopMomentum × LoopMomentum) :
    0 ≤ twoLoopSelectedWeight k := by
  apply div_nonneg
  · exact add_nonneg
      (mul_nonneg (powerSelectedLine_nonneg _ _ _) (powerSelectedLine_nonneg _ _ _))
      (mul_nonneg (powerSelectedLine_nonneg _ _ _) (powerSelectedLine_nonneg _ _ _))
  · positivity

theorem twoLoopSelectedWeight_measurable : Measurable twoLoopSelectedWeight := by
  unfold twoLoopSelectedWeight powerSelectedLine
  fun_prop

theorem twoLoopSelectedWeight_integrable :
    Integrable twoLoopSelectedWeight (volume.prod volume) := by
  exact ((powerSelectedLine_30_integrable.mul_prod powerSelectedLine_40_integrable).add
    (powerSelectedLine_32_integrable.mul_prod powerSelectedLine_44_integrable)).div_const _

theorem twoLoopSelectedWeight_integral :
    (∫ k : LoopMomentum × LoopMomentum, twoLoopSelectedWeight k ∂volume.prod volume) =
      1 / (768 * Real.pi ^ 4) := by
  unfold twoLoopSelectedWeight
  rw [integral_div, integral_add
    (powerSelectedLine_30_integrable.mul_prod powerSelectedLine_40_integrable)
    (powerSelectedLine_32_integrable.mul_prod powerSelectedLine_44_integrable),
    integral_prod_mul, integral_prod_mul, powerSelectedLine_30_integral,
    powerSelectedLine_40_integral, powerSelectedLine_32_integral, powerSelectedLine_44_integral]
  field_simp
  ring

theorem twoLoopSelectedWeight_literal (k : LoopMomentum × LoopMomentum) :
    twoLoopSelectedWeight k = (1 + ‖k.1‖ ^ 2 * ‖k.2‖ ^ 4) /
      ((2 * Real.pi) ^ 8 * (‖k.1‖ ^ 2 * ‖k.2‖ ^ 2 *
        (1 + ‖k.1‖ ^ 2) ^ 3 * (1 + ‖k.2‖ ^ 2) ^ 4)) := by
  by_cases h1 : ‖k.1‖ = 0
  · simp [twoLoopSelectedWeight, powerSelectedLine, h1]
  by_cases h2 : ‖k.2‖ = 0
  · simp [twoLoopSelectedWeight, powerSelectedLine, h2]
  have hb1 : 1 + ‖k.1‖ ^ 2 ≠ 0 := by positivity
  have hb2 : 1 + ‖k.2‖ ^ 2 ≠ 0 := by positivity
  unfold twoLoopSelectedWeight powerSelectedLine
  field_simp

end UV
