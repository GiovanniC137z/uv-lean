import UV.ExtendNativeHolonomyFlat
import UV.ExtendNativeHolonomyHeat

/-! Identification of the literal relative proper-time trace with the
complete paired-winding expression. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace UV.ExtendNativeHolonomy

variable {E : Type} [NormedAddCommGroup E]

def normalHeatTrace (C : NormalCircle E) (s θ : ℝ) : ℝ :=
  ∑' n : ℤ, shiftedNormalHeatTerm C s θ n

def windingHeatReal (C : NormalCircle E) (s θ : ℝ) (w : ℤ) : ℝ :=
  Real.exp (-(w : ℝ) ^ 2 * C.length ^ 2 / (4 * s)) * Real.cos (↑w * θ)

private theorem normalWinding_gaussian_summable {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℤ => Real.exp (-(a * (n : ℝ) ^ 2))) := by
  have hNat : Summable (fun n : ℕ => Real.exp (-(a * (n : ℝ) ^ 2))) := by
    have hs := Real.summable_pow_mul_exp_neg_nat_mul 0 ha
    simp only [pow_zero, one_mul] at hs
    apply hs.of_nonneg_of_le (fun _ => Real.exp_nonneg _)
    intro n
    rw [Real.exp_le_exp]
    have h' : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast (show n ≤ n ^ 2 from Nat.le_self_pow (by norm_num) n)
    have h := mul_le_mul_of_nonneg_left h' ha.le
    nlinarith
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · simpa only [Int.cast_natCast] using hNat
  · simpa only [Int.cast_neg, Int.cast_natCast, neg_sq] using hNat

private theorem windingHeatTerm_summable (C : NormalCircle E) {s : ℝ}
    (hs : 0 < s) (θ : ℝ) : Summable (windingNormalHeatTerm C s θ) := by
  let a := C.length ^ 2 / (4 * s)
  have ha : 0 < a := div_pos (sq_pos_of_pos C.length_pos) (by positivity)
  apply (normalWinding_gaussian_summable ha).of_norm_bounded
  intro n
  simp only [windingNormalHeatTerm, Complex.norm_exp, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_self,
    add_zero]
  apply Real.exp_le_exp.mpr
  dsimp [a]
  apply le_of_eq
  ring

private theorem windingHeatTerm_re (C : NormalCircle E) (s θ : ℝ) (n : ℤ) :
    (windingNormalHeatTerm C s θ n).re = windingHeatReal C s θ n := by
  simp only [windingNormalHeatTerm, windingHeatReal, Complex.exp_re, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_self, add_zero, zero_add, mul_one]

private theorem windingHeatReal_summable (C : NormalCircle E) {s : ℝ}
    (hs : 0 < s) (θ : ℝ) : Summable (windingHeatReal C s θ) := by
  have hm := (windingHeatTerm_summable C hs θ).mapL Complex.reCLM
  change Summable (fun n => (windingNormalHeatTerm C s θ n).re) at hm
  simpa only [windingHeatTerm_re] using hm

private theorem normal_heatTrace_real (C : NormalCircle E) {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    normalHeatTrace C s θ = (C.length / Real.sqrt (4 * Real.pi * s)) *
      ∑' n : ℤ, windingHeatReal C s θ n := by
  have h := congrArg Complex.re (normal_heatTrace_poisson C hs θ)
  simpa only [normalHeatTrace, Complex.ofReal_re, Complex.re_ofReal_mul,
    Complex.re_tsum (windingHeatTerm_summable C hs θ), windingHeatTerm_re] using h

private theorem normal_heatTrace_difference (C : NormalCircle E) {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    normalHeatTrace C s 0 - normalHeatTrace C s θ =
      2 * (C.length / Real.sqrt (4 * Real.pi * s)) *
        ∑' n : ℕ, Real.exp (-(windingIndex n) ^ 2 * C.length ^ 2 / (4 * s)) *
          (1 - Real.cos (windingIndex n * θ)) := by
  let g : ℤ → ℝ := fun n => windingHeatReal C s 0 n - windingHeatReal C s θ n
  have hg : Summable g := (windingHeatReal_summable C hs 0).sub (windingHeatReal_summable C hs θ)
  have hgn (n : ℤ) : g (-n) = g n := by
    simp [g, windingHeatReal, Real.cos_neg]
  have hg₀ : g 0 = 0 := by simp [g, windingHeatReal]
  rw [normal_heatTrace_real C hs 0, normal_heatTrace_real C hs θ, ← mul_sub,
    ← (windingHeatReal_summable C hs 0).tsum_sub (windingHeatReal_summable C hs θ)]
  change _ * (∑' n, g n) = _
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat hgn hg, hg₀, zero_add,
    tsum_pnat_eq_tsum_succ (f := fun n : ℕ => g n), two_nsmul]
  have he (n : ℕ) : g (↑(n + 1) : ℤ) =
      Real.exp (-(windingIndex n) ^ 2 * C.length ^ 2 / (4 * s)) *
        (1 - Real.cos (windingIndex n * θ)) := by
    unfold g windingHeatReal windingIndex
    push_cast
    simp only [mul_zero, Real.cos_zero, mul_one]
    ring
  simp_rw [he]
  ring

def heatDetIntegrand (C : NormalCircle E) (θ : ℝ) (p : UV.ScalarMomentum) (s : ℝ) : ℝ :=
  Real.exp (-(holonomyEnergy C p ^ 2 * s)) *
    (normalHeatTrace C s 0 - normalHeatTrace C s θ) / (angularVolume * s)

def pairedProper (C : NormalCircle E) (θ : ℝ) (p : UV.ScalarMomentum) (n : ℕ) (s : ℝ) : ℝ :=
  (C.length / (Real.sqrt Real.pi * angularVolume) * (1 - Real.cos (windingIndex n * θ))) *
    properWindingKernel (windingIndex n * C.length) (holonomyEnergy C p) s

private theorem windingIndex_pos (n : ℕ) : 0 < windingIndex n := by
  unfold windingIndex
  positivity

private theorem pairedProper_nonneg (C : NormalCircle E) (θ : ℝ) (p : UV.ScalarMomentum)
    (n : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ pairedProper C θ p n s := by
  unfold pairedProper properWindingKernel angularVolume
  exact mul_nonneg (mul_nonneg (div_nonneg C.length_pos.le (by positivity))
    (sub_nonneg.mpr (Real.cos_le_one _))) (mul_nonneg (Real.rpow_nonneg hs _) (Real.exp_nonneg _))

private theorem heat_integrand_paired (C : NormalCircle E) (θ : ℝ) (p : UV.ScalarMomentum)
    {s : ℝ} (hs : 0 < s) : heatDetIntegrand C θ p s = ∑' n, pairedProper C θ p n s := by
  unfold heatDetIntegrand
  rw [normal_heatTrace_difference C hs θ, div_eq_mul_inv, ← mul_assoc,
    mul_comm (_ * _) ((angularVolume * s)⁻¹), ← mul_assoc, ← tsum_mul_left]
  congr 1
  funext n
  unfold pairedProper properWindingKernel
  rw [Real.exp_sub]
  have hκ : -(windingIndex n ^ 2) * C.length ^ 2 / (4 * s) =
      -((windingIndex n * C.length) ^ 2 / (4 * s)) := by ring
  rw [hκ]
  have hp : s ^ (-(3 : ℝ) / 2) = (s * Real.sqrt s)⁻¹ := by
    rw [show -(3 : ℝ) / 2 = -(1 + 1 / 2) by ring, Real.rpow_neg hs.le,
      Real.rpow_add hs, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hp, show 4 * Real.pi * s = 4 * (Real.pi * s) by ring,
    Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ)), Real.sqrt_mul Real.pi_pos.le,
    show Real.sqrt 4 = 2 by norm_num]
  simp only [Real.exp_neg, div_eq_mul_inv]
  have hv : 0 < angularVolume := by unfold angularVolume; positivity
  field_simp [hv.ne', hs.ne', (Real.sqrt_pos.mpr hs).ne', (Real.sqrt_pos.mpr Real.pi_pos).ne']

private theorem pairedProper_integral (C : NormalCircle E) (θ : ℝ) (p : UV.ScalarMomentum)
    (n : ℕ) :
    (∫ s in Ioi (0 : ℝ), pairedProper C θ p n s) = flatIntegrand C n 0 θ p := by
  unfold pairedProper
  rw [integral_const_mul, winding_proper_integral (mul_pos (windingIndex_pos n) C.length_pos)
    (by unfold holonomyEnergy; positivity)]
  unfold flatIntegrand windingDecay
  have hθ : windingProfile n 0 θ = 1 - Real.cos (windingIndex n * θ) := rfl
  rw [hθ]
  have hv : 0 < angularVolume := by unfold angularVolume; positivity
  field_simp [hv.ne', C.length_pos.ne', (windingIndex_pos n).ne',
    (Real.sqrt_pos.mpr Real.pi_pos).ne']

private theorem pairedProper_integrable (C : NormalCircle E) (θ : ℝ) (p : UV.ScalarMomentum)
    (n : ℕ) : IntegrableOn (pairedProper C θ p n) (Ioi (0 : ℝ)) := by
  have hpos := mul_pos (windingIndex_pos n) C.length_pos
  have hi : IntegrableOn (properWindingKernel (windingIndex n * C.length) (holonomyEnergy C p))
      (Ioi (0 : ℝ)) := by
    by_contra hno
    have he := winding_proper_integral (ω := holonomyEnergy C p) hpos (by unfold holonomyEnergy; positivity)
    unfold IntegrableOn at hno
    rw [integral_undef hno] at he
    exact (div_pos (mul_pos (mul_pos two_pos (Real.sqrt_pos.mpr Real.pi_pos)) (Real.exp_pos _))
      hpos).ne' he.symm
  exact hi.const_mul _

/-- Literal relative determinant per four-volume. The zero winding cancels
between the two traces before the proper-time integration. -/
theorem heatDet_integral_eq_flat (C : NormalCircle E) (θ : ℝ) :
    (∫ p, ∫ s in Ioi (0 : ℝ), heatDetIntegrand C θ p s) = flatLogDet C θ := by
  unfold flatLogDet
  apply integral_congr_ae
  refine Eventually.of_forall fun p => ?_
  dsimp only
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs =>
    heat_integrand_paired C θ p (mem_Ioi.mp hs))]
  have hS : Summable (fun n => ∫ s in Ioi (0 : ℝ), ‖pairedProper C θ p n s‖) := by
    have hEq (n : ℕ) : (∫ s in Ioi (0 : ℝ), ‖pairedProper C θ p n s‖) =
        flatIntegrand C n 0 θ p := by
      rw [← pairedProper_integral]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      exact Real.norm_of_nonneg (pairedProper_nonneg C θ p n (mem_Ioi.mp hs).le)
    simp_rw [hEq]
    exact flatIntegrand_summable C 0 θ p
  rw [← integral_tsum_of_summable_integral_norm (pairedProper_integrable C θ p) hS]
  simp only [pairedProper_integral]

end UV.ExtendNativeHolonomy
