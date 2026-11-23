import UV.ContinueNormalHolonomyTheta
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Gaussian winding integrals after the quartic change of radial scale. -/

noncomputable section

open Real Set Filter MeasureTheory
open scoped Topology

namespace UV.ContinueNormalHolonomy

/-- Rescaled limiting winding density for a radial insertion (r^p). -/
def quarticWindingProfile (p w x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * x ^ (p + 4) * Real.exp (-(Real.pi ^ 2 * w ^ 2) * x ^ (8 : ℕ))

theorem quarticWindingProfile_integrable {p w : ℝ} (hp : 0 ≤ p) (hw : w ≠ 0) :
    IntegrableOn (quarticWindingProfile p w) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (b := Real.pi ^ 2 * w ^ 2) (p := 8) (s := p + 4)
    (by linarith) (by norm_num) (by positivity)
  simp only [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
  change Integrable (quarticWindingProfile p w) (volume.restrict (Ioi (0 : ℝ)))
  exact (h.const_mul (1 / 2 : ℝ)).congr (ae_of_all _ fun x => by
    rw [quarticWindingProfile, mul_assoc])

theorem quarticWindingProfile_integral {p w : ℝ} (hp : 0 ≤ p) (hw : w ≠ 0) :
    (∫ x in Ioi 0, quarticWindingProfile p w x) =
      Real.Gamma ((p + 5) / 8) /
        (16 * Real.pi ^ ((p + 5) / 4) * |w| ^ ((p + 5) / 4)) := by
  simp only [quarticWindingProfile, mul_assoc, integral_const_mul]
  have hg := integral_rpow_mul_exp_neg_mul_rpow (p := 8) (q := p + 4)
     (b := Real.pi ^ 2 * w ^ 2) (by norm_num) (by linarith) (by positivity)
  rw [show (p + 4 + 1) = (p + 5) by ring] at hg
  simp only [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hg
  rw [hg, ← sq_abs w, Real.mul_rpow (sq_nonneg _) (sq_nonneg _)]
  rw [← Real.rpow_natCast_mul Real.pi_pos.le, ← Real.rpow_natCast_mul (abs_nonneg w)]
  norm_num
  rw [show 2 * ((-5 + -p) / 8) = -((p + 5) / 4) by ring,
    Real.rpow_neg Real.pi_pos.le, Real.rpow_neg (abs_nonneg w)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The positive quartic-scale coefficient of a fixed nonzero marked winding. -/
theorem quarticWindingProfile_integral_positive {p w : ℝ} (hp : 0 ≤ p) (hw : w ≠ 0) :
    0 < ∫ x in Ioi 0, quarticWindingProfile p w x := by
  rw [quarticWindingProfile_integral hp hw]
  apply div_pos (Real.Gamma_pos_of_pos (by linarith))
  positivity

/-- The loss of a winding phase under a fixed normal holonomy. -/
def normalWindingPhaseLoss (a : ℝ) (w : ℕ+) : ℝ :=
  1 - Real.cos (2 * Real.pi * (w : ℕ) * a)

private theorem normalWindingPhaseLoss_nonneg (a : ℝ) (w : ℕ+) :
    0 ≤ normalWindingPhaseLoss a w :=
  sub_nonneg.mpr (Real.cos_le_one _)

private theorem normalWindingPhaseLoss_le_two (a : ℝ) (w : ℕ+) :
    normalWindingPhaseLoss a w ≤ 2 := by
  unfold normalWindingPhaseLoss
  linarith [Real.neg_one_le_cos (2 * Real.pi * (w : ℕ) * a)]

/-- Winding sum after evaluating the positive quartic radial integrals. -/
def quarticHolonomyConstant (a : ℝ) : ℝ :=
  Real.Gamma (5 / 8) / (8 * Real.pi ^ (5 / 4 : ℝ)) *
    ∑' w : ℕ+, normalWindingPhaseLoss a w / ((w : ℕ) : ℝ) ^ (5 / 4 : ℝ)

private theorem quarticHolonomySeries_summable (a : ℝ) :
    Summable (fun w : ℕ+ => normalWindingPhaseLoss a w / ((w : ℕ) : ℝ) ^ (5 / 4 : ℝ)) := by
  have hs := (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 5 / 4)).comp_injective
    (show Function.Injective (fun w : ℕ+ => (w : ℕ)) from Subtype.val_injective)
  apply (hs.mul_left (2 : ℝ)).of_norm_bounded
  intro w
  rw [Real.norm_of_nonneg (div_nonneg (normalWindingPhaseLoss_nonneg _ _) (by positivity))]
  exact (div_le_div_of_nonneg_right (normalWindingPhaseLoss_le_two _ _) (by positivity)).trans_eq
    (div_eq_mul_inv _ _)

theorem quarticHolonomyConstant_positive {a : ℝ} (ha : ∀ m : ℤ, a ≠ (m : ℝ)) :
    0 < quarticHolonomyConstant a := by
  unfold quarticHolonomyConstant
  apply mul_pos (div_pos (Real.Gamma_pos_of_pos (by norm_num)) (by positivity))
  have h : 0 < normalWindingPhaseLoss a 1 := by
    unfold normalWindingPhaseLoss
    norm_num
    apply lt_of_le_of_ne (Real.cos_le_one _)
    intro h
    obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff _).mp h
    exact ha m (mul_left_cancel₀ (show 2 * Real.pi ≠ 0 by positivity) (by linarith))
  refine (div_pos h (by positivity : 0 < (((1 : ℕ+) : ℕ) : ℝ) ^ (5 / 4 : ℝ))).trans_le ?_
  apply (quarticHolonomySeries_summable a).le_tsum
  intro w _
  exact div_nonneg (normalWindingPhaseLoss_nonneg _ _) (by positivity)

private def quarticHolonomyTerm (a : ℝ) (w : ℕ+) (x : ℝ) : ℝ :=
  (2 * normalWindingPhaseLoss a w) * quarticWindingProfile 0 (w : ℕ) x

theorem quarticHolonomyProfile_eq (a x : ℝ) (hx : 0 < x) :
    (Real.sqrt (4 * Real.pi))⁻¹ * relativeNormalTheta (x ^ (8 : ℕ))⁻¹ a =
      ∑' w : ℕ+, quarticHolonomyTerm a w x := by
  have hx8 : 0 < x ^ (8 : ℕ) := pow_pos hx 8
  rw [relativeNormalTheta_poisson (inv_pos.mpr hx8), div_inv_eq_mul,
    Real.sqrt_mul Real.pi_pos.le, Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ))]
  have he : Real.sqrt (x ^ (8 : ℕ)) = x ^ (4 : ℕ) := by
    rw [show (8 : ℕ) = 4 * 2 by decide, pow_mul, Real.sqrt_sq (by positivity)]
  have hfour : Real.sqrt (4 : ℝ) = 2 := by
    convert Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2) using 1
    norm_num
  rw [he, hfour, ← mul_assoc,
    show (2 * Real.sqrt Real.pi)⁻¹ * (2 * (Real.sqrt Real.pi * x ^ (4 : ℕ))) = x ^ (4 : ℕ) by
      field_simp [Real.sqrt_ne_zero'.mpr Real.pi_pos], ← tsum_mul_left]
  apply tsum_congr
  intro w
  simp only [relativeNormalWinding, quarticHolonomyTerm, normalWindingPhaseLoss,
    quarticWindingProfile, zero_add, Int.cast_natCast]
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_inv_eq_mul]
  rw [show -(Real.pi ^ 2 * x ^ (8 : ℕ)) * ((w : ℕ) : ℝ) ^ 2 =
    -(Real.pi ^ 2 * ((w : ℕ) : ℝ) ^ 2) * x ^ (8 : ℕ) by ring]
  ring

/-- The exact Gamma coefficient of the limiting rescaled relative radial trace.
The factor (2) for both signs of each winding is included. -/
theorem quarticHolonomyProfile_integral (a : ℝ) :
    (∫ x in Ioi 0, (Real.sqrt (4 * Real.pi))⁻¹ * relativeNormalTheta (x ^ (8 : ℕ))⁻¹ a) =
      quarticHolonomyConstant a := by
  let μ := (volume : Measure ℝ).restrict (Ioi 0)
  have hi (w : ℕ+) : Integrable (quarticHolonomyTerm a w) μ :=
    (quarticWindingProfile_integrable (p := 0) (w := ((w : ℕ) : ℝ))
      (by norm_num) (by exact_mod_cast (PNat.ne_zero w))).const_mul _
  have hnorm (w : ℕ+) :
      (∫ x, ‖quarticHolonomyTerm a w x‖ ∂μ) = ∫ x, quarticHolonomyTerm a w x ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Real.norm_of_nonneg (by
      unfold quarticHolonomyTerm quarticWindingProfile
      have := normalWindingPhaseLoss_nonneg a w
      have : 0 ≤ x := hx.le
      positivity)
  have he (w : ℕ+) : (∫ x, quarticHolonomyTerm a w x ∂μ) =
      (Real.Gamma (5 / 8) / (8 * Real.pi ^ (5 / 4 : ℝ))) *
        (normalWindingPhaseLoss a w / ((w : ℕ) : ℝ) ^ (5 / 4 : ℝ)) := by
    rw [show (fun x => quarticHolonomyTerm a w x) =
      fun x => (2 * normalWindingPhaseLoss a w) * quarticWindingProfile 0 (w : ℕ) x from rfl,
      integral_const_mul]
    change (2 * normalWindingPhaseLoss a w) * (∫ x in Ioi 0, quarticWindingProfile 0 (w : ℕ) x) = _
    rw [quarticWindingProfile_integral (by norm_num) (by exact_mod_cast (PNat.ne_zero w)),
      zero_add, abs_of_nonneg (Nat.cast_nonneg _)]
    field_simp
    ring
  have hs : Summable (fun w : ℕ+ => ∫ x, ‖quarticHolonomyTerm a w x‖ ∂μ) := by
    simp_rw [hnorm, he]
    exact (quarticHolonomySeries_summable a).mul_left _
  calc
    _ = ∫ x, (∑' w : ℕ+, quarticHolonomyTerm a w x) ∂μ :=
      setIntegral_congr_fun measurableSet_Ioi (fun x hx => quarticHolonomyProfile_eq a x hx)
    _ = ∑' w : ℕ+, ∫ x, quarticHolonomyTerm a w x ∂μ :=
      (integral_tsum_of_summable_integral_norm hi hs).symm
    _ = _ := by simp only [he, tsum_mul_left, quarticHolonomyConstant]

end UV.ContinueNormalHolonomy
