import UV.Subordination
import UV.MomentRecurrence

/-! Exact inverse moments of the OQED heat density.

`modifiedBesselK` uses the symmetric Schläfli integral on the positive real
axis: K_ν(z) = ½ ∫₀∞ t^(ν−1) exp(−z(t+t⁻¹)/2) dt.  This is the standard
modified Bessel K convention, equivalent by positive scaling to DLMF 10.32.10.
Its integration variable and order are independent of the OQED density.
Only the positive-argument branch is used below. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal

namespace UV

/-- Symmetric Schläfli integral for the real modified Bessel function K. -/
def modifiedBesselK (ν z : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ t : ℝ in Ioi 0,
    t ^ (ν - 1) * Real.exp (-(z / 2) * (t + t⁻¹))

def temperedInverseCore (μ r τ : ℝ) : ℝ :=
  τ ^ (-r - 3 / 2) * Real.exp (-(μ ^ 2 * τ) - 1 / (4 * τ))

theorem temperedInverseCore_integrable (μ : ℝ) {r : ℝ} (hr : -(1 / 2 : ℝ) < r) :
    IntegrableOn (temperedInverseCore μ r) (Ioi 0) := by
  refine (inverseCore_integrable hr).mono' (by unfold temperedInverseCore; fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  unfold temperedInverseCore
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hτ.le _) (Real.exp_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hτ.le _)
  apply Real.exp_le_exp.mpr
  have h := mul_nonneg (sq_nonneg μ) hτ.le
  linarith

theorem temperedInverseCore_inversion (μ r τ : ℝ) (hτ : 0 < τ) :
    ((-1 : ℝ) ^ 2 * τ ^ ((-1 : ℝ) - 1)) *
      ((τ ^ (-1 : ℝ)) ^ (r - 1 / 2) *
        Real.exp (-(μ ^ 2 / (τ ^ (-1 : ℝ)) + τ ^ (-1 : ℝ) / 4))) =
      temperedInverseCore μ r τ := by
  unfold temperedInverseCore
  norm_num only [neg_one_sq, one_mul]
  rw [← Real.rpow_mul hτ.le, ← mul_assoc, ← Real.rpow_add hτ]
  congr 1
  · congr 1
    ring
  · rw [Real.rpow_neg_one]
    congr 1
    field_simp
    ring

theorem temperedInverseCore_integral_inversion (μ r : ℝ) :
    (∫ τ : ℝ in Ioi 0, temperedInverseCore μ r τ) =
      ∫ x : ℝ in Ioi 0, x ^ (r - 1 / 2) * Real.exp (-(μ ^ 2 / x + x / 4)) := by
  calc
    _ = ∫ τ : ℝ in Ioi 0, (|(-1 : ℝ)| * τ ^ ((-1 : ℝ) - 1)) •
        ((τ ^ (-1 : ℝ)) ^ (r - 1 / 2) *
          Real.exp (-(μ ^ 2 / (τ ^ (-1 : ℝ)) + τ ^ (-1 : ℝ) / 4))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro τ hτ
      simpa only [abs_neg, abs_one, one_mul, smul_eq_mul, neg_one_sq] using
        (temperedInverseCore_inversion μ r τ hτ).symm
    _ = _ := integral_comp_rpow_Ioi
      (fun x : ℝ => x ^ (r - 1 / 2) * Real.exp (-(μ ^ 2 / x + x / 4)))
      (p := -1) (by norm_num)

theorem temperedInverseCore_bessel_integral {μ : ℝ} (hμ : 0 < μ) (r : ℝ) :
    (∫ τ : ℝ in Ioi 0, temperedInverseCore μ r τ) =
      2 * (2 * μ) ^ (r + 1 / 2) * modifiedBesselK (r + 1 / 2) μ := by
  have hp : 0 < 2 * μ := by positivity
  have hs : (2 * μ) * (2 * μ) ^ (r - 1 / 2) = (2 * μ) ^ (r + 1 / 2) := by
    rw [show r + 1 / 2 = 1 + (r - 1 / 2) by ring, Real.rpow_add hp, Real.rpow_one]
  rw [temperedInverseCore_integral_inversion]
  calc
    _ = (2 * μ) * ∫ t : ℝ in Ioi 0,
        (2 * μ * t) ^ (r - 1 / 2) * Real.exp (-(μ ^ 2 / (2 * μ * t) + (2 * μ * t) / 4)) := by
      rw [integral_comp_mul_left_Ioi
        (fun x : ℝ => x ^ (r - 1 / 2) * Real.exp (-(μ ^ 2 / x + x / 4))) 0 hp,
        smul_eq_mul, mul_zero, ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
    _ = (2 * μ) * ∫ t : ℝ in Ioi 0,
        (2 * μ) ^ (r - 1 / 2) *
          (t ^ (r - 1 / 2) * Real.exp (-(μ / 2) * (t + t⁻¹))) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [Real.mul_rpow hp.le ht.le]
      have he : -(μ ^ 2 / (2 * μ * t) + (2 * μ * t) / 4) =
          -(μ / 2) * (t + t⁻¹) := by
        field_simp
        ring
      rw [he]
      ring
    _ = _ := by
      rw [integral_const_mul, ← mul_assoc, hs]
      unfold modifiedBesselK
      rw [show r + 1 / 2 - 1 = r - 1 / 2 by ring]
      ring

theorem oqedWeightedDensity_bessel {μ : ℝ} (hμ : 0 < μ) (r : ℝ) :
    (∫ τ : ℝ in Ioi 0, τ ^ (-r) * oqedDensity μ τ) =
      Real.exp μ / Real.sqrt Real.pi * (2 * μ) ^ (r + 1 / 2) *
        modifiedBesselK (r + 1 / 2) μ := by
  calc
    _ = (Real.exp μ / (2 * Real.sqrt Real.pi)) *
        ∫ τ : ℝ in Ioi 0, temperedInverseCore μ r τ := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro τ hτ
      unfold oqedDensity oqedDensityCore temperedInverseCore
      dsimp only
      rw [show -r - 3 / 2 = -r + (-(3 : ℝ) / 2) by ring, Real.rpow_add hτ]
      ring
    _ = _ := by
      rw [temperedInverseCore_bessel_integral hμ]
      ring

/-- The genuine Bessel-K inverse-moment formula for the literal OQED measure. -/
theorem oqedInverseMoment_bessel {μ r : ℝ} (hμ : 0 < μ) (hr : -(1 / 2 : ℝ) < r) :
    inverseMoment (oqedMeasure μ) r =
      ENNReal.ofReal (Real.exp μ / Real.sqrt Real.pi * (2 * μ) ^ (r + 1 / 2) *
        modifiedBesselK (r + 1 / 2) μ) := by
  rw [oqedInverseMoment_eq, ← oqedWeightedDensity_bessel hμ r]
  symm
  apply ofReal_integral_eq_lintegral_ofReal (oqedWeightedDensity_integrable μ hr)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  exact mul_nonneg (Real.rpow_nonneg hτ.le _) (oqedDensity_nonneg μ τ hτ.le)

/-- The standard Schläfli integrand is genuinely integrable on the order range
needed for every source inverse moment. -/
theorem modifiedBesselK_integrable_pos_order {ν z : ℝ} (hν : 0 < ν) (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => t ^ (ν - 1) *
      Real.exp (-(z / 2) * (t + t⁻¹))) (Ioi 0) := by
  let f : ℝ → ℝ := fun x => x ^ (ν - 1) * Real.exp (-(z ^ 2 / x + x / 4))
  have hp : 0 < 2 * z := by positivity
  have hcore := temperedInverseCore_integrable z (r := ν - 1 / 2) (by linarith)
  have hinv : IntegrableOn (fun t : ℝ => (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) •
      f (t ^ (-1 : ℝ))) (Ioi 0) := by
    apply hcore.congr_fun _ measurableSet_Ioi
    intro t ht
    dsimp only [f]
    simpa only [abs_neg, abs_one, one_mul, smul_eq_mul, neg_one_sq,
      show ν - 1 / 2 - 1 / 2 = ν - 1 by ring] using
      (temperedInverseCore_inversion z (ν - 1 / 2) t ht).symm
  have hf : IntegrableOn f (Ioi 0) :=
    (integrableOn_Ioi_comp_rpow_iff f (p := -1) (by norm_num)).mp hinv
  have hscale := (integrableOn_Ioi_comp_mul_left_iff f 0 hp).mpr
    (by simpa only [mul_zero] using hf)
  have hc : IntegrableOn (fun t : ℝ => (2 * z) ^ (ν - 1) *
      (t ^ (ν - 1) * Real.exp (-(z / 2) * (t + t⁻¹)))) (Ioi 0) := by
    apply hscale.congr_fun _ measurableSet_Ioi
    intro t ht
    dsimp only [f]
    rw [Real.mul_rpow hp.le ht.le]
    have he : -(z ^ 2 / (2 * z * t) + (2 * z * t) / 4) =
        -(z / 2) * (t + t⁻¹) := by
      field_simp
      ring
    rw [he]
    ring
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr
    (Real.rpow_pos_of_pos hp (ν - 1)).ne') _).mp hc

theorem modifiedBesselK_order_reflection (ν z : ℝ) :
    modifiedBesselK (-ν) z = modifiedBesselK ν z := by
  unfold modifiedBesselK
  congr 1
  calc
    _ = ∫ t : ℝ in Ioi 0, (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) •
        ((t ^ (-1 : ℝ)) ^ (ν - 1) *
          Real.exp (-(z / 2) * (t ^ (-1 : ℝ) + (t ^ (-1 : ℝ))⁻¹))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      simp only [abs_neg, abs_one, one_mul, smul_eq_mul]
      rw [← Real.rpow_mul ht.le, ← mul_assoc, ← Real.rpow_add ht]
      congr 1
      · congr 1
        ring
      · rw [Real.rpow_neg_one, inv_inv, add_comm]
    _ = _ := integral_comp_rpow_Ioi
      (fun t : ℝ => t ^ (ν - 1) * Real.exp (-(z / 2) * (t + t⁻¹)))
      (p := -1) (by norm_num)

/-- DLMF 10.32.10, the usual Schläfli integral convention for K.  This identity
is obtained independently of the heat density by positive scaling and order
reflection. -/
theorem modifiedBesselK_schlafli (ν : ℝ) {z : ℝ} (hz : 0 < z) :
    modifiedBesselK ν z =
      (1 / 2 : ℝ) * (z / 2) ^ ν * ∫ t : ℝ in Ioi 0,
        t ^ (-ν - 1) * Real.exp (-t - z ^ 2 / (4 * t)) := by
  have hp : 0 < z / 2 := by positivity
  have hc : (z / 2) * (z / 2) ^ (-ν - 1) = (z / 2) ^ (-ν) := by
    calc
      _ = (z / 2) ^ (1 + (-ν - 1)) := by rw [Real.rpow_add hp, Real.rpow_one]
      _ = _ := by congr 1; ring
  have hi : (∫ t : ℝ in Ioi 0, t ^ (-ν - 1) * Real.exp (-t - z ^ 2 / (4 * t))) =
      (z / 2) ^ (-ν) * ∫ s : ℝ in Ioi 0,
        s ^ (-ν - 1) * Real.exp (-(z / 2) * (s + s⁻¹)) := by
    calc
      _ = (z / 2) * ∫ s : ℝ in Ioi 0,
          (z / 2 * s) ^ (-ν - 1) * Real.exp (-(z / 2 * s) - z ^ 2 / (4 * (z / 2 * s))) := by
        rw [integral_comp_mul_left_Ioi
          (fun t : ℝ => t ^ (-ν - 1) * Real.exp (-t - z ^ 2 / (4 * t))) 0 hp,
          smul_eq_mul, mul_zero, ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
      _ = (z / 2) * ∫ s : ℝ in Ioi 0,
          (z / 2) ^ (-ν - 1) *
            (s ^ (-ν - 1) * Real.exp (-(z / 2) * (s + s⁻¹))) := by
        congr 1
        apply setIntegral_congr_fun measurableSet_Ioi
        intro s hs
        dsimp only
        rw [Real.mul_rpow hp.le hs.le]
        have he : -(z / 2 * s) - z ^ 2 / (4 * (z / 2 * s)) =
            -(z / 2) * (s + s⁻¹) := by
          field_simp
          ring
        rw [he]
        ring
      _ = _ := by rw [integral_const_mul, ← mul_assoc, hc]
  rw [hi]
  symm
  calc
    _ = modifiedBesselK (-ν) z := by
      unfold modifiedBesselK
      rw [show -ν - 1 = (-ν) - 1 by ring]
      rw [show (1 / 2 : ℝ) * (z / 2) ^ ν *
        ((z / 2) ^ (-ν) * (∫ s : ℝ in Ioi 0,
          s ^ (-ν - 1) * Real.exp (-(z / 2) * (s + s⁻¹)))) =
        (1 / 2 : ℝ) * ((z / 2) ^ ν * (z / 2) ^ (-ν)) *
          (∫ s : ℝ in Ioi 0, s ^ (-ν - 1) *
            Real.exp (-(z / 2) * (s + s⁻¹))) by ring,
        ← Real.rpow_add hp, add_neg_cancel, Real.rpow_zero, mul_one]
    _ = _ := modifiedBesselK_order_reflection ν z

end UV
