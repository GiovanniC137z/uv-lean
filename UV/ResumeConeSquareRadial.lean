import UV.ResumeConePole
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-! Exact radial evaluation of the displayed cone-square angular
coefficient. This evaluates its radial contribution with a fixed
positive cutoff. The angular-average identity is a separate step. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Set
open scoped Interval

def coneSquareRadialWeight (h r : ℝ) : ℝ :=
  r ^ 5 / (Real.sqrt (h ^ 2 + r ^ 4)) ^ 3

theorem cone_square_radial_weight_eq {h r : ℝ} (hr : 0 < r) :
    coneSquareRadialWeight h r = r⁻¹ / (Real.sqrt (1 + (h / r ^ 2) ^ 2)) ^ 3 := by
  have H : Real.sqrt (h ^ 2 + r ^ 4) = r ^ 2 * Real.sqrt (1 + (h / r ^ 2) ^ 2) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
    field_simp [hr.ne']
    exact add_comm _ _
  unfold coneSquareRadialWeight
  rw [H, mul_pow, div_mul_eq_div_div, ← pow_mul]
  field_simp [hr.ne']

theorem cone_square_radial_integral {h R : ℝ} (hh : 0 < h) :
    (∫ r in (0 : ℝ)..R, coneSquareRadialWeight h r) =
      (Real.arsinh (R ^ 2 / h) - R ^ 2 / Real.sqrt (h ^ 2 + R ^ 4)) / 2 := by
  let F (r : ℝ) := (Real.arsinh (r ^ 2 / h) - r ^ 2 / Real.sqrt (h ^ 2 + r ^ 4)) / 2
  have hpos (r : ℝ) : 0 < h ^ 2 + r ^ 4 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hh) (by positivity)
  have hd (r : ℝ) : HasDerivAt F (coneSquareRadialWeight h r) r := by
    let S := Real.sqrt (h ^ 2 + r ^ 4)
    have hS : 0 < S := Real.sqrt_pos.mpr (hpos r)
    have hS2 : S ^ 2 = h ^ 2 + r ^ 4 := Real.sq_sqrt (hpos r).le
    have hsqrt : Real.sqrt (1 + (r ^ 2 / h) ^ 2) = S / h := by
      apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (div_nonneg hS.le hh.le)).mp
      rw [Real.sq_sqrt (by positivity), div_pow, div_pow, hS2]
      field_simp [hh.ne']
    have htop : HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_id r).pow 2
    have hpoly : HasDerivAt (fun t : ℝ => h ^ 2 + t ^ 4) (4 * r ^ 3) r := by
      simpa using ((hasDerivAt_id r).pow 4).const_add (h ^ 2)
    have hroot := (Real.hasDerivAt_sqrt (hpos r).ne').comp r hpoly
    have hs : HasDerivAt (fun r : ℝ => Real.sqrt (h ^ 2 + r ^ 4)) (2 * r ^ 3 / S) r := by
      convert hroot using 1
      unfold S
      ring
    have hdA := (Real.hasDerivAt_arsinh (r ^ 2 / h)).comp r (htop.div_const h)
    have hdB := htop.div hs hS.ne'
    convert (hdA.sub hdB).div_const 2 using 1
    rw [hsqrt]
    change coneSquareRadialWeight h r =
      ((S / h)⁻¹ * (2 * r / h) - (2 * r * S - r ^ 2 * (2 * r ^ 3 / S)) / S ^ 2) / 2
    change r ^ 5 / S ^ 3 = _
    field_simp [hS.ne', hh.ne']
    ring
  have hc : Continuous (coneSquareRadialWeight h) := by
    unfold coneSquareRadialWeight
    exact (continuous_id.pow 5).div
      ((Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 4))).pow 3)
      (fun r => pow_ne_zero _ (Real.sqrt_pos.mpr (hpos r)).ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
    (hc.intervalIntegrable _ _)]
  simp [F, Real.arsinh_zero]

/-- The radial term of the square has the exact log coefficient π²
after multiplication by the area of the three-sphere. -/
theorem cone_square_radial_log_budget {h R : ℝ} (hh : 0 < h) (hR : 0 < R)
    (hsmall : h ≤ R ^ 2) :
    ‖2 * Real.pi ^ 2 * (∫ r in (0 : ℝ)..R, coneSquareRadialWeight h r) -
        Real.pi ^ 2 * Real.log (R ^ 2 / h)‖ ≤ Real.pi ^ 2 * (1 + Real.log 3) := by
  let u := R ^ 2 / h
  let s := Real.sqrt (1 + u ^ 2)
  have hu : 1 ≤ u := (le_div_iff₀ hh).mpr (by simpa using hsmall)
  have hu₀ : 0 < u := zero_lt_one.trans_le hu
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs₁ : s ^ 2 = 1 + u ^ 2 := Real.sq_sqrt (by positivity)
  have hle : u ≤ s :=
    (sq_le_sq₀ hu₀.le hs.le).mp (by rw [hs₁]; linarith)
  have hle' : s ≤ 2 * u := by
    apply (sq_le_sq₀ hs.le (by positivity)).mp
    rw [hs₁]
    nlinarith [mul_le_mul_of_nonneg_right hu hu₀.le]
  have hrat : R ^ 2 / Real.sqrt (h ^ 2 + R ^ 4) = u / s := by
    have he : Real.sqrt (h ^ 2 + R ^ 4) = h * s := by
      apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hh.le hs.le)).mp
      rw [Real.sq_sqrt (by positivity), mul_pow, hs₁]
      dsimp [u]
      field_simp [hh.ne']
    rw [he]
    dsimp [u]
    field_simp [hh.ne', hs.ne']
  have hlog₀ : Real.log u ≤ Real.arsinh u := by
    unfold Real.arsinh
    exact Real.log_le_log hu₀ (by change u ≤ u + s; linarith)
  have hlog₁ : Real.arsinh u ≤ Real.log u + Real.log 3 := by
    unfold Real.arsinh
    have h := Real.log_le_log (show 0 < u + s by positivity) (show u + s ≤ u * 3 by linarith)
    rwa [Real.log_mul hu₀.ne' (by norm_num : (3 : ℝ) ≠ 0)] at h
  have hq₀ : 0 ≤ u / s := div_nonneg hu₀.le hs.le
  have hq₁ : u / s ≤ 1 := (div_le_one hs).mpr hle
  rw [cone_square_radial_integral hh, hrat]
  change ‖2 * Real.pi ^ 2 * ((Real.arsinh u - u / s) / 2) -
    Real.pi ^ 2 * Real.log u‖ ≤ _
  rw [show 2 * Real.pi ^ 2 * ((Real.arsinh u - u / s) / 2) -
    Real.pi ^ 2 * Real.log u = Real.pi ^ 2 * (Real.arsinh u - Real.log u - u / s) by ring,
    norm_mul, Real.norm_of_nonneg (sq_nonneg Real.pi)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  rw [Real.norm_eq_abs, abs_le]
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  constructor <;> linarith

end UV.SectorPlane
