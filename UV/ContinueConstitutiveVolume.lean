import UV.ContinueConstitutiveMagnetic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Calibration of the sampling length by additive swept volume in the
three-dimensional Euclidean tangent ball on the fixed carrier frame. -/

noncomputable section

open MeasureTheory Set Real
open scoped NNReal

namespace UV
open SectorPlane

def constitutiveBallVolume (a : ℝ≥0) : ℝ :=
  (volume : Measure Spatial).real (Metric.ball 0 a.val)

theorem constitutiveBallVolume_value (a : ℝ≥0) :
    constitutiveBallVolume a = (4*π/3) * a.val^3 := by
  rw [constitutiveBallVolume, measureReal_def, EuclideanSpace.volume_ball_fin_three,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal a.property,
    ENNReal.toReal_ofReal (by positivity)]
  ring

/-- A nonnegative additive volume is linear in proper length. Integer
bracketing establishes the statement for every real length on the ray. -/
theorem positive_swept_volume_linear (V : ℝ≥0 →+ ℝ) (hp : ∀ s, 0 ≤ V s) (s : ℝ≥0) :
    V s = (s:ℝ) * V 1 := by
  have hm : Monotone V := by
    intro x y hxy
    have ha := V.map_add x (y-x)
    rw [add_tsub_cancel_of_le hxy] at ha
    linarith [hp (y-x)]
  have hnat (j : ℕ) : V (j : ℝ≥0) = (j:ℝ)*V 1 := by
    simpa only [nsmul_eq_mul, mul_one] using V.map_nsmul (1:ℝ≥0) j
  have hbound (n : ℕ) : |(n:ℝ) * (V s - (s:ℝ)*V 1)| ≤ V 1 := by
    let j := ⌊(n:ℝ≥0)*s⌋₊
    have h₁ : (j:ℝ≥0) ≤ (n:ℝ≥0)*s := Nat.floor_le (by positivity)
    have h₂ : (n:ℝ≥0)*s ≤ (j:ℝ≥0)+1 := (Nat.lt_floor_add_one _).le
    have hv₁ := hm h₁
    have hv₂ := hm h₂
    have hns : V ((n:ℝ≥0)*s) = (n:ℝ)*V s := by simpa only [nsmul_eq_mul] using V.map_nsmul s n
    rw [hnat, hns] at hv₁
    rw [hns, V.map_add, hnat] at hv₂
    have hj₁ : (j:ℝ) ≤ (n:ℝ)*(s:ℝ) := by exact_mod_cast h₁
    have hj₂ : (n:ℝ)*(s:ℝ) ≤ (j:ℝ)+1 := by exact_mod_cast h₂
    rw [abs_le]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_right hj₁ (hp 1), mul_le_mul_of_nonneg_right hj₂ (hp 1)]
  by_contra hne
  have hd := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n,hn⟩ := exists_nat_gt (V 1 / |V s - (s:ℝ)*V 1|)
  have hlarge := (div_lt_iff₀ hd).mp hn
  have hsmall := hbound n
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)] at hsmall
  linarith

theorem constitutive_volume_law (a : ℝ≥0 → ℝ≥0) {L : ℝ≥0} (hL : 0 < L)
    (hcal : a L = L) (hadd : ∀ s t, constitutiveBallVolume (a (s+t)) =
      constitutiveBallVolume (a s) + constitutiveBallVolume (a t)) (s : ℝ≥0) :
    ((a s : ℝ≥0) : ℝ)^3 = (L:ℝ)^2 * (s:ℝ) := by
  let V : ℝ≥0 →+ ℝ := {
    toFun := fun t => constitutiveBallVolume (a t)
    map_zero' := by have h := hadd 0 0; simp only [add_zero] at h; linarith
    map_add' := hadd }
  have hp (t : ℝ≥0) : 0 ≤ V t := ENNReal.toReal_nonneg
  have h₁ := positive_swept_volume_linear V hp s
  have h₂ := positive_swept_volume_linear V hp L
  change constitutiveBallVolume (a s) = (s:ℝ)*V 1 at h₁
  change constitutiveBallVolume (a L) = (L:ℝ)*V 1 at h₂
  rw [hcal, constitutiveBallVolume_value] at h₂
  rw [constitutiveBallVolume_value] at h₁
  change (4*π/3) * ((a s : ℝ≥0) : ℝ)^3 = (s:ℝ) * V 1 at h₁
  change (4*π/3) * (L:ℝ)^3 = (L:ℝ) * V 1 at h₂
  have hLc : (0:ℝ) < L := hL
  have hπ : 4*π/3 ≠ 0 := by positivity
  have he : (4*π/3)*((L:ℝ)*((a s : ℝ≥0):ℝ)^3) = (4*π/3)*((L:ℝ)*((L:ℝ)^2*(s:ℝ))) := by
    linear_combination (L:ℝ)*h₁ - (s:ℝ)*h₂
  exact mul_left_cancel₀ hLc.ne' (mul_left_cancel₀ hπ he)

theorem constitutive_volume_exponents {a L s : ℝ} (ha : 0 ≤ a) (hL : 0 < L) (hs : 0 < s)
    (hc : a^3 = L^2*s) :
    a/L = (s/L)^((1:ℝ)/3) ∧ a^2/L^2 = (s/L)^((2:ℝ)/3) := by
  have hv : (a/L)^3 = s/L := by rw [div_pow, hc]; field_simp
  have h0 : 0 ≤ a/L := div_nonneg ha hL.le
  have h1 : a/L = (s/L)^((1:ℝ)/3) := by
    have he := Real.rpow_mul h0 3 ((1:ℝ)/3)
    norm_num at he
    simpa only [← hv] using he
  refine ⟨h1, ?_⟩
  rw [← div_pow, h1, ← Real.rpow_mul_natCast (div_nonneg hs.le hL.le)]
  congr 1
  norm_num

end UV
