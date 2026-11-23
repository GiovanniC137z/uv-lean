import UV.ContinueRoughCurvatureBound
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! The original radial interval and its exact substitution to the
positive logarithmic-depth coordinate for the quartic collar. -/

noncomputable section
open Real MeasureTheory Set Filter
open scoped ENNReal BigOperators
namespace UV.RoughCurvature

def collarRadius (z : ℝ) : ℝ := (1+3*z)^(-1/3:ℝ)

theorem collarRadius_in_unit_interval {z : ℝ} (hz : 0 < z) :
    collarRadius z ∈ Ioo 0 1 := by
  have h : 1 < 1+3*z := by linarith
  exact ⟨rpow_pos_of_pos (zero_lt_one.trans h) _, rpow_lt_one_of_one_lt_of_neg h (by norm_num)⟩

theorem collarDepth_in_positive_halfline {r : ℝ} (hr : r ∈ Ioo 0 1) : 0 < collarDepth r := by
  have h : 0 < r^3 := pow_pos hr.1 _
  have h₁ : r^3 < 1 := by simpa using pow_lt_pow_left₀ hr.2 hr.1.le (by norm_num : (3:ℕ) ≠ 0)
  unfold collarDepth
  exact div_pos (sub_pos.2 (one_lt_inv₀ h |>.2 h₁)) (by norm_num)

theorem collarRadius_depth {r : ℝ} (hr : 0 < r) : collarRadius (collarDepth r) = r := by
  unfold collarRadius collarDepth
  have hpow : (r^3)⁻¹ = r^(-3:ℝ) := by rw [rpow_neg hr.le, show (3:ℝ) = ((3:ℕ):ℝ) from rfl, rpow_natCast]
  rw [show 1+3*(((r^3)⁻¹ - 1)/3) = (r^3)⁻¹ by ring, hpow, ← rpow_mul hr.le,
    show -(3:ℝ)*(-1/3)=1 by ring, rpow_one]

theorem collarDepth_radius {z : ℝ} (hz : 0 ≤ z) : collarDepth (collarRadius z) = z := by
  have hB : 0 < 1+3*z := by linarith
  unfold collarDepth collarRadius
  rw [← rpow_mul_natCast hB.le, show (-1/3:ℝ)*(3:ℕ) = -1 by norm_num,
    rpow_neg_one, inv_inv]
  ring

theorem collar_radius_hasDerivAt {z : ℝ} (hz : 0 < z) :
    HasDerivAt collarRadius (-((1+3*z)^(-4/3:ℝ))) z := by
  have hB : 0 < 1+3*z := by linarith
  have hl : HasDerivAt (fun s : ℝ => 1+3*s) 3 z := by
    convert ((hasDerivAt_id z).const_mul 3).const_add 1 using 1
    ring
  have hs := (hasDerivAt_rpow_const (p := (-1/3:ℝ)) (Or.inl hB.ne')).comp z hl
  convert hs using 1
  rw [show (-1/3:ℝ)-1 = -4/3 by ring]
  ring

/-- The two Green endpoint factors contribute r⁴ and the vertex r⁻²
leaves r² dr. Its exact transformed measure is (1+3z)⁻² dz. -/
theorem collar_weighted_radial_change (f : ℝ → ℝ≥0∞) :
    (∫⁻ r in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (r^2) * f (collarDepth r)) =
      ∫⁻ z in Set.Ioi (0:ℝ), ENNReal.ofReal (collarVertexWeight z) * f z := by
  have hrange : collarRadius '' Ioi (0:ℝ) = Ioo 0 1 := by
    ext r
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact collarRadius_in_unit_interval hz
    · intro hr
      exact ⟨collarDepth r,collarDepth_in_positive_halfline hr,collarRadius_depth hr.1⟩
  have hinj : InjOn collarRadius (Ioi (0:ℝ)) := by
    intro x hx y hy h
    simpa only [collarDepth_radius hx.le,collarDepth_radius hy.le] using congrArg collarDepth h
  rw [← hrange, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun z hz => (collar_radius_hasDerivAt hz).hasDerivWithinAt) hinj]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  have hB : 0 < 1+3*z := by linarith [mem_Ioi.mp hz]
  rw [collarDepth_radius hz.le, abs_neg, abs_of_nonneg (rpow_nonneg hB.le _),
    ← mul_assoc, ← ENNReal.ofReal_mul (rpow_nonneg hB.le _), collarRadius,
    ← rpow_mul_natCast hB.le, ← rpow_add hB, collarVertexWeight]
  congr 2
  norm_num

/-- The neutral inverse of -d²/dr²+2/r² has the regular left
solution r² and the right Dirichlet solution r⁻¹−r². -/
def neutralCollarGreen (r s : ℝ) : ℝ :=
  (min r s)^2*((max r s)⁻¹-(max r s)^2)/3

theorem neutral_collar_green_exact {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    neutralCollarGreen r s = r^2*s^2 * collarModeGreen 0 (collarDepth r) (collarDepth s) := by
  wlog h : r ≤ s generalizing r s
  · rw [neutralCollarGreen, min_comm r s,max_comm r s, ← neutralCollarGreen,this hs hr (le_of_not_ge h),
      collarModeGreen, collarModeGreen, if_pos rfl, if_pos rfl, min_comm (collarDepth s), mul_comm (s^2)]
  have hD : collarDepth s ≤ collarDepth r := by
    have hInv := inv_anti₀ (pow_pos hr 3) (pow_le_pow_left₀ hr.le h 3)
    unfold collarDepth
    linarith
  simp only [neutralCollarGreen, collarModeGreen, if_true, min_eq_left h, max_eq_right h, min_eq_right hD]
  unfold collarDepth
  field_simp

end UV.RoughCurvature
