import UV.FurtherShellBoundary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! Positive timelike shell Jacobian under a boost along a genuine
unit spatial axis. The transverse momentum stays fixed. -/

noncomputable section

open Filter Set MeasureTheory
open scoped ENNReal InnerProductSpace

namespace UV.SectorPlane

/-- Positive shell frequency at squared transverse mass (d). -/
def axialFrequency (d x : ℝ) : ℝ := Real.sqrt (d+x^2)

theorem axialFrequency_pos {d : ℝ} (hd : 0 < d) (x : ℝ) : 0 < axialFrequency d x :=
  Real.sqrt_pos.mpr (by positivity)

theorem axialFrequency_sq {d : ℝ} (hd : 0 ≤ d) (x : ℝ) :
    axialFrequency d x ^ 2 = d+x^2 := Real.sq_sqrt (by positivity)

def axialBoostCoordinate (d t x : ℝ) : ℝ :=
  Real.cosh t * x + Real.sinh t * axialFrequency d x

def axialBoostFrequency (d t x : ℝ) : ℝ :=
  Real.cosh t * axialFrequency d x + Real.sinh t * x

theorem axialBoostFrequency_pos {d : ℝ} (hd : 0 < d) (t x : ℝ) :
    0 < axialBoostFrequency d t x := by
  have hE := axialFrequency_pos hd x
  have hC := Real.cosh_pos t
  have hx : |x| < axialFrequency d x := by
    apply (sq_lt_sq₀ (abs_nonneg _) hE.le).mp
    rw [sq_abs, axialFrequency_sq hd.le]
    linarith
  have hS : |Real.sinh t| < Real.cosh t := by
    apply (sq_lt_sq₀ (abs_nonneg _) hC.le).mp
    rw [sq_abs]
    linarith [Real.cosh_sq_sub_sinh_sq t]
  have hsmall : |Real.sinh t * x| < Real.cosh t * axialFrequency d x := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hx.le (abs_nonneg _)).trans_lt
      (mul_lt_mul_of_pos_right hS hE)
  unfold axialBoostFrequency
  linarith [neg_abs_le (Real.sinh t*x)]

theorem axialBoostFrequency_on_shell {d : ℝ} (hd : 0 < d) (t x : ℝ) :
    axialFrequency d (axialBoostCoordinate d t x) = axialBoostFrequency d t x := by
  have hE := axialFrequency_sq hd.le x
  have hC := Real.cosh_sq_sub_sinh_sq t
  have h := axialBoostFrequency_pos hd t x
  have hAx := axialFrequency_pos hd (axialBoostCoordinate d t x)
  apply (sq_eq_sq₀ hAx.le h.le).mp
  rw [axialFrequency_sq hd.le]
  dsimp only [axialBoostFrequency, axialBoostCoordinate]
  linear_combination -(Real.cosh t^2 - Real.sinh t^2)*hE - d * hC

theorem axialBoostCoordinate_inverse {d : ℝ} (hd : 0 < d) (t x : ℝ) :
    axialBoostCoordinate d (-t) (axialBoostCoordinate d t x) = x := by
  change Real.cosh (-t) * axialBoostCoordinate d t x +
    Real.sinh (-t) * axialFrequency d (axialBoostCoordinate d t x) = x
  rw [Real.cosh_neg, Real.sinh_neg, axialBoostFrequency_on_shell hd]
  unfold axialBoostCoordinate axialBoostFrequency
  linear_combination x*Real.cosh_sq_sub_sinh_sq t

theorem axialBoostCoordinate_bijective {d : ℝ} (hd : 0 < d) (t : ℝ) :
    Function.Bijective (axialBoostCoordinate d t) := by
  refine ⟨fun x y h => ?_, fun x => ?_⟩
  · simpa only [axialBoostCoordinate_inverse hd] using congrArg (axialBoostCoordinate d (-t)) h
  · exact ⟨axialBoostCoordinate d (-t) x, by
      simpa only [neg_neg] using (axialBoostCoordinate_inverse hd (-t) x)⟩

/-- Axial derivative of the exact mass-shell boost. -/
theorem axialBoostCoordinate_hasDerivAt {d : ℝ} (hd : 0 < d) (t x : ℝ) :
    HasDerivAt (axialBoostCoordinate d t)
      (axialBoostFrequency d t x / axialFrequency d x) x := by
  have hE := axialFrequency_pos hd x
  have h := (hasDerivAt_const x d).add ((hasDerivAt_id x).pow 2)
  have h2 : HasDerivAt (axialFrequency d) (x/axialFrequency d x) x := by
    convert h.sqrt (by positivity : d+x^2 ≠ 0) using 1
    simp only [id_eq, Pi.add_apply, Pi.pow_apply, zero_add, Nat.reduceSub, pow_one, mul_one]
    change x / axialFrequency d x = 2*x/(2*axialFrequency d x)
    field_simp
  have h3 := (((hasDerivAt_id x).const_mul (Real.cosh t))).add
    (h2.const_mul (Real.sinh t))
  convert h3 using 1
  unfold axialBoostFrequency
  field_simp

/-- The invariant positive-frequency scalar mass-shell coefficient at
fixed transverse momentum is preserved by exact axial boosts. -/
theorem axialBoost_lintegral_shellWeight {d : ℝ} (hd : 0 < d) (t : ℝ) (g : ℝ → ℝ≥0∞) :
    (∫⁻ x, ENNReal.ofReal ((2*axialFrequency d x)⁻¹) * g (axialBoostCoordinate d t x)) =
      ∫⁻ x, ENNReal.ofReal ((2*axialFrequency d x)⁻¹) * g x := by
  have hBij := axialBoostCoordinate_bijective hd t
  have h := lintegral_image_eq_lintegral_abs_deriv_mul
    (s := (univ : Set ℝ)) MeasurableSet.univ
    (fun x _ => (axialBoostCoordinate_hasDerivAt hd t x).hasDerivWithinAt)
    hBij.1.injOn (fun x => ENNReal.ofReal ((2*axialFrequency d x)⁻¹)*g x)
  rw [image_univ, hBij.2.range_eq, Measure.restrict_univ] at h
  rw [h]
  apply lintegral_congr
  intro x
  have hE := axialFrequency_pos hd x
  have hF := axialBoostFrequency_pos hd t x
  rw [abs_of_pos (div_pos hF hE), axialBoostFrequency_on_shell hd, ← mul_assoc,
    ← ENNReal.ofReal_mul (div_nonneg hF.le hE.le)]
  have he : (axialBoostFrequency d t x / axialFrequency d x) *
      (2*axialBoostFrequency d t x)⁻¹ = (2*axialFrequency d x)⁻¹ := by
    field_simp
  rw [he]

/-- A fixed-plane signed carrier stores the oriented positive shell
frequency. The transverse momentum vector is unchanged and uses a
unit axis, so the boost does not change the sector's carrier unit. -/
theorem axialBoost_physicalShellPoint {E : Type*} [NormedAddCommGroup E]
    (diamond : Plane E) (n : UnitVector Spatial) (q : Spatial)
    (hq : ⟪(n : Spatial), q⟫_ℝ = 0) {m : ℝ} (hm : 0 < m) (t x : ℝ) :
    let d := m^2 + ‖q‖^2
    let x' := axialBoostCoordinate d t x
    diamond.physicalShellPoint m (x' • (n : Spatial)+q) =
      (sectorSign diamond.s * axialBoostFrequency d t x, x' • (n : Spatial)+q) := by
  dsimp only
  let d := m^2+‖q‖^2
  let x' := axialBoostCoordinate d t x
  let p := x' • (n : Spatial)+q
  have hFreq : shellFrequency m p = axialBoostFrequency d t x := by
    rw [← axialBoostFrequency_on_shell (by positivity : 0 < d)]
    change shellFrequency m p = axialFrequency d x'
    unfold shellFrequency axialFrequency
    congr 1
    unfold p
    rw [norm_add_sq_real, norm_smul, n.property, mul_one, Real.norm_eq_abs, sq_abs,
      real_inner_smul_left, hq]
    unfold d
    ring
  exact congrArg (fun u => (sectorSign diamond.s * u, p)) hFreq


end UV.SectorPlane
