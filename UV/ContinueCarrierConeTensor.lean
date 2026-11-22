import UV.ContinuationSectorPlane
import UV.ResumeConeSquareRadial

/-! Exact quadratic numerator channels at the cone tip. The four-vector uses
its intrinsic Euclidean polar norm on one selected plane. These algebraic
identities retain the normalized carrier direction and do not change either
side of the directed pole prescription. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Set Filter
open scoped Topology Interval

abbrev IntrinsicFour := EuclideanSpace ℝ (Fin 4)

/-- Minkowski square in the intrinsic four-coordinate chart. -/
def intrinsicShell (q : IntrinsicFour) : ℝ := 2 * q 0 ^ 2 - ‖q‖ ^ 2

/-- The intrinsic Lorentzian contraction uses the same time and three
spatial slots as the normalized polar four-vector. -/
theorem intrinsicShell_coordinates (q : IntrinsicFour) :
    intrinsicShell q = q 0 ^ 2 - ∑ i : Fin 3, q i.succ ^ 2 := by
  have h := EuclideanSpace.norm_sq_eq q
  rw [Fin.sum_univ_succ] at h
  simp only [Real.norm_eq_abs, sq_abs] at h
  unfold intrinsicShell
  linarith

/-- The angular cone coordinate of an actual norm-one four-vector. -/
def coneCoordinate (ω : UnitVector IntrinsicFour) : ℝ := 2 * ω.val 0 ^ 2 - 1

theorem intrinsic_polar_shell (r : ℝ) (ω : UnitVector IntrinsicFour) :
    intrinsicShell (r • ω.val) = r ^ 2 * coneCoordinate ω := by
  unfold intrinsicShell coneCoordinate
  rw [norm_smul, ω.property, mul_one, Real.norm_eq_abs, sq_abs]
  change 2 * (r * ω.val 0) ^ 2 - r ^ 2 = _
  ring

theorem intrinsic_polar_numerator (r : ℝ) (ω : UnitVector IntrinsicFour) (μ ν : Fin 4) :
    (r • ω.val) μ * (r • ω.val) ν = r ^ 2 * (ω.val μ * ω.val ν) := by
  change (r * ω.val μ) * (r * ω.val ν) = _
  ring

theorem unit_four_coordinate_bound (ω : UnitVector IntrinsicFour) (μ : Fin 4) :
    |ω.val μ| ≤ 1 := by
  simpa [Real.norm_eq_abs, ω.property] using PiLp.norm_apply_le ω.val μ

theorem quadratic_angular_numerator_bound (ω : UnitVector IntrinsicFour) (μ ν : Fin 4) :
    |ω.val μ * ω.val ν| ≤ 1 := by
  rw [abs_mul]
  exact (mul_le_mul (unit_four_coordinate_bound ω μ) (unit_four_coordinate_bound ω ν)
    (abs_nonneg _) zero_le_one).trans_eq (mul_one 1)

theorem coneCoordinate_bounds (ω : UnitVector IntrinsicFour) :
    -1 ≤ coneCoordinate ω ∧ coneCoordinate ω ≤ 1 := by
  have h := unit_four_coordinate_bound ω 0
  unfold coneCoordinate
  constructor
  · nlinarith [sq_nonneg (ω.val 0)]
  · have hsq : ω.val 0 ^ 2 ≤ 1 := by nlinarith [abs_le.mp h]
    linarith

/-- The temporal squared coordinate is an exact affine cone-coordinate weight. -/
theorem temporal_angular_weight (ω : UnitVector IntrinsicFour) :
    ω.val 0 ^ 2 = (1 + coneCoordinate ω) / 2 := by unfold coneCoordinate; ring

/-- The sum of the three spatial squares is the complementary affine weight. -/
theorem spatial_angular_weight (ω : UnitVector IntrinsicFour) :
    (∑ i : Fin 3, ω.val i.succ ^ 2) = (1 - coneCoordinate ω) / 2 := by
  have hnorm := EuclideanSpace.norm_sq_eq ω.val
  rw [ω.property, one_pow, Fin.sum_univ_succ] at hnorm
  simp only [Real.norm_eq_abs, sq_abs] at hnorm
  unfold coneCoordinate
  linarith

/-- The polynomial numerator of a longitudinal line contributes two powers
of polar radius at the same finite pole height. -/
theorem longitudinal_polar_scaling {r h : ℝ} (hr : 0 < r) (η : ℝ)
    (ω : UnitVector IntrinsicFour) (μ ν : Fin 4) :
    ((r • ω.val) μ * (r • ω.val) ν : ℂ) *
        (((intrinsicShell (r • ω.val) : ℝ) : ℂ) + Complex.I * ((η * h : ℝ) : ℂ))⁻¹ ^ 2 =
      (r : ℂ)⁻¹ ^ 2 * ((ω.val μ * ω.val ν : ℝ) : ℂ) *
        (((coneCoordinate ω : ℝ) : ℂ) + Complex.I * ((η * (h / r ^ 2) : ℝ) : ℂ))⁻¹ ^ 2 := by
  rw [← Complex.ofReal_mul ((r • ω.val) μ) ((r • ω.val) ν),
    intrinsic_polar_numerator, intrinsic_polar_shell]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have he : ((r ^ 2 * coneCoordinate ω : ℝ) : ℂ) + Complex.I * ((η * h : ℝ) : ℂ) =
      (r : ℂ) ^ 2 * (((coneCoordinate ω : ℝ) : ℂ) +
        Complex.I * ((η * (h / r ^ 2) : ℝ) : ℂ)) := by
    push_cast
    field_simp
  rw [he, mul_inv_rev, mul_pow]
  push_cast
  field_simp

/-- The normalized scalar angular density in the cone coordinate U=cos θ. -/
def coneAngularWeight (θ : ℝ) : ℝ := (1 - Real.cos θ) / Real.pi

def coneAngularPole (η t θ : ℝ) : ℂ :=
  ((Real.cos θ : ℂ) + Complex.I * ((η * t : ℝ) : ℂ))⁻¹

def coneAngularFirst (η t : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..Real.pi, coneAngularWeight θ • coneAngularPole η t θ

def coneAngularSecond (η t : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..Real.pi, coneAngularWeight θ • coneAngularPole η t θ ^ 2

/-- Temporal quadratic tensor channel before radial integration. -/
def coneTemporalSecond (η t : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..Real.pi, coneAngularWeight θ •
    (((1 + Real.cos θ) / 2 : ℝ) • coneAngularPole η t θ ^ 2)

/-- A spatial diagonal quadratic channel after the equal-coordinate angular
average on the three spatial slots. No arbitrary nonradial test is asserted. -/
def coneSpatialSecond (η t : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..Real.pi, coneAngularWeight θ •
    (((1 - Real.cos θ) / 6 : ℝ) • coneAngularPole η t θ ^ 2)

theorem coneAngularPole_continuous {η t : ℝ} (ht : 0 < t) (hη : η ^ 2 = 1) :
    Continuous (coneAngularPole η t) := by
  have hηne : η ≠ 0 := by intro h; simp [h] at hη
  apply ((Complex.continuous_ofReal.comp Real.continuous_cos).add continuous_const).inv₀
  intro θ hzero
  have h := congrArg Complex.im hzero
  simp only [Function.comp_apply, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.ofReal_re, Complex.I_im, zero_mul, one_mul, zero_add, Complex.zero_im] at h
  exact (mul_ne_zero hηne ht.ne') h

theorem coneAngularPole_identity {η t : ℝ} (ht : 0 < t) (hη : η ^ 2 = 1) (θ : ℝ) :
    (Real.cos θ : ℂ) * coneAngularPole η t θ ^ 2 =
      coneAngularPole η t θ - Complex.I * ((η * t : ℝ) : ℂ) * coneAngularPole η t θ ^ 2 := by
  have hηne : η ≠ 0 := by intro h; simp [h] at hη
  have hd : ((Real.cos θ : ℂ) + Complex.I * ((η * t : ℝ) : ℂ)) ≠ 0 := by
    intro hz
    have h := congrArg Complex.im hz
    have hm : η * t = 0 := by simpa using h
    exact (mul_ne_zero hηne ht.ne') hm
  unfold coneAngularPole
  field_simp
  ring

/-- The exact temporal quadratic tensor coefficient is determined by the
scalar first and second averages, with the same signed pole side. -/
theorem coneTemporalSecond_identity {η t : ℝ} (ht : 0 < t) (hη : η ^ 2 = 1) :
    coneTemporalSecond η t =
      ((1 - Complex.I * ((η * t : ℝ) : ℂ)) * coneAngularSecond η t + coneAngularFirst η t) / 2 := by
  have hw : Continuous coneAngularWeight := by unfold coneAngularWeight; fun_prop
  have hp := coneAngularPole_continuous ht hη
  have hi₂ := (hw.smul (hp.pow 2)).intervalIntegrable (μ := volume) 0 Real.pi
  have hi₁ := (hw.smul hp).intervalIntegrable (μ := volume) 0 Real.pi
  have he (θ : ℝ) : coneAngularWeight θ •
      (((1 + Real.cos θ) / 2 : ℝ) • coneAngularPole η t θ ^ 2) =
      ((1 - Complex.I * ((η * t : ℝ) : ℂ)) *
        (coneAngularWeight θ • coneAngularPole η t θ ^ 2) +
        coneAngularWeight θ • coneAngularPole η t θ) / 2 := by
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one,
      Complex.ofReal_ofNat]
    linear_combination ((coneAngularWeight θ : ℂ) / 2) * coneAngularPole_identity ht hη θ
  unfold coneTemporalSecond
  simp_rw [he]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add (hi₂.const_mul _) hi₁, intervalIntegral.integral_const_mul]
  rfl

/-- The exact equal-coordinate spatial diagonal coefficient. -/
theorem coneSpatialSecond_identity {η t : ℝ} (ht : 0 < t) (hη : η ^ 2 = 1) :
    coneSpatialSecond η t =
      ((1 + Complex.I * ((η * t : ℝ) : ℂ)) * coneAngularSecond η t - coneAngularFirst η t) / 6 := by
  have hw : Continuous coneAngularWeight := by unfold coneAngularWeight; fun_prop
  have hp := coneAngularPole_continuous ht hη
  have hi₂ := (hw.smul (hp.pow 2)).intervalIntegrable (μ := volume) 0 Real.pi
  have hi₁ := (hw.smul hp).intervalIntegrable (μ := volume) 0 Real.pi
  have he (θ : ℝ) : coneAngularWeight θ •
      (((1 - Real.cos θ) / 6 : ℝ) • coneAngularPole η t θ ^ 2) =
      ((1 + Complex.I * ((η * t : ℝ) : ℂ)) *
        (coneAngularWeight θ • coneAngularPole η t θ ^ 2) -
        coneAngularWeight θ • coneAngularPole η t θ) / 6 := by
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_ofNat]
    linear_combination -((coneAngularWeight θ : ℂ) / 6) * coneAngularPole_identity ht hη θ
  unfold coneSpatialSecond
  simp_rw [he]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_sub (hi₂.const_mul _) hi₁, intervalIntegral.integral_const_mul]
  rfl

/-- Euclidean contraction of the quadratic channels recovers the original
uncontracted scalar square. -/
theorem cone_tensor_euclidean_trace {η t : ℝ} (ht : 0 < t) (hη : η ^ 2 = 1) :
    coneTemporalSecond η t + 3 * coneSpatialSecond η t = coneAngularSecond η t := by
  rw [coneTemporalSecond_identity ht hη, coneSpatialSecond_identity ht hη]
  ring

/-- Lorentzian contraction has the exact numerator U, hence one simple
angular resolvent minus the finite-height remainder of the square. -/
theorem cone_tensor_lorentz_trace {η t : ℝ} (ht : 0 < t) (hη : η ^ 2 = 1) :
    coneTemporalSecond η t - 3 * coneSpatialSecond η t =
      coneAngularFirst η t - Complex.I * ((η * t : ℝ) : ℂ) * coneAngularSecond η t := by
  rw [coneTemporalSecond_identity ht hη, coneSpatialSecond_identity ht hη]
  ring

/-- The closed scalar first average at a signed imaginary angular pole. -/
def coneFirstClosed (η t : ℝ) : ℂ :=
  ((t : ℂ) - Complex.I * (η : ℂ)) / (Real.sqrt (1 + t ^ 2) : ℂ) - 1

/-- The closed scalar double-pole average. -/
def coneSecondClosed (η t : ℝ) : ℂ :=
  (Complex.I * (η : ℂ) - (t : ℂ)) / (Real.sqrt (1 + t ^ 2) : ℂ) ^ 3

def coneTemporalClosed (η t : ℝ) : ℂ :=
  ((1 - Complex.I * ((η * t : ℝ) : ℂ)) * coneSecondClosed η t + coneFirstClosed η t) / 2

def coneSpatialClosed (η t : ℝ) : ℂ :=
  ((1 + Complex.I * ((η * t : ℝ) : ℂ)) * coneSecondClosed η t - coneFirstClosed η t) / 6

theorem cone_normalized_numerator_norm {η : ℝ} (hη : η ^ 2 = 1) (t : ℝ) :
    ‖Complex.I * (η : ℂ) - (t : ℂ)‖ = Real.sqrt (1 + t ^ 2) := by
  rw [Complex.norm_def]
  congr 1
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero,
    Complex.sub_im, Complex.mul_im, one_mul, zero_sub, zero_add]
  nlinarith

theorem coneSecondClosed_norm {η : ℝ} (hη : η ^ 2 = 1) (t : ℝ) :
    ‖coneSecondClosed η t‖ = 1 / (1 + t ^ 2) := by
  have hs : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs2 := Real.sq_sqrt (show 0 ≤ 1 + t ^ 2 by positivity)
  unfold coneSecondClosed
  rw [norm_div, norm_pow, cone_normalized_numerator_norm hη, Complex.norm_real,
    Real.norm_of_nonneg hs.le]
  field_simp
  nlinarith

theorem coneSecondClosed_norm_le {η : ℝ} (hη : η ^ 2 = 1) (t : ℝ) :
    ‖coneSecondClosed η t‖ ≤ 1 := by
  rw [coneSecondClosed_norm hη]
  exact (div_le_one (by positivity : 0 < 1 + t ^ 2)).mpr (by nlinarith [sq_nonneg t])

theorem coneFirstClosed_norm_le {η : ℝ} (hη : η ^ 2 = 1) (t : ℝ) :
    ‖coneFirstClosed η t‖ ≤ 2 := by
  have hs : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hn : ‖(t : ℂ) - Complex.I * (η : ℂ)‖ = Real.sqrt (1 + t ^ 2) := by
    rw [norm_sub_rev]
    exact cone_normalized_numerator_norm hη t
  have hunit : ‖((t : ℂ) - Complex.I * (η : ℂ)) / (Real.sqrt (1 + t ^ 2) : ℂ)‖ = 1 := by
    rw [norm_div, hn, Complex.norm_real, Real.norm_of_nonneg hs.le, div_self hs.ne']
  unfold coneFirstClosed
  calc
    _ ≤ ‖((t : ℂ) - Complex.I * (η : ℂ)) / (Real.sqrt (1 + t ^ 2) : ℂ)‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le _ _
    _ = 2 := by rw [hunit]; norm_num

theorem cone_shift_second_norm_le {η t : ℝ} (ht : 0 ≤ t) (hη : η ^ 2 = 1) :
    ‖Complex.I * ((η * t : ℝ) : ℂ) * coneSecondClosed η t‖ ≤ 1 := by
  have hηnorm : |η| = 1 := by nlinarith [sq_abs η, abs_nonneg η]
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, hηnorm, abs_of_nonneg ht, one_mul, coneSecondClosed_norm hη]
  rw [one_div, ← div_eq_mul_inv]
  exact (div_le_one (by positivity : 0 < 1 + t ^ 2)).mpr (by nlinarith [sq_nonneg (t - 1)])

/-- Uniform temporal coefficient, before multiplying by the restored radial
power from the quadratic numerator. -/
theorem coneTemporalClosed_norm_le {η t : ℝ} (ht : 0 ≤ t) (hη : η ^ 2 = 1) :
    ‖coneTemporalClosed η t‖ ≤ 2 := by
  have hB := coneSecondClosed_norm_le hη t
  have hA := coneFirstClosed_norm_le hη t
  have hz := cone_shift_second_norm_le ht hη
  have hm : ‖(1 - Complex.I * ((η * t : ℝ) : ℂ)) * coneSecondClosed η t‖ ≤ 2 := by
    rw [sub_mul, one_mul]
    exact (norm_sub_le _ _).trans (by linarith)
  unfold coneTemporalClosed
  rw [norm_div]
  norm_num only [Complex.norm_ofNat]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    ((norm_add_le _ _).trans (by linarith))

/-- Uniform coefficient for any one of the equal spatial diagonal channels. -/
theorem coneSpatialClosed_norm_le {η t : ℝ} (ht : 0 ≤ t) (hη : η ^ 2 = 1) :
    ‖coneSpatialClosed η t‖ ≤ 2 / 3 := by
  have hB := coneSecondClosed_norm_le hη t
  have hA := coneFirstClosed_norm_le hη t
  have hz := cone_shift_second_norm_le ht hη
  have hm : ‖(1 + Complex.I * ((η * t : ℝ) : ℂ)) * coneSecondClosed η t‖ ≤ 2 := by
    rw [add_mul, one_mul]
    exact (norm_add_le _ _).trans (by linarith)
  unfold coneSpatialClosed
  rw [norm_div]
  norm_num only [Complex.norm_ofNat]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 6)).mpr
    ((norm_sub_le _ _).trans (by linarith))

/-- The quadratic temporal channel restores the locally integrable radial
majorant 2r after including the four-dimensional polar Jacobian. -/
theorem coneTemporalClosed_radial_bound {η h r : ℝ} (hη : η ^ 2 = 1)
    (hh : 0 ≤ h) (hr : 0 < r) :
    ‖(r : ℂ) * coneTemporalClosed η (h / r ^ 2)‖ ≤ 2 * r := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
  have ht : 0 ≤ h / r ^ 2 := div_nonneg hh (sq_nonneg r)
  nlinarith [mul_le_mul_of_nonneg_left (coneTemporalClosed_norm_le ht hη) hr.le]

theorem coneSpatialClosed_radial_bound {η h r : ℝ} (hη : η ^ 2 = 1)
    (hh : 0 ≤ h) (hr : 0 < r) :
    ‖(r : ℂ) * coneSpatialClosed η (h / r ^ 2)‖ ≤ (2 / 3) * r := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
  have ht : 0 ≤ h / r ^ 2 := div_nonneg hh (sq_nonneg r)
  nlinarith [mul_le_mul_of_nonneg_left (coneSpatialClosed_norm_le ht hη) hr.le]

/-- Radial integrability is independent of the positive reference pole height. -/
theorem coneTemporalClosed_radial_integrable {η h R : ℝ} (hη : η ^ 2 = 1)
    (hh : 0 ≤ h) :
    IntegrableOn (fun r : ℝ => (r : ℂ) * coneTemporalClosed η (h / r ^ 2)) (Ioc 0 R) := by
  have hi : IntegrableOn (fun r : ℝ => 2 * |r|) (Ioc 0 R) :=
    ((continuous_const.mul continuous_id.abs).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  apply hi.mono'
  · have hm : Measurable (fun r : ℝ => (r : ℂ) * coneTemporalClosed η (h / r ^ 2)) := by
      unfold coneTemporalClosed coneFirstClosed coneSecondClosed
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    simpa only [abs_of_pos hr.1] using coneTemporalClosed_radial_bound hη hh hr.1

theorem coneSpatialClosed_radial_integrable {η h R : ℝ} (hη : η ^ 2 = 1)
    (hh : 0 ≤ h) :
    IntegrableOn (fun r : ℝ => (r : ℂ) * coneSpatialClosed η (h / r ^ 2)) (Ioc 0 R) := by
  have hi : IntegrableOn (fun r : ℝ => (2 / 3) * |r|) (Ioc 0 R) :=
    ((continuous_const.mul continuous_id.abs).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  apply hi.mono'
  · have hm : Measurable (fun r : ℝ => (r : ℂ) * coneSpatialClosed η (h / r ^ 2)) := by
      unfold coneSpatialClosed coneFirstClosed coneSecondClosed
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    simpa only [abs_of_pos hr.1] using coneSpatialClosed_radial_bound hη hh hr.1

/-- Any bounded measurable compact radial test can multiply the temporal channel. -/
theorem coneTemporalClosed_radial_test_integrable {η h R : ℝ} (hη : η ^ 2 = 1)
    (hh : 0 ≤ h) {χ : ℝ → ℂ} (hχ : Measurable χ) (hB : ∃ C, ∀ r, ‖χ r‖ ≤ C) :
    IntegrableOn (fun r => χ r * ((r : ℂ) * coneTemporalClosed η (h / r ^ 2))) (Ioc 0 R) :=
  (coneTemporalClosed_radial_integrable hη hh).bdd_mul hχ.aestronglyMeasurable hB

/-- The analogous spatial diagonal channel obeys the same full-height control. -/
theorem coneSpatialClosed_radial_test_integrable {η h R : ℝ} (hη : η ^ 2 = 1)
    (hh : 0 ≤ h) {χ : ℝ → ℂ} (hχ : Measurable χ) (hB : ∃ C, ∀ r, ‖χ r‖ ≤ C) :
    IntegrableOn (fun r => χ r * ((r : ℂ) * coneSpatialClosed η (h / r ^ 2))) (Ioc 0 R) :=
  (coneSpatialClosed_radial_integrable hη hh).bdd_mul hχ.aestronglyMeasurable hB

end UV.SectorPlane
