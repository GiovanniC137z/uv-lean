import UV.AdvanceStableSquare

/-! The inverse root primitive of the fractional singularity on
the massless stable-half branch of a fixed sector plane. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.RevisionSpectrum
open scoped Topology Interval

variable {E : Type*} [NormedAddCommGroup E]

private theorem Plane.stable_shell_root_argument_slit (diamond : Plane E) (ε : Evolution)
    (h : Height) (w : ℝ) :
    -(diamond.shiftedShellCoefficient ε h w) ∈ Complex.slitPlane := by
  have hη : diamond.eta ε ≠ 0 := by
    intro he
    simpa [he] using diamond.eta_sq ε
  apply Complex.mem_slitPlane_iff.mpr
  right
  have hprod := mul_ne_zero hη h.property.ne'
  simpa [Plane.shiftedShellCoefficient, Complex.mul_im] using hprod

theorem Plane.stable_shell_inverse_root_hasDerivAt (diamond : Plane E) (ε : Evolution)
    (h : Height) (w : ℝ) :
    HasDerivAt (fun u => (diamond.stableShellRoot ε h u)⁻¹)
      ((2 : ℂ)⁻¹ * ((diamond.stableShellRoot ε h w) ^ 3)⁻¹) w := by
  let W (u : ℝ) := -(diamond.shiftedShellCoefficient ε h u)
  have hW : HasDerivAt W (-1 : ℂ) w := by
    change HasDerivAt (fun u : ℝ => -((u : ℂ) + Complex.I *
      ((diamond.eta ε * (h : ℝ) : ℝ) : ℂ))) (-1 : ℂ) w
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, Pi.neg_apply] using
      ((Complex.ofRealCLM.hasDerivAt (x := w)).add_const
        (Complex.I * ((diamond.eta ε * (h : ℝ) : ℝ) : ℂ))).neg
  have hslit : W w ∈ Complex.slitPlane := diamond.stable_shell_root_argument_slit ε h w
  have hP₀ : principalSqrt (W w) ≠ 0 := diamond.stable_shell_root_ne_zero ε h w
  have hP := ((principalSqrt_hasDerivAt hslit).fun_inv hP₀).comp w hW
  have hcpow : (2⁻¹ : ℂ) - 1 = -(2⁻¹ : ℂ) := by norm_num
  rw [hcpow, Complex.cpow_neg] at hP
  let s := diamond.stableShellRoot ε h w
  change HasDerivAt (fun u => (diamond.stableShellRoot ε h u)⁻¹)
    (-((2 : ℂ)⁻¹ * s⁻¹) / s ^ 2 * -1) w at hP
  convert hP using 1
  change (2 : ℂ)⁻¹ * (s ^ 3)⁻¹ = -((2 : ℂ)⁻¹ * s⁻¹) / s ^ 2 * -1
  simp only [neg_mul, mul_neg_one, neg_neg, div_eq_mul_inv]
  ring

/-- The derivative is taken in the dimensionless angular invariant,
whose physical shell invariant is r²u. -/
theorem Plane.stable_shell_inverse_root_angular_derivative (diamond : Plane E)
    (ε : Evolution) (h : Height) (r u : ℝ) :
    HasDerivAt (fun v => (diamond.stableShellRoot ε h (r ^ 2 * v))⁻¹)
      (((r ^ 2 / 2 : ℝ) : ℂ) * ((diamond.stableShellRoot ε h (r ^ 2 * u)) ^ 3)⁻¹) u := by
  have hd := (diamond.stable_shell_inverse_root_hasDerivAt ε h (r ^ 2 * u)).scomp u
    (show HasDerivAt (fun v : ℝ => r ^ 2 * v) (r ^ 2) u from by
      simpa using (hasDerivAt_id u).const_mul (r ^ 2))
  convert hd using 1
  simp only [Complex.real_smul]
  push_cast
  ring

theorem Plane.stable_shell_inverse_root_norm_le (diamond : Plane E) (ε : Evolution)
    (h : Height) {w : ℝ} (hw : w ≠ 0) :
    ‖(diamond.stableShellRoot ε h w)⁻¹‖ ≤ inverseRootAbs w := by
  have hwz : |w| ≤ ‖diamond.shiftedShellCoefficient ε h w‖ := by
    simpa only [Plane.shiftedShellCoefficient, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero,
      sub_zero, add_zero] using Complex.abs_re_le_norm (diamond.shiftedShellCoefficient ε h w)
  rw [norm_inv, Plane.stableShellRoot, principalSqrt_norm, norm_neg, inverseRootAbs]
  exact inv_anti₀ (Real.sqrt_pos.mpr (abs_pos.mpr hw)) (Real.sqrt_le_sqrt hwz)

theorem Plane.stable_shell_inverse_root_angular_norm_le (diamond : Plane E)
    (ε : Evolution) (h : Height) {r u : ℝ} (hr : 0 < r) (hu : u ≠ 0) :
    ‖(diamond.stableShellRoot ε h (r ^ 2 * u))⁻¹‖ ≤ r⁻¹ * inverseRootAbs u := by
  refine (diamond.stable_shell_inverse_root_norm_le ε h (mul_ne_zero (pow_ne_zero _ hr.ne') hu)).trans_eq ?_
  rw [inverseRootAbs, abs_mul, abs_of_nonneg (sq_nonneg r), Real.sqrt_mul (sq_nonneg r),
    Real.sqrt_sq hr.le, mul_inv, inverseRootAbs]

/-- Root boundary before inversion, with the sign outside the fixed
pole unit and the ordinary nonnegative root on each real side. -/
def stableShellBoundaryRoot (η w : ℝ) : ℂ :=
  (Real.sqrt (-w) : ℂ) - Complex.I * (η : ℂ) * (Real.sqrt w : ℂ)

private theorem spectralRootUpper_zero_formula (w : ℝ) :
    spectralRootUpper (-w) 0 = (Real.sqrt (-w) : ℂ) + Complex.I * (Real.sqrt w : ℂ) := by
  by_cases hw : 0 ≤ w
  · rw [spectralRootUpper_at_cut (neg_nonpos.mpr hw), neg_neg,
      Real.sqrt_eq_zero_of_nonpos (neg_nonpos.mpr hw)]
    simp [mul_comm Complex.I]
  · have hn : 0 ≤ -w := neg_nonneg.mpr (le_of_not_ge hw)
    unfold spectralRootUpper
    rw [show Real.sqrt ((-w) ^ 2 + (0 : ℝ) ^ 2) = -w by simpa using Real.sqrt_sq hn]
    simp [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hw)]

theorem stable_shell_boundary_root_norm (η : ℝ) (hη : η ^ 2 = 1) (w : ℝ) :
    ‖stableShellBoundaryRoot η w‖ = Real.sqrt |w| := by
  have he : |η| = 1 := (sq_eq_sq₀ (abs_nonneg _) zero_le_one).mp (by
    rw [sq_abs, hη, one_pow])
  by_cases hw : 0 ≤ w
  · simp [stableShellBoundaryRoot, Real.sqrt_eq_zero_of_nonpos (neg_nonpos.mpr hw),
      abs_of_nonneg hw, Complex.norm_real, Real.norm_eq_abs, he, abs_of_nonneg]
  · simp [stableShellBoundaryRoot, Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hw),
      abs_of_neg (lt_of_not_ge hw), Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]

theorem Plane.stable_shell_root_tendsto (diamond : Plane E) (ε : Evolution) (w : ℝ) :
    Tendsto (fun h : Height => diamond.stableShellRoot ε h w)
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 (stableShellBoundaryRoot (diamond.eta ε) w)) := by
  let H := (𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ))
  have hh : Tendsto (fun h : Height => (h : ℝ)) H (𝓝 (0 : ℝ)) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  have hη : diamond.eta ε = 1 ∨ diamond.eta ε = -1 :=
    eq_or_eq_neg_of_sq_eq_sq (diamond.eta ε) 1 (by simp)
  rcases hη with he | he
  · have ht := ((spectralRootUpper_continuous (-w)).star.continuousAt (x := 0)).tendsto.comp hh
    have hlim : star (spectralRootUpper (-w) 0) = stableShellBoundaryRoot (diamond.eta ε) w := by
      rw [spectralRootUpper_zero_formula]
      simp [stableShellBoundaryRoot, he, sub_eq_add_neg]
    rw [hlim] at ht
    refine ht.congr fun h => ?_
    have hEq : -(diamond.shiftedShellCoefficient ε h w) = ((-w : ℝ) : ℂ) - (h : ℂ) * Complex.I := by
      simp [Plane.shiftedShellCoefficient, he]
      ring
    rw [Plane.stableShellRoot, hEq, principalSqrt_lower_eq (-w) h.property]
    rfl
  · have ht := ((spectralRootUpper_continuous (-w)).continuousAt (x := 0)).tendsto.comp hh
    have hlim : spectralRootUpper (-w) 0 = stableShellBoundaryRoot (diamond.eta ε) w := by
      rw [spectralRootUpper_zero_formula]
      simp [stableShellBoundaryRoot, he, sub_eq_add_neg]
    rw [hlim] at ht
    refine ht.congr fun h => ?_
    have hEq : -(diamond.shiftedShellCoefficient ε h w) = ((-w : ℝ) : ℂ) + (h : ℂ) * Complex.I := by
      simp [Plane.shiftedShellCoefficient, he]
      ring
    rw [Plane.stableShellRoot, hEq, principalSqrt_upper_eq (-w) h.property]
    rfl

theorem Plane.stable_shell_inverse_root_tendsto (diamond : Plane E) (ε : Evolution)
    {w : ℝ} (hw : w ≠ 0) :
    Tendsto (fun h : Height => (diamond.stableShellRoot ε h w)⁻¹)
      ((𝓝[>] (0 : ℝ)).comap (fun h : Height => (h : ℝ)))
      (𝓝 ((stableShellBoundaryRoot (diamond.eta ε) w)⁻¹)) := by
  apply (diamond.stable_shell_root_tendsto ε w).inv₀
  apply norm_pos_iff.mp
  rw [stable_shell_boundary_root_norm _ (diamond.eta_sq ε)]
  exact Real.sqrt_pos.mpr (abs_pos.mpr hw)

end UV.SectorPlane
