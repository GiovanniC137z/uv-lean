import UV.ScalarKernelBoundary

/-! Regular profiles satisfy the compact shell estimates by differentiating
in the real shell variable. The stable-half branch at positive mass is
covered separately on its actual prescribed side of the cut. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E]

/-- A C¹ profile of height and real shell invariant need only have a
bounded derivative on the compact rectangles met by a test. -/
theorem Plane.contDiff_shell_kernel_bounds (diamond : Plane E) (ε : Evolution) (s : ℝ)
    {U : ℝ × ℝ → ℂ} (hU : ContDiff ℝ 1 U) :
    diamond.ShellKernelBounds ε s (fun h w => U ((h : ℝ), w)) (fun w => U (0, w)) := by
  refine ⟨fun h => hU.continuous.comp (continuous_const.prodMk continuous_id),
    (hU.continuous.comp (continuous_const.prodMk continuous_id)).measurable, ?_, ?_⟩
  · intro w
    exact hU.continuous.continuousAt.tendsto.comp (pole_height_tendsto_zero.prodMk_nhds tendsto_const_nhds)
  · intro R
    let B := max |R| |s|
    let D := Icc (0 : ℝ) 1 ×ˢ Icc (-B) B
    have hc : IsCompact D := isCompact_Icc.prod isCompact_Icc
    have hv : Convex ℝ D := (convex_Icc _ _).prod (convex_Icc _ _)
    obtain ⟨A, hA⟩ := hc.exists_bound_of_continuousOn (hU.continuous_fderiv le_rfl).continuousOn
    let C := max A 0
    have hC : 0 ≤ C := le_max_right _ _
    refine ⟨C, hC, ?_⟩
    filter_upwards [pole_height_tendsto_zero (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with h hh w hw
    have htime : (h : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨h.property.le, (show (h : ℝ) < 1 from hh).le⟩
    have hwB : |w| ≤ B := hw.trans ((le_abs_self R).trans (le_max_left _ _))
    have hsB : |s| ≤ B := le_max_right _ _
    have hloc := hv.norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => hU.differentiable le_rfl x)
      (fun x hx => (hA x hx).trans (le_max_left A 0))
      (show ((h : ℝ), s) ∈ D from ⟨htime, abs_le.mp hsB⟩)
      (show ((h : ℝ), w) ∈ D from ⟨htime, abs_le.mp hwB⟩)
    have hdiff : ‖U ((h : ℝ), w) - U ((h : ℝ), s)‖ ≤ C * |w - s| := by
      simpa [C, Prod.norm_def, Real.norm_eq_abs] using hloc
    by_cases he : w = s
    · simp [he, hC]
    · rw [norm_mul]
      calc
        _ ≤ (C * |w - s|) * |w - s|⁻¹ := mul_le_mul hdiff
          (diamond.pole_coefficient_off_shell_bound ε h (sub_ne_zero.mpr he)) (norm_nonneg _) (by positivity)
        _ = C := by rw [mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr (sub_ne_zero.mpr he)), mul_one]

/-- Extracted scalar numerator with its vectorial displacement and
unmodified real shell argument. -/
def Plane.scalarKernelReadout (diamond : Plane E) (ε : Evolution) (a : ℝ)
    (φ : ℂ → ℂ) (h : Height) (w : ℝ) : ℂ :=
  φ (-(a : ℂ) ^ 2 * diamond.shiftedShellCoefficient ε h w)

theorem Plane.scalar_kernel_bounds_of_contDiff (diamond : Plane E) (ε : Evolution) (a s : ℝ)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) :
    diamond.ShellKernelBounds ε s (diamond.scalarKernelReadout ε a φ)
      (fun w => φ (-(a : ℂ) ^ 2 * (w : ℂ))) := by
  let U (z : ℝ × ℝ) := φ (-(a : ℂ) ^ 2 * ((z.2 : ℂ) +
    Complex.I * ((diamond.eta ε * z.1 : ℝ) : ℂ)))
  have hU : ContDiff ℝ 1 U := by
    apply hφ.comp
    exact contDiff_const.mul ((Complex.ofRealCLM.contDiff.comp contDiff_snd).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst))))
  simpa only [U, mul_zero, Complex.ofReal_zero, add_zero,
    Plane.scalarKernelReadout, Plane.shiftedShellCoefficient] using
    diamond.contDiff_shell_kernel_bounds ε s hU

def stableSideValue (η a w : ℝ) : ℂ := Complex.exp (-(a : ℂ) * stableShellBoundaryRoot η w)

theorem stable_side_value_at_mass (η a : ℝ) {m : ℝ} (hm : 0 ≤ m) :
    stableSideValue η a (m ^ 2) = Complex.exp (Complex.I * (η : ℂ) * (a : ℂ) * (m : ℂ)) := by
  unfold stableSideValue stableShellBoundaryRoot
  rw [Real.sqrt_sq hm, Real.sqrt_eq_zero_of_nonpos (neg_nonpos.mpr (sq_nonneg m)), Complex.ofReal_zero]
  congr 1
  ring

theorem Plane.stable_half_positive_mass_kernel_bounds (diamond : Plane E) (ε : Evolution)
    {a m : ℝ} (ha : 0 ≤ a) (hm : 0 < m) :
    diamond.ShellKernelBounds ε (m ^ 2) (fun h w => diamond.stableHalfCoefficient ε a w h)
      (stableSideValue (diamond.eta ε) a) := by
  refine ⟨diamond.stable_half_coefficient_continuous ε a, ?_, ?_, ?_⟩
  · unfold stableSideValue stableShellBoundaryRoot
    fun_prop
  · intro w
    have h := Complex.continuous_exp.continuousAt.tendsto.comp
      ((diamond.stable_shell_root_tendsto ε w).const_mul (-(a : ℂ)))
    refine h.congr fun h => ?_
    rw [Plane.stableHalfCoefficient, dif_pos h.property, diamond.stable_half_numerator_characters]
    rfl
  · intro _
    let b := m ^ 2 / 4
    have hb : 0 < b := by dsimp [b]; positivity
    have hbm : 2 * b ≤ m ^ 2 := by dsimp [b]; linarith [sq_nonneg m]
    refine ⟨max (a / (2 * Real.sqrt b)) (2 / b), (le_max_of_le_right (by positivity)), ?_⟩
    refine Eventually.of_forall fun h w _ => ?_
    simpa only [Plane.massiveStableRemainder, dif_pos h.property] using
      diamond.massive_stable_remainder_norm_bound ε ha hb hbm h.property w

end UV.SectorPlane
