import UV.ResumeConeMajorant
import UV.ExtendStablePole
import Mathlib.Analysis.Complex.RealDeriv

/-! The nontree part of the single stable-half massless coefficient.
The term subtracted here is the literal pole at the same positive
height. The branch remainder is controlled on both cone sheets. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology

theorem exp_sub_one_norm_le_of_re_nonpos {z : ℂ} (hz : z.re ≤ 0) :
    ‖Complex.exp z - 1‖ ≤ ‖z‖ := by
  let g (t : ℝ) := Complex.exp ((t : ℂ) * z)
  have hd (t : ℝ) : HasDerivAt g (g t * z) t := by
    simpa [g] using (((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z).cexp)
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖g t * z‖ ≤ ‖z‖ := by
    rw [norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [show g t = Complex.exp ((t : ℂ) * z) from rfl, Complex.norm_exp, Real.exp_le_one_iff]
    simpa [Complex.mul_re] using mul_nonpos_of_nonneg_of_nonpos ht.1 hz
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hd t).hasDerivWithinAt) hb (convex_Icc (0 : ℝ) 1)
    (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
  simpa [g] using he

variable {E : Type*} [NormedAddCommGroup E]

/-- The branch factor after subtracting the literal unweighted inverse. -/
def Plane.stableHalfRegular (diamond : Plane E) (ε : Evolution) (a w h : ℝ) : ℂ :=
  if hh : 0 < h then (diamond.stableHalfCoefficient ε a w h - 1) *
    diamond.poleCoefficient ε ⟨h, hh⟩ w else 0

theorem Plane.pole_coefficient_eq_inv (diamond : Plane E) (ε : Evolution) (h : Height)
    (w : ℝ) : diamond.poleCoefficient ε h w = (diamond.shiftedShellCoefficient ε h w)⁻¹ := by
  simp [Plane.poleCoefficient, diamond.pole_inverse_complex, Plane.shiftedShellCoefficient, directed]

theorem Plane.stable_half_regular_norm_bound (diamond : Plane E) (ε : Evolution)
    {a w h : ℝ} (ha : 0 ≤ a) (hw : w ≠ 0) (hh : 0 < h) :
    ‖diamond.stableHalfRegular ε a w h‖ ≤ a * inverseRootAbs w := by
  let z := diamond.shiftedShellCoefficient ε ⟨h, hh⟩ w
  let x := -(a : ℂ) * principalSqrt (-z)
  have hx : x.re ≤ 0 := by
    have H := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha)
      (principalSqrt_re_nonneg (-z))
    simpa [x, Complex.mul_re] using H
  have hz : z ≠ 0 := diamond.massless_shifted_coefficient_nonzero ε ⟨h, hh⟩ w
  have hroot : ‖principalSqrt (-z)‖ = Real.sqrt ‖z‖ :=
    (principalSqrt_norm (-z)).trans (by rw [norm_neg])
  have hn : ‖x‖ = a * Real.sqrt ‖z‖ := by
    unfold x
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg ha, hroot]
  have hzw : |w| ≤ ‖z‖ := by
    have h := Complex.abs_re_le_norm z
    simpa [z, Plane.shiftedShellCoefficient] using h
  have hpos : 0 < Real.sqrt ‖z‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr hz)
  have h := exp_sub_one_norm_le_of_re_nonpos hx
  rw [Plane.stableHalfRegular, dif_pos hh, Plane.stableHalfCoefficient, dif_pos hh,
    diamond.stable_half_numerator_characters, diamond.pole_coefficient_eq_inv]
  change ‖(Complex.exp x - 1) * z⁻¹‖ ≤ a * inverseRootAbs w
  rw [norm_mul, norm_inv, inverseRootAbs]
  calc
    _ ≤ (a * Real.sqrt ‖z‖) * ‖z‖⁻¹ :=
      mul_le_mul_of_nonneg_right (h.trans_eq hn) (inv_nonneg.mpr (norm_nonneg _))
    _ = a * (Real.sqrt ‖z‖)⁻¹ := by
      field_simp [hpos.ne', (norm_pos_iff.mpr hz).ne']
      linear_combination a * Real.sq_sqrt (norm_nonneg z)
    _ ≤ a * (Real.sqrt |w|)⁻¹ := mul_le_mul_of_nonneg_left
      (inv_anti₀ (Real.sqrt_pos.mpr (abs_pos.mpr hw)) (Real.sqrt_le_sqrt hzw)) ha

theorem Plane.stable_half_spacelike_coefficient_limit (diamond : Plane E) (ε : Evolution)
    (a : ℝ) {w : ℝ} (hw : w < 0) :
    Tendsto (diamond.stableHalfCoefficient ε a w) (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.exp ((-(a * Real.sqrt (-w)) : ℝ) : ℂ))) := by
  let Z (h : ℝ) : ℂ := -((w : ℂ) + Complex.I * ((diamond.eta ε * h : ℝ) : ℂ))
  have hZ : Continuous Z := by unfold Z; fun_prop
  have hZ0 : Z 0 = ((-w : ℝ) : ℂ) := by simp [Z]
  have hS : ContinuousAt principalSqrt (Z 0) :=
    (principalSqrt_differentiableAt (by rw [hZ0]; simpa using neg_pos.mpr hw)).continuousAt
  have ht := hS.tendsto.comp (hZ.continuousAt (x := (0 : ℝ))).tendsto
  rw [hZ0, principalSqrt_ofReal (neg_nonneg.mpr hw.le)] at ht
  have hlim := Complex.continuous_exp.continuousAt.tendsto.comp (ht.const_mul (-(a : ℂ)))
  have hlim' := hlim.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have he : -(a : ℂ) * (Real.sqrt (-w) : ℂ) =
      ((-(a * Real.sqrt (-w)) : ℝ) : ℂ) := by push_cast; ring
  rw [he] at hlim'
  refine hlim'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hpos : 0 < h := hh
  simp [Z, Plane.stableHalfCoefficient, hpos, diamond.stable_half_numerator_characters,
    Plane.shiftedShellCoefficient, Function.comp_apply]

/-- The spacelike parts cancel and the timelike parts give the
locally integrable sine density away from the null set w = 0. -/
theorem Plane.stable_half_regular_jump_limit (diamond : Plane E)
    (εPos εNeg : Evolution) (hPos : diamond.eta εPos = 1) (hNeg : diamond.eta εNeg = -1)
    (a : ℝ) {w : ℝ} (hw : w ≠ 0) :
    Tendsto (fun h => diamond.stableHalfRegular εPos a w h -
      diamond.stableHalfRegular εNeg a w h) (𝓝[>] (0 : ℝ))
      (𝓝 (if 0 < w then 2 * Complex.I *
        ((Real.sin (a * Real.sqrt w) / w : ℝ) : ℂ) else 0)) := by
  let P (ε : Evolution) (h : ℝ) : ℂ :=
    ((w : ℂ) + Complex.I * ((diamond.eta ε * h : ℝ) : ℂ))⁻¹
  have hp (ε : Evolution) : Tendsto (P ε) (𝓝[>] (0 : ℝ)) (𝓝 (w : ℂ)⁻¹) := by
    have hc : Continuous (fun h : ℝ => (w : ℂ) + Complex.I *
        ((diamond.eta ε * h : ℝ) : ℂ)) := by fun_prop
    have hC := hc.continuousAt (x := (0 : ℝ))
    have hD := hC.inv₀ (by simp [hw])
    simpa [P] using hD.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have H (ε : Evolution) : (fun h => (diamond.stableHalfCoefficient ε a w h - 1) * P ε h)
      =ᶠ[𝓝[>] 0] diamond.stableHalfRegular ε a w := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hpos : 0 < h := hh
    rw [Plane.stableHalfRegular, dif_pos hpos, diamond.pole_coefficient_eq_inv]
    rfl
  rcases lt_or_gt_of_ne hw with hlt | hgt
  · rw [if_neg hlt.not_gt]
    have hp' := (((diamond.stable_half_spacelike_coefficient_limit εPos a hlt).sub_const 1).mul
      (hp εPos)).congr' (H εPos)
    have hn' := (((diamond.stable_half_spacelike_coefficient_limit εNeg a hlt).sub_const 1).mul
      (hp εNeg)).congr' (H εNeg)
    simpa only [sub_self] using hp'.sub hn'
  · rw [if_pos hgt]
    have hp' := (((diamond.stable_half_timed_coefficient_limit εPos a hgt).sub_const 1).mul
      (hp εPos)).congr' (H εPos)
    have hn' := (((diamond.stable_half_timed_coefficient_limit εNeg a hgt).sub_const 1).mul
      (hp εNeg)).congr' (H εNeg)
    have ht := hp'.sub hn'
    rw [hPos, hNeg, one_mul, neg_one_mul, neg_mul] at ht
    have he :
        (Complex.exp (((a * Real.sqrt w : ℝ) : ℂ) * Complex.I) - 1) * (w : ℂ)⁻¹ -
          (Complex.exp (((-(a * Real.sqrt w) : ℝ) : ℂ) * Complex.I) - 1) * (w : ℂ)⁻¹ =
          2 * Complex.I * ((Real.sin (a * Real.sqrt w) / w : ℝ) : ℂ) := by
      rw [← sub_mul, sub_sub_sub_cancel_right, stable_half_boundary_phase_difference]
      push_cast
      ring
    rwa [he] at ht

theorem Plane.stable_half_regular_measurable (diamond : Plane E) (ε : Evolution)
    (a h : ℝ) : Measurable (fun w => diamond.stableHalfRegular ε a w h) := by
  by_cases hh : 0 < h
  · have hZ : Continuous (diamond.shiftedShellCoefficient ε ⟨h, hh⟩) :=
      Complex.continuous_ofReal.add continuous_const
    simp only [Plane.stableHalfRegular, hh, dite_true, Plane.stableHalfCoefficient,
      diamond.stable_half_numerator_characters, diamond.pole_coefficient_eq_inv]
    exact (((principalSqrt_measurable.comp hZ.neg.measurable).const_mul (-(a : ℂ))).cexp.sub
      measurable_const).mul hZ.measurable.inv
  · simpa only [Plane.stableHalfRegular, hh, dite_false] using
      (measurable_const : Measurable (fun _ : ℝ => (0 : ℂ)))

/-- Subtracting the unit pole leaves an unbounded branch term at the
massless tip for every positive depth. This is along the actual
positive-height ray in the declared carrier character. -/
theorem Plane.stable_half_regular_at_tip_unbounded (diamond : Plane E) (ε : Evolution)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun h => ‖diamond.stableHalfRegular ε a 0 h‖) (𝓝[>] (0 : ℝ)) atTop := by
  have hsqrt : Tendsto (fun h : ℝ => Real.sqrt h) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt (x := (0 : ℝ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hsqrt' : Tendsto (fun h : ℝ => Real.sqrt h) (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hsqrt, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact Real.sqrt_pos.mpr hh
  have hlarge := (tendsto_inv_nhdsGT_zero.comp hsqrt').const_mul_atTop ha
  have hlarge' := tendsto_atTop_add_const_right _ (-a ^ 2) hlarge
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), a * Real.sqrt h < 1 := by
    have h := hsqrt.const_mul a
    rw [mul_zero] at h
    exact h (Iio_mem_nhds zero_lt_one)
  apply tendsto_atTop_mono' _ _ hlarge'
  filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hsh
  have hp : 0 < h := hh
  let z := diamond.shiftedShellCoefficient ε ⟨h, hp⟩ 0
  have hz : z ≠ 0 := diamond.massless_shifted_coefficient_nonzero ε ⟨h, hp⟩ 0
  have hzn : ‖z‖ = h := by
    simp [z, Plane.shiftedShellCoefficient, Plane.eta, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hp]
  have hrem := stable_half_massless_remainder (a := a) hz (by
    rw [abs_of_pos ha, hzn]
    exact hsh.le)
  have heq : diamond.stableHalfRegular ε a 0 h =
      Complex.exp (-(a : ℂ) * principalSqrt (-z)) / z - z⁻¹ := by
    rw [Plane.stableHalfRegular, dif_pos hp, Plane.stableHalfCoefficient, dif_pos hp,
      diamond.stable_half_numerator_characters, diamond.pole_coefficient_eq_inv]
    change (Complex.exp (-(a : ℂ) * principalSqrt (-z)) - 1) * z⁻¹ =
      Complex.exp (-(a : ℂ) * principalSqrt (-z)) / z - z⁻¹
    rw [sub_mul, one_mul, div_eq_mul_inv]
  rw [← heq] at hrem
  have hreverse := norm_sub_norm_le ((a : ℂ) / principalSqrt (-z))
    (diamond.stableHalfRegular ε a 0 h)
  rw [norm_sub_rev, norm_div, Complex.norm_real, Real.norm_of_nonneg ha.le,
    principalSqrt_norm, norm_neg, hzn] at hreverse
  change a * (Real.sqrt h)⁻¹ + (-a ^ 2) ≤ ‖diamond.stableHalfRegular ε a 0 h‖
  rw [← div_eq_mul_inv]
  linarith

end UV.SectorPlane
