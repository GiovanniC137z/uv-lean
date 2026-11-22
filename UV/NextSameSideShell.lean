import UV.FurtherCoincidentShell
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Support

/-! The square of a pole on one prescribed side of the regular shell.
The signed imaginary coefficient is retained in the actual carrier
quotient, and the derivatives are paired at positive height. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology NNReal

def sameSideReal (h D : ℝ) : ℝ := (D ^ 2 - h ^ 2) / (D ^ 2 + h ^ 2) ^ 2

def sameSideImag (h D : ℝ) : ℝ := -(2 * h * D) / (D ^ 2 + h ^ 2) ^ 2

theorem polePV_hasDerivAt {h : ℝ} (hh : 0 < h) (D : ℝ) :
    HasDerivAt (polePV h) (-sameSideReal h D) D := by
  have hden : HasDerivAt (fun x : ℝ => x ^ 2 + h ^ 2) (2 * D) D := by
    simpa using ((hasDerivAt_id D).pow 2).add_const (h ^ 2)
  convert (hasDerivAt_id D).div hden (by positivity) using 1
  simp only [sameSideReal, id_eq]
  ring

theorem polePoisson_hasDerivAt {h : ℝ} (hh : 0 < h) (D : ℝ) :
    HasDerivAt (polePoisson h) (sameSideImag h D) D := by
  have hden : HasDerivAt (fun x : ℝ => x ^ 2 + h ^ 2) (2 * D) D := by
    simpa using ((hasDerivAt_id D).pow 2).add_const (h ^ 2)
  convert (hasDerivAt_const D h).div hden (by positivity) using 1
  unfold sameSideImag
  ring

private theorem integral_derivative_against_test {u u' f f' : ℝ → ℝ}
    (hu : ∀ D, HasDerivAt u (u' D) D) (hu' : Continuous u')
    (hf : ∀ D, HasDerivAt f (f' D) D) (hf' : Continuous f')
    (hs : HasCompactSupport f) (hs' : HasCompactSupport f') :
    (∫ D, u' D * f D) = - ∫ D, u D * f' D := by
  have huc : Continuous u := continuous_iff_continuousAt.mpr fun D => (hu D).continuousAt
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun D => (hf D).continuousAt
  have h₀ : Integrable (fun D => u D * f D) :=
    (huc.mul hfc).integrable_of_hasCompactSupport (hs.mul_left (f := u))
  have h₁ : Integrable (fun D => u' D * f D) :=
    (hu'.mul hfc).integrable_of_hasCompactSupport (hs.mul_left (f := u'))
  have h₂ : Integrable (fun D => u D * f' D) :=
    (huc.mul hf').integrable_of_hasCompactSupport (hs'.mul_left (f := u))
  have hb := integral_mul_deriv_eq_deriv_mul_of_integrable hu hf h₂ h₁ h₀
  linarith

/-- Pointwise second-order control of the even increment follows from a
Lipschitz derivative. No independent bound on the even part is needed. -/
theorem shell_even_increment_le {f f' : ℝ → ℝ} {L : ℝ≥0}
    (hf : ∀ D, HasDerivAt f (f' D) D) (hl : LipschitzWith L f') (D : ℝ) :
    ‖evenShellTest f D - f 0‖ ≤ (L : ℝ) * D ^ 2 := by
  let g (r : ℝ) := f r + f (-r)
  have hder (r : ℝ) : HasDerivAt g (f' r - f' (-r)) r := by
    simpa [g, sub_eq_add_neg] using (hf r).add ((hf (-r)).comp r (hasDerivAt_id r).neg)
  have hb (r : ℝ) (hr : r ∈ Icc (-|D|) |D|) :
      ‖f' r - f' (-r)‖ ≤ 2 * (L : ℝ) * |D| := by
    have h := hl.norm_sub_le r (-r)
    rw [show r - -r = 2 * r by ring, norm_mul, Real.norm_of_nonneg zero_le_two,
      Real.norm_eq_abs r] at h
    have ha := (abs_le).2 hr
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left ha L.coe_nonneg])
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r _ => (hder r).hasDerivWithinAt) hb (convex_Icc _ _)
    (x := 0) (y := D) ⟨by simp, abs_nonneg _⟩ ⟨neg_abs_le _, le_abs_self _⟩
  have hg : g D - g 0 = 2 * (evenShellTest f D - f 0) := by
    simp only [g, evenShellTest, neg_zero]; ring
  rw [hg, norm_mul, Real.norm_of_nonneg zero_le_two, sub_zero, Real.norm_eq_abs D] at he
  rw [mul_assoc, ← pow_two, sq_abs] at he
  linarith

/-- The even subtraction and the negative distributional derivative of
the principal value are exactly the same finite part. -/
theorem shell_finite_part_eq_symmetric_derivative {f f' : ℝ → ℝ} {L : ℝ≥0}
    (hf : ∀ D, HasDerivAt f (f' D) D) (hs : HasCompactSupport f)
    (hl : LipschitzWith L f') :
    (∫ D, shellFinitePartTest f D) = ∫ D in Ioi (0 : ℝ), symmetricTest f' D := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun D => (hf D).continuousAt
  have hval : f' = deriv f := funext fun D => (hf D).deriv.symm
  have hfs' : HasCompactSupport f' := hval ▸ hs.deriv
  obtain ⟨C, hC⟩ := hfc.bounded_above_of_compact_support hs
  have hB := shell_finite_part_test_integrable hfc hC
    (fun D _ => shell_even_increment_le hf hl D)
  have hA := symmetric_test_integrable hl (hl.continuous.integrable_of_hasCompactSupport hfs')
  let g (D : ℝ) := f D + f (-D) - 2 * f 0
  let v (D : ℝ) := g D / D
  have hg (D : ℝ) : HasDerivAt g (f' D - f' (-D)) D := by
    simpa [g, sub_eq_add_neg] using
      ((hf D).add ((hf (-D)).comp D (hasDerivAt_id D).neg)).sub_const (2 * f 0)
  have hzero : g 0 = 0 := by simp [g]; ring
  have hvc : ContinuousAt v 0 := by
    rw [continuousAt_iff_punctured_nhds]
    have h0 : HasDerivAt g 0 0 := by simpa using hg 0
    simpa [v, hzero, div_eq_inv_mul] using h0.tendsto_slope_zero
  have hvinf : Tendsto v atTop (𝓝 0) := by
    refine tendsto_bdd_div_atTop_nhds_zero (b := -(4 * C)) (B := 4 * C) ?_ ?_ tendsto_id
    · exact Eventually.of_forall fun D => by
        have := abs_le.mp (hC D)
        have := abs_le.mp (hC (-D))
        have := abs_le.mp (hC 0)
        dsimp [g]
        linarith
    · exact Eventually.of_forall fun D => by
        have := abs_le.mp (hC D)
        have := abs_le.mp (hC (-D))
        have := abs_le.mp (hC 0)
        dsimp [g]
        linarith
  have hvd (D : ℝ) (hD : D ∈ Ioi (0 : ℝ)) :
      HasDerivAt v (symmetricTest f' D - 2 * shellFinitePartTest f D) D := by
    have hp : 0 < D := hD
    convert (hg D).div (hasDerivAt_id D) hp.ne' using 1
    dsimp [g, symmetricTest, shellFinitePartTest, evenShellTest]
    field_simp [hp.ne']
  have he := integral_Ioi_of_hasDerivAt_of_tendsto hvc.continuousWithinAt hvd
    (hA.sub (hB.integrableOn.const_mul 2)) hvinf
  have hV : v 0 = 0 := by simp [v]
  rw [hV, sub_zero, integral_sub hA (hB.integrableOn.const_mul 2), integral_const_mul] at he
  have hsym (D : ℝ) : shellFinitePartTest f (-D) = shellFinitePartTest f D := by
    simp only [shellFinitePartTest, evenShellTest, neg_neg, neg_sq, add_comm (f (-D))]
  have hfull : (∫ D, shellFinitePartTest f D) =
      2 * ∫ D in Ioi (0 : ℝ), shellFinitePartTest f D := by
    rw [← integral_add_compl measurableSet_Ioi hB, compl_Ioi, ← neg_zero,
      ← integral_comp_neg_Ioi, neg_zero]
    simp_rw [hsym]
    ring
  rw [hfull]
  linarith

variable {E : Type*} [NormedAddCommGroup E]

/-- The literal same-side square uses the same vectorial pole unit and
the same sector-evolution sign in both factors. -/
theorem Plane.same_side_pole_square (diamond : Plane E) (ε : Evolution)
    (height : Height) (D : ℝ) :
    diamond.poleInverse ε height D ^ 2 =
      directed ((sameSideReal (height : ℝ) D : ℂ) +
        Complex.I * ((diamond.eta ε * sameSideImag (height : ℝ) D : ℝ) : ℂ)) := by
  rw [pow_two, diamond.inverse_pole_split ε height, ← directed_mul]
  congr 1
  have hη : (diamond.eta ε : ℂ) ^ 2 = 1 := by exact_mod_cast diamond.eta_sq ε
  have hden : ((D : ℂ) ^ 2 + (height : ℝ) ^ 2) ≠ 0 := by
    exact_mod_cast (add_pos_of_nonneg_of_pos (sq_nonneg D) (sq_pos_of_pos height.property)).ne'
  unfold sameSideReal sameSideImag polePV polePoisson
  push_cast
  have hs : (Complex.I * (diamond.eta ε : ℂ)) ^ 2 = -1 := by
    rw [mul_pow, Complex.I_sq, hη, mul_one]
  field_simp [hden]
  linear_combination ((height : ℝ) : ℂ) ^ 2 * hs

/-- In the invariant shell coordinate the two unscaled scalar components
converge to the finite part and the delta derivative. -/
theorem same_side_shell_test_limit
    {f f' : ℝ → ℝ} {L : ℝ≥0} (hf : ∀ D, HasDerivAt f (f' D) D)
    (hs : HasCompactSupport f) (hl : LipschitzWith L f') :
    Tendsto (fun h : ℝ =>
      (∫ D, sameSideReal h D * f D, ∫ D, sameSideImag h D * f D))
      (𝓝[>] (0 : ℝ)) (𝓝 ((∫ D, shellFinitePartTest f D), -(Real.pi * f' 0))) := by
  have hval : f' = deriv f := funext fun D => (hf D).deriv.symm
  have hs' : HasCompactSupport f' := hval ▸ hs.deriv
  obtain ⟨C, hC⟩ := hl.continuous.bounded_above_of_compact_support hs'
  have hPV := pole_pv_test_limit hl (hl.continuous.integrable_of_hasCompactSupport hs')
  have hlim := hPV.prodMk_nhds (pole_poisson_test_limit hl.continuous C hC).neg
  rw [← shell_finite_part_eq_symmetric_derivative hf hs hl] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : 0 < h := hh
  have hreal := integral_derivative_against_test (polePV_hasDerivAt hh')
    (by
      unfold sameSideReal
      refine continuous_neg.comp (Continuous.div ?_ ?_ (fun D => by positivity)) <;> fun_prop)
    hf hl.continuous hs hs'
  have himag := integral_derivative_against_test (polePoisson_hasDerivAt hh')
    (by
      unfold sameSideImag
      refine Continuous.div ?_ ?_ (fun D => by positivity) <;> fun_prop)
    hf hl.continuous hs hs'
  simp only [neg_mul, integral_neg] at hreal
  rw [neg_inj.mp hreal, himag]

/-- The imaginary component in the directed line has the signed coefficient ηπδ′. -/
theorem Plane.same_side_pole_square_test_limit (diamond : Plane E) (ε : Evolution)
    {f f' : ℝ → ℝ} {L : ℝ≥0} (hf : ∀ D, HasDerivAt f (f' D) D)
    (hs : HasCompactSupport f) (hl : LipschitzWith L f') :
    Tendsto (fun h : ℝ =>
      (∫ D, sameSideReal h D * f D, diamond.eta ε * ∫ D, sameSideImag h D * f D))
      (𝓝[>] (0 : ℝ)) (𝓝 ((∫ D, shellFinitePartTest f D), -diamond.eta ε * (Real.pi * f' 0))) := by
  have h := same_side_shell_test_limit hf hs hl
  have hRe := continuous_fst.continuousAt.tendsto.comp h
  have hIm := continuous_snd.continuousAt.tendsto.comp h
  simpa only [Function.comp_def, mul_neg, neg_mul] using
    hRe.prodMk_nhds (hIm.const_mul (diamond.eta ε))

end UV.SectorPlane
