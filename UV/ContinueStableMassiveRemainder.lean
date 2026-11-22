import UV.ContinueStableMassiveChart

/-! The stable-half numerator after subtracting its exact same-height
value at the positive-mass shell. The bound is uniform through the
branch edge and uses no pole selector. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier UV.RevisionSpectrum
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

theorem exp_difference_norm_le_of_re_nonpos {x y : ℂ}
    (hx : x.re ≤ 0) (hy : y.re ≤ 0) : ‖Complex.exp x - Complex.exp y‖ ≤ ‖x - y‖ := by
  by_cases hxy : x.re ≤ y.re
  · have h₀ : (x - y).re ≤ 0 := by simp only [Complex.sub_re]; linarith
    have h₁ : ‖Complex.exp y‖ ≤ 1 := by simpa only [Complex.norm_exp, Real.exp_le_one_iff] using hy
    rw [show Complex.exp x - Complex.exp y = (Complex.exp (x - y) - 1) * Complex.exp y by
      rw [sub_mul, one_mul, ← Complex.exp_add]; congr 1; ring, norm_mul]
    exact (mul_le_mul_of_nonneg_left h₁ (norm_nonneg _)).trans
      (by simpa only [mul_one] using exp_sub_one_norm_le_of_re_nonpos h₀)
  · rw [norm_sub_rev (Complex.exp x), norm_sub_rev x]
    have h₀ : (y - x).re ≤ 0 := by simp only [Complex.sub_re]; linarith
    have h₁ : ‖Complex.exp x‖ ≤ 1 := by simpa only [Complex.norm_exp, Real.exp_le_one_iff] using hx
    rw [show Complex.exp y - Complex.exp x = (Complex.exp (y - x) - 1) * Complex.exp x by
      rw [sub_mul, one_mul, ← Complex.exp_add]; congr 1; ring, norm_mul]
    exact (mul_le_mul_of_nonneg_left h₁ (norm_nonneg _)).trans
      (by simpa only [mul_one] using exp_sub_one_norm_le_of_re_nonpos h₀)

private theorem spectralRootUpper_re_ge_sqrt {w h : ℝ} (hw : 0 ≤ w) :
    Real.sqrt w ≤ (spectralRootUpper w h).re := by
  have hle : w ≤ Real.sqrt (w ^ 2 + h ^ 2) := by
    apply (sq_le_sq₀ hw (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity)]
    exact le_add_of_nonneg_right (sq_nonneg h)
  have H : (spectralRootUpper w h).re = Real.sqrt ((Real.sqrt (w ^ 2 + h ^ 2) + w) / 2) := by
    simp [spectralRootUpper]
  rw [H]
  exact Real.sqrt_le_sqrt (by linarith)

private theorem Plane.shifted_shell_sqrt_re_ge (diamond : Plane E) (ε : Evolution)
    (h : Height) {w : ℝ} (hw : 0 ≤ w) :
    Real.sqrt w ≤ (principalSqrt (diamond.shiftedShellCoefficient ε h w)).re := by
  have hη : diamond.eta ε = 1 ∨ diamond.eta ε = -1 := by
    rcases diamond with ⟨s, b, G⟩
    cases s <;> cases ε <;> norm_num [Plane.eta, sectorSign, evolutionSign]
  rcases hη with hη | hη
  · have H : diamond.shiftedShellCoefficient ε h w = (w : ℂ) + (h : ℝ) * Complex.I := by
      simp [Plane.shiftedShellCoefficient, hη, mul_comm Complex.I]
    rw [H, principalSqrt_upper_eq w h.property]
    exact spectralRootUpper_re_ge_sqrt hw
  · have H : diamond.shiftedShellCoefficient ε h w = (w : ℂ) - (h : ℝ) * Complex.I := by
      simp [Plane.shiftedShellCoefficient, hη]
      ring
    rw [H, principalSqrt_lower_eq w h.property]
    change Real.sqrt w ≤ (spectralRootUpper w h).re
    exact spectralRootUpper_re_ge_sqrt hw

theorem Plane.stable_half_coefficient_norm_le_one (diamond : Plane E) (ε : Evolution)
    {a w h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) :
    ‖diamond.stableHalfCoefficient ε a w h‖ ≤ 1 := by
  rw [Plane.stableHalfCoefficient, dif_pos hh, diamond.stable_half_numerator_characters]
  dsimp only
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have H := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha)
    (principalSqrt_re_nonneg (-(diamond.shiftedShellCoefficient ε ⟨h, hh⟩ w)))
  simpa [Complex.mul_re] using H

theorem Plane.stable_half_coefficient_timelike_difference (diamond : Plane E) (ε : Evolution)
    {a b w v h : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hw : b ≤ w) (hv : b ≤ v) (hh : 0 < h) :
    ‖diamond.stableHalfCoefficient ε a w h - diamond.stableHalfCoefficient ε a v h‖ ≤
      a / (2 * Real.sqrt b) * |w - v| := by
  let z (x : ℝ) := diamond.shiftedShellCoefficient ε ⟨h, hh⟩ x
  let r (x : ℝ) := principalSqrt (z x)
  let c : ℂ := Complex.I * ((diamond.eta ε * a : ℝ) : ℂ)
  have hn : ‖c‖ = a := by
    simp [c, Plane.eta, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
  have hnorm : 2 * Real.sqrt b ≤ ‖r w + r v‖ := by
    have h₁ : Real.sqrt b ≤ (r w).re :=
      (Real.sqrt_le_sqrt hw).trans (diamond.shifted_shell_sqrt_re_ge ε ⟨h, hh⟩ (hb.le.trans hw))
    have h₂ : Real.sqrt b ≤ (r v).re :=
      (Real.sqrt_le_sqrt hv).trans (diamond.shifted_shell_sqrt_re_ge ε ⟨h, hh⟩ (hb.le.trans hv))
    calc
      _ ≤ (r w + r v).re := by rw [Complex.add_re]; linarith
      _ ≤ _ := le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
  have hs : (r w - r v) * (r w + r v) = ((w - v : ℝ) : ℂ) := by
    rw [show (r w - r v) * (r w + r v) = (r w) ^ 2 - (r v) ^ 2 by ring]
    simp [r, z, principalSqrt_sq, Plane.shiftedShellCoefficient]
  have hr : ‖r w - r v‖ ≤ |w - v| / (2 * Real.sqrt b) := by
    rw [le_div_iff₀ (by positivity)]
    calc
      _ ≤ ‖r w - r v‖ * ‖r w + r v‖ := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ = _ := by rw [← norm_mul, hs, Complex.norm_real, Real.norm_eq_abs]
  have ht (q : ℝ) : (c * r q).re ≤ 0 := by
    have H := diamond.stable_half_coefficient_norm_le_one ε (w := q) ha hh
    rw [diamond.stable_half_analytic_form ε ⟨h, hh⟩ a q, Complex.norm_exp, Real.exp_le_one_iff] at H
    exact H
  rw [diamond.stable_half_analytic_form ε ⟨h, hh⟩ a w,
    diamond.stable_half_analytic_form ε ⟨h, hh⟩ a v]
  change ‖Complex.exp (c * r w) - Complex.exp (c * r v)‖ ≤ _
  calc
    _ ≤ ‖c * r w - c * r v‖ := exp_difference_norm_le_of_re_nonpos (ht w) (ht v)
    _ = a * ‖r w - r v‖ := by rw [← mul_sub, norm_mul, hn]
    _ ≤ a / (2 * Real.sqrt b) * |w - v| := by
      convert mul_le_mul_of_nonneg_left hr ha using 1
      ring

def Plane.massiveStableRemainder (diamond : Plane E) (ε : Evolution) (a m w h : ℝ) : ℂ :=
  if hh : 0 < h then
    (diamond.stableHalfCoefficient ε a w h - diamond.stableHalfCoefficient ε a (m ^ 2) h) *
      diamond.poleCoefficient ε ⟨h, hh⟩ (w - m ^ 2)
  else 0

theorem Plane.massive_stable_remainder_norm_bound (diamond : Plane E) (ε : Evolution)
    {a b m h : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hm : 2 * b ≤ m ^ 2) (hh : 0 < h) (w : ℝ) :
    ‖diamond.massiveStableRemainder ε a m w h‖ ≤
      max (a / (2 * Real.sqrt b)) (2 / b) := by
  let D := w - m ^ 2
  let z := diamond.shiftedShellCoefficient ε ⟨h, hh⟩ D
  let U := diamond.stableHalfCoefficient ε a w h - diamond.stableHalfCoefficient ε a (m ^ 2) h
  have hz₀ : 0 < ‖z‖ := norm_pos_iff.mpr (diamond.massless_shifted_coefficient_nonzero ε ⟨h, hh⟩ D)
  have hz : |D| ≤ ‖z‖ := by
    simpa [z, Plane.shiftedShellCoefficient] using Complex.abs_re_le_norm z
  rw [Plane.massiveStableRemainder, dif_pos hh, diamond.pole_coefficient_eq_inv]
  change ‖U * z⁻¹‖ ≤ _
  rw [norm_mul, norm_inv, ← div_eq_mul_inv]
  apply (div_le_iff₀ hz₀).2
  by_cases hn : |D| ≤ b
  · have hw : b ≤ w := by
      have h := (abs_le.mp hn).1
      dsimp [D] at h
      linarith
    have hmv : b ≤ m ^ 2 := by linarith
    exact (diamond.stable_half_coefficient_timelike_difference ε ha hb hw hmv hh).trans
      (mul_le_mul (le_max_left _ _) hz (abs_nonneg _) (by positivity))
  · have hU : ‖U‖ ≤ 2 := by
      convert (norm_sub_le _ _).trans
        (add_le_add (diamond.stable_half_coefficient_norm_le_one ε (w := w) ha hh)
          (diamond.stable_half_coefficient_norm_le_one ε (w := m ^ 2) ha hh)) using 1
      norm_num
    refine hU.trans ?_
    calc
      _ = (2 / b) * b := by field_simp
      _ ≤ _ := mul_le_mul (le_max_right _ _) ((lt_of_not_ge hn).le.trans hz)
        hb.le (by positivity)

theorem Plane.stable_half_coefficient_continuous (diamond : Plane E) (ε : Evolution) (a : ℝ)
    (h : Height) : Continuous (fun w => diamond.stableHalfCoefficient ε a w (h : ℝ)) := by
  let W (w : ℝ) := -(diamond.shiftedShellCoefficient ε h w)
  have hW : Continuous W := (Complex.continuous_ofReal.add continuous_const).neg
  have hn : diamond.eta ε ≠ 0 := by
    intro H
    simpa [H] using diamond.eta_sq ε
  have hS (w : ℝ) : W w ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    simpa [W, Plane.shiftedShellCoefficient] using
      (neg_ne_zero.mpr (mul_ne_zero hn h.property.ne'))
  have hc : Continuous (fun w => principalSqrt (W w)) :=
    continuous_iff_continuousAt.mpr fun w =>
      (principalSqrt_hasDerivAt (hS w)).continuousAt.comp hW.continuousAt
  simp only [Plane.stableHalfCoefficient, dif_pos h.property, diamond.stable_half_numerator_characters]
  exact Complex.continuous_exp.comp (continuous_const.mul hc)

end UV.SectorPlane
