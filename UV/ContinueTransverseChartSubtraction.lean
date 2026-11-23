import UV.ContinueStableMassiveChart
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Double subtraction on a genuine two-normal Cartesian chart. Joint
C² regularity controls the mixed divided difference under the original
product Lebesgue measure. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology NNReal

def transverseNormalCutoff (x : ℝ) : ℂ := (massiveNormalCutoff 1 x : ℂ)

theorem transverse_normal_cutoff_zero : transverseNormalCutoff 0 = 1 := by
  norm_num [transverseNormalCutoff, massiveNormalCutoff]

theorem transverse_normal_cutoff_even (x : ℝ) :
    transverseNormalCutoff (-x) = transverseNormalCutoff x := by
  simp only [transverseNormalCutoff, massiveNormalCutoff, abs_neg]

theorem transverse_normal_cutoff_lipschitz : LipschitzWith 1 transverseNormalCutoff := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h := (massive_normal_cutoff_lipschitz (b := 1) zero_lt_one).dist_le_mul x y
  simpa only [transverseNormalCutoff, Complex.isometry_ofReal.dist_eq, NNReal.coe_mk, inv_one,
    NNReal.coe_one] using h

theorem transverse_normal_cutoff_compact : HasCompactSupport transverseNormalCutoff := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro x hx
  apply abs_le.mp
  by_contra! H
  exact hx (by simp [transverseNormalCutoff, massive_normal_cutoff_zero zero_lt_one H.le])

theorem transverse_cutoff_defect_bound (x : ℝ) : ‖1 - transverseNormalCutoff x‖ ≤ |x| := by
  have H := transverse_normal_cutoff_lipschitz.norm_sub_le 0 x
  simpa only [transverse_normal_cutoff_zero, sub_zero, zero_sub, norm_neg, Real.norm_eq_abs, NNReal.coe_one,
    one_mul] using H

def transverseNormalRemainder (f : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  f p - transverseNormalCutoff p.1 * f (0,p.2) -
    transverseNormalCutoff p.2 * f (p.1,0) +
      transverseNormalCutoff p.1 * transverseNormalCutoff p.2 * f (0,0)

theorem transverse_normal_remainder_continuous {f : ℝ × ℝ → ℂ} (hf : Continuous f) :
    Continuous (transverseNormalRemainder f) := by
  have hx := transverse_normal_cutoff_lipschitz.continuous.comp
    (continuous_fst : Continuous (Prod.fst : ℝ × ℝ → ℝ))
  have hy := transverse_normal_cutoff_lipschitz.continuous.comp
    (continuous_snd : Continuous (Prod.snd : ℝ × ℝ → ℝ))
  exact ((hf.sub (hx.mul (hf.comp (continuous_const.prodMk continuous_snd)))).sub
    (hy.mul (hf.comp (continuous_fst.prodMk continuous_const)))).add ((hx.mul hy).mul continuous_const)

theorem transverse_normal_remainder_compact {f : ℝ × ℝ → ℂ} (hs : HasCompactSupport f) :
    HasCompactSupport (transverseNormalRemainder f) := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn
    (continuous_id : Continuous (id : ℝ × ℝ → ℝ × ℝ)).continuousOn
  let R := max 1 C
  let K := Icc (-R) R ×ˢ Icc (-R) R
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hfar (p : ℝ × ℝ) : R < ‖p‖ → f p = 0 := by
    intro h
    by_contra H
    exact (not_le_of_gt h) ((hC p (subset_tsupport f H)).trans (le_max_right _ _))
  have hcut (x : ℝ) (hx : R < |x|) : transverseNormalCutoff x = 0 := by
    unfold transverseNormalCutoff
    rw [massive_normal_cutoff_zero zero_lt_one ((le_max_left _ _).trans hx.le), Complex.ofReal_zero]
  apply HasCompactSupport.intro hK
  intro p hp
  have hn : R < ‖p‖ := by
    apply lt_of_not_ge
    intro h
    apply hp
    change max ‖p.1‖ ‖p.2‖ ≤ R at h
    exact ⟨abs_le.mp (by simpa only [Real.norm_eq_abs] using (le_max_left ‖p.1‖ ‖p.2‖).trans h),
      abs_le.mp (by simpa only [Real.norm_eq_abs] using (le_max_right ‖p.1‖ ‖p.2‖).trans h)⟩
  by_cases hx : R < |p.1|
  · have hx' : R < ‖(p.1, (0 : ℝ))‖ := by simpa [Prod.norm_def, Real.norm_eq_abs] using hx
    simp [transverseNormalRemainder, hfar p hn, hfar (p.1,0) hx', hcut _ hx]
  · have hy : R < |p.2| := by
      by_contra! H
      exact hp ⟨abs_le.mp (le_of_not_gt hx),abs_le.mp H⟩
    have hy' : R < ‖((0 : ℝ), p.2)‖ := by simpa [Prod.norm_def, Real.norm_eq_abs] using hy
    simp [transverseNormalRemainder, hfar p hn, hfar (0,p.2) hy', hcut _ hy]

theorem transverse_normal_mixed_difference_of_lipschitz {f : ℝ × ℝ → ℂ}
    (hf : Differentiable ℝ f) {L : ℝ≥0} (hL : LipschitzWith L (fderiv ℝ f))
    (x y : ℝ) :
    ‖f (x,y) - f (0,y) - f (x,0) + f (0,0)‖ ≤ (L : ℝ) * |x| * |y| := by
  let g (u : ℝ) := f (x,u) - f (0,u)
  have hg (u : ℝ) : HasDerivAt g
      ((fderiv ℝ f (x,u) - fderiv ℝ f (0,u)) (0,1)) u := by
    have H (v : ℝ) : HasDerivAt (fun t : ℝ => f (v,t)) (fderiv ℝ f (v,u) (0,1)) u :=
      (((hf (v,u)).hasFDerivAt).comp_hasDerivAt u
        ((hasDerivAt_const u v).prodMk (hasDerivAt_id u)))
    exact (H x).sub (H 0)
  have hb (u : ℝ) : ‖deriv g u‖ ≤ (L : ℝ) * |x| := by
    rw [(hg u).deriv]
    calc
      _ ≤ ‖fderiv ℝ f (x,u) - fderiv ℝ f (0,u)‖ * ‖((0,1) : ℝ × ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L : ℝ) * |x| := by
        have H := hL.norm_sub_le (x,u) (0,u)
        simpa [Prod.norm_def, Real.norm_eq_abs] using H
  have H := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := (Set.univ : Set ℝ)) (fun u _ => (hg u).differentiableAt)
    (fun u _ => hb u) convex_univ (mem_univ (0 : ℝ)) (mem_univ y)
  rw [sub_zero, Real.norm_eq_abs] at H
  exact (show f (x,y) - f (0,y) - f (x,0) + f (0,0) = g y - g 0 by unfold g; ring) ▸ H

theorem transverse_normal_mixed_difference_bound {f : ℝ × ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    ∃ L : ℝ≥0, ∀ x y : ℝ,
      ‖f (x,y) - f (0,y) - f (x,0) + f (0,0)‖ ≤ (L : ℝ) * |x| * |y| := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hs.fderiv ℝ) hfd le_rfl
  exact ⟨L, transverse_normal_mixed_difference_of_lipschitz (hf.differentiable (by norm_num)) hL⟩

theorem transverse_normal_remainder_bound_of_lipschitz {f : ℝ × ℝ → ℂ}
    {L L₀ : ℝ≥0} (hL₀ : LipschitzWith L₀ f)
    (hL : ∀ x y : ℝ, ‖f (x,y) - f (0,y) - f (x,0) + f (0,0)‖ ≤ (L : ℝ) * |x| * |y|)
    {B₀ : ℝ} (hB₀ : ‖f (0,0)‖ ≤ B₀) (p : ℝ × ℝ) :
    ‖transverseNormalRemainder f p‖ ≤ ((L : ℝ) + 2*(L₀ : ℝ) + B₀) * |p.1| * |p.2| := by
  rcases p with ⟨x,y⟩
  let A := f (x,y) - f (0,y) - f (x,0) + f (0,0)
  let B := (1-transverseNormalCutoff x) * (f (0,y) - f (0,0))
  let C := (1-transverseNormalCutoff y) * (f (x,0) - f (0,0))
  let D := (1-transverseNormalCutoff x) * (1-transverseNormalCutoff y) * f (0,0)
  have h₁ : ‖f (0,y) - f (0,0)‖ ≤ (L₀ : ℝ) * |y| := by
    simpa [Prod.norm_def, Real.norm_eq_abs] using hL₀.norm_sub_le (0,y) (0,0)
  have h₂ : ‖f (x,0) - f (0,0)‖ ≤ (L₀ : ℝ) * |x| := by
    simpa [Prod.norm_def, Real.norm_eq_abs] using hL₀.norm_sub_le (x,0) (0,0)
  have hB : ‖B‖ ≤ |x| * ((L₀ : ℝ) * |y|) := by
    unfold B
    rw [norm_mul]
    exact mul_le_mul (transverse_cutoff_defect_bound x) h₁ (norm_nonneg _) (abs_nonneg _)
  have hC : ‖C‖ ≤ |y| * ((L₀ : ℝ) * |x|) := by
    unfold C
    rw [norm_mul]
    exact mul_le_mul (transverse_cutoff_defect_bound y) h₂ (norm_nonneg _) (abs_nonneg _)
  have hD : ‖D‖ ≤ (|x| * |y|) * ‖f (0,0)‖ := by
    unfold D
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (transverse_cutoff_defect_bound x) (transverse_cutoff_defect_bound y)
        (norm_nonneg _) (abs_nonneg _)) (norm_nonneg _)
  have he : transverseNormalRemainder f (x,y) = (A+B)+(C+D) := by
    simp only [transverseNormalRemainder, A,B,C,D]
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  have h := add_le_add ((norm_add_le A B).trans (add_le_add (hL x y) hB))
    ((norm_add_le C D).trans (add_le_add hC hD))
  exact h.trans (by
    calc
      _ ≤ (L : ℝ) * |x| * |y| + |x| * ((L₀ : ℝ) * |y|) +
        (|y| * ((L₀ : ℝ) * |x|) + (|x| * |y|) * B₀) := by
          gcongr
      _ = _ := by ring)

theorem transverse_normal_remainder_bound {f : ℝ × ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    ∃ C ≥ 0, ∀ p : ℝ × ℝ, ‖transverseNormalRemainder f p‖ ≤ C * |p.1| * |p.2| := by
  obtain ⟨L,hL⟩ := transverse_normal_mixed_difference_bound hf hs
  obtain ⟨L₀,hL₀⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hf (by norm_num)
  exact ⟨(L : ℝ) + 2*(L₀ : ℝ) + ‖f (0,0)‖, by positivity,
    transverse_normal_remainder_bound_of_lipschitz hL₀ hL le_rfl⟩

end UV.SectorPlane
