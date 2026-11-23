import UV.ContinueRelativeSoftTrace

/-! The constant-field derivative of the actual shifted log determinant
integrand. Directions are unit vectors in the original Euclidean plane chart. -/

noncomputable section

namespace UV.RelativeSoft

open UV.SectorPlane
open scoped RealInnerProductSpace

/-- One-dimensional restriction of the fixed-width determinant density with
external field t•u and the two actual chord arguments. -/
def constantFieldDensity (e m σ : ℝ) (k : EuclideanPlaneMomentum) (u : ConeUnitDirection)
    (t : ℝ) : ℝ :=
  softLog m (k + softChord σ (k + (e*t) • u.val) - softChord σ k) - softLog m k

def softChordSecond (σ : ℝ) (k : EuclideanPlaneMomentum) (u : ConeUnitDirection) :
    EuclideanPlaneMomentum :=
  let g := Real.exp (-(σ^2*‖k‖^2))
  let p := inner ℝ k u.val
  (4*σ^4*g*p^2-2*σ^2*g) • k - (4*σ^2*g*p) • u.val

private theorem constant_field_ray_hasDerivAt (e : ℝ) (k : EuclideanPlaneMomentum)
    (u : ConeUnitDirection) (t : ℝ) :
    HasDerivAt (fun t => k+(e*t) • u.val) (e • u.val) t := by
  simpa only [mul_one] using (((hasDerivAt_id t).const_mul e).smul_const u.val).const_add k

private theorem constant_field_shift_hasDerivAt (e σ : ℝ) (k : EuclideanPlaneMomentum)
    (u : ConeUnitDirection) (t : ℝ) :
    HasDerivAt (fun t => k + softChord σ (k+(e*t) • u.val) - softChord σ k)
      (e • softChordDifferential σ (k+(e*t) • u.val) u.val) t := by
  have h := (soft_chord_hasFDerivAt σ (k+(e*t) • u.val)).comp_hasDerivAt t
    (constant_field_ray_hasDerivAt e k u t)
  simpa only [Function.comp_apply,map_smul] using (h.const_add k).sub_const (softChord σ k)

theorem constant_field_density_derivative (e σ : ℝ) {m : ℝ} (hm : m ≠ 0)
    (k : EuclideanPlaneMomentum) (u : ConeUnitDirection) (t : ℝ) :
    HasDerivAt (constantFieldDensity e m σ k u)
      (e * inner ℝ (softLogGradient m (k + softChord σ (k+(e*t) • u.val) - softChord σ k))
        (softChordDifferential σ (k+(e*t) • u.val) u.val)) t := by
  let q := k + softChord σ (k+(e*t) • u.val) - softChord σ k
  have hs : 0 < m^2 := sq_pos_of_ne_zero hm
  have hd : m^2+‖q‖^2 ≠ 0 := (add_pos_of_pos_of_nonneg hs (sq_nonneg _)).ne'
  have h := (soft_log_hasFDerivAt m q hd).comp_hasDerivAt t (constant_field_shift_hasDerivAt e σ k u t)
  simpa only [constantFieldDensity,Function.comp_apply,innerSL_apply,real_inner_smul_right] using
    h.sub_const (softLog m k)

theorem soft_chord_direction_hasDerivAt_zero (e σ : ℝ) (k : EuclideanPlaneMomentum)
    (u : ConeUnitDirection) :
    HasDerivAt (fun t : ℝ => softChordDifferential σ (k+(e*t) • u.val) u.val)
      (e • softChordSecond σ k u) 0 := by
  let q (t : ℝ) := k+(e*t) • u.val
  have hq : q 0 = k := by simp [q]
  have hr := constant_field_ray_hasDerivAt e k u 0
  change HasDerivAt q (e • u.val) 0 at hr
  let p := inner ℝ k u.val
  have hn : HasDerivAt (fun t => ‖q t‖^2) (2*e*p) 0 := by
    have h := (hasStrictFDerivAt_norm_sq (q 0)).hasFDerivAt.comp_hasDerivAt 0 hr
    convert h using 1
    simp only [hq,two_nsmul,ContinuousLinearMap.add_apply,innerSL_apply,real_inner_smul_right,p]
    ring
  let g := Real.exp (-(σ^2*‖k‖^2))
  have he : HasDerivAt (fun t => Real.exp (-(σ^2*‖q t‖^2))) (g * (-(σ^2*(2*e*p)))) 0 := by
    simpa only [Pi.neg_apply,hq,g] using (hn.const_mul (σ^2)).neg.exp
  have hp : HasDerivAt (fun t => inner ℝ (q t) u.val) e 0 := by
    have h := hr.inner ℝ (hasDerivAt_const 0 u.val)
    simpa only [inner_zero_right,real_inner_smul_left,real_inner_self_eq_norm_sq,
      u.property,one_pow,mul_one,zero_add,add_zero] using h
  have hd := (he.smul_const u.val).sub (((he.const_mul (2*σ^2)).mul hp).smul hr)
  have hfun : (fun t : ℝ => softChordDifferential σ (q t) u.val) =
      fun t => Real.exp (-(σ^2*‖q t‖^2)) • u.val -
        ((2*σ^2 * Real.exp (-(σ^2*‖q t‖^2))) * inner ℝ (q t) u.val) • q t := by
    funext t
    simp [softChordDifferential,softOuter,smul_smul]
  change HasDerivAt (fun t : ℝ => softChordDifferential σ (q t) u.val) _ _
  rw [hfun]
  convert hd using 1
  simp only [softChordSecond,Pi.mul_apply,hq,smul_sub,smul_smul,g,p]
  module

/-- The axial or transverse unit-direction second derivative of the literal
constant-field density before momentum integration by parts. -/
theorem constant_field_density_second (e σ : ℝ) {m : ℝ} (hm : m ≠ 0)
    (k : EuclideanPlaneMomentum) (u : ConeUnitDirection) :
    HasDerivAt (deriv (constantFieldDensity e m σ k u))
      (e^2 * (inner ℝ (softLogHessian m k (softChordDifferential σ k u.val))
          (softChordDifferential σ k u.val) +
        inner ℝ (softLogGradient m k) (softChordSecond σ k u))) 0 := by
  let q (t : ℝ) := k + softChord σ (k+(e*t) • u.val) - softChord σ k
  have hq : q 0 = k := by simp [q]
  have hs : HasDerivAt q (e • softChordDifferential σ k u.val) 0 := by
    simpa only [mul_zero,zero_smul,add_zero,q] using constant_field_shift_hasDerivAt e σ k u 0
  have hd : m^2+‖k‖^2 ≠ 0 := (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hm) (sq_nonneg _)).ne'
  have hg : HasDerivAt (fun t => softLogGradient m (q t))
      (e • softLogHessian m k (softChordDifferential σ k u.val)) 0 := by
    have h := (soft_log_gradient_hasFDerivAt m (q 0) (by rwa [hq])).comp_hasDerivAt 0 hs
    simpa only [Function.comp_apply,hq,map_smul] using h
  have h := (hg.inner ℝ (soft_chord_direction_hasDerivAt_zero e σ k u)).const_mul e
  have hfun : deriv (constantFieldDensity e m σ k u) =
      fun t => e * inner ℝ (softLogGradient m (q t))
        (softChordDifferential σ (k+(e*t) • u.val) u.val) :=
    funext fun t => (constant_field_density_derivative e σ hm k u t).deriv
  rw [hfun]
  convert h using 1
  simp only [hq,mul_zero,zero_smul,add_zero,real_inner_smul_right,real_inner_smul_left]
  ring

end UV.RelativeSoft
