import UV.ContinueAngularMassBracket
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Polynomial

/-! Zonal S³ harmonics in the normalized angular coordinate. The integrals
include the semicircle weight pulled back under u = cos θ. -/

noncomputable section
open Polynomial Polynomial.Chebyshev MeasureTheory Real
open scoped Polynomial
namespace UV

theorem angular_zonal_laplacian (j : ℕ) :
    (1-X^2)*derivative (derivative (U ℝ j))-3*X*derivative (U ℝ j) =
      -(j:ℝ[X])*((j:ℝ[X])+2)*U ℝ j := by
  have h := congrArg (derivative (R := ℝ)) (add_one_mul_T_eq_poly_in_U (R := ℝ) (j:ℤ))
  simp only [derivative_sub,derivative_add,derivative_mul,derivative_one,derivative_X,
    derivative_X_pow,T_derivative_eq_U,add_sub_cancel_right,Int.cast_natCast,
    derivative_natCast,zero_add,zero_mul,zero_sub,one_mul,Nat.cast_ofNat] at h
  push_cast at h
  simp only [pow_one, show C (2:ℝ) = (2:ℝ[X]) from C_eq_natCast 2] at h
  linear_combination (norm := ring_nf) h

theorem angular_zonal_neighbor (j : ℕ) :
    X*U ℝ j = (C (1/2:ℝ))*(U ℝ ((j:ℤ)+1)+U ℝ ((j:ℤ)-1)) := by
  rw [U_add_one]
  have hh : C (1/2:ℝ) * (2:ℝ[X]) = 1 := by
    calc _ = C ((1/2:ℝ)*2) := by rw [map_mul, show C (2:ℝ) = (2:ℝ[X]) from C_eq_natCast 2]
         _ = 1 := by norm_num
  linear_combination (norm := ring_nf) -(X*U ℝ j)*hh

private theorem angular_cos_integral (n : ℤ) :
    (∫ θ in (0:ℝ)..π, cos ((n:ℝ)*θ)) = if n=0 then π else 0 := by
  split_ifs with hn
  · simp [hn]
  have hne : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  let F := fun θ : ℝ => sin ((n:ℝ)*θ)/(n:ℝ)
  have hF (θ : ℝ) : HasDerivAt F (cos ((n:ℝ)*θ)) θ := by
    convert (((hasDerivAt_id θ).const_mul (n:ℝ)).sin.div_const (n:ℝ)) using 1
    field_simp
    rfl
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hF θ)
    ((continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)]
  simp [F,Real.sin_int_mul_pi]

theorem angular_zonal_orthonormal (j k : ℕ) :
    (2/π)*(∫ θ in (0:ℝ)..π,
      (U ℝ j).eval (cos θ)*(U ℝ k).eval (cos θ)*(sin θ)^2) =
      if j=k then 1 else 0 := by
  let a : ℤ := j+1
  let b : ℤ := k+1
  have hf (θ : ℝ) :
      (U ℝ j).eval (cos θ)*(U ℝ k).eval (cos θ)*(sin θ)^2 =
      (cos (((a-b:ℤ):ℝ)*θ)-cos (((a+b:ℤ):ℝ)*θ))/2 := by
    calc _ = ((U ℝ j).eval (cos θ)*sin θ)*((U ℝ k).eval (cos θ)*sin θ) := by ring
         _ = _ := by
           rw [U_real_cos,U_real_cos]
           simp only [a,b,Int.cast_sub,Int.cast_add,Int.cast_one,Int.cast_natCast,sub_mul,add_mul,
             Real.cos_sub,Real.cos_add]
           ring
  simp_rw [hf]
  rw [intervalIntegral.integral_div,intervalIntegral.integral_sub]
  · rw [angular_cos_integral,angular_cos_integral]
    have h₁ : a+b ≠ 0 := by dsimp [a,b]; omega
    have h₂ : a-b = 0 ↔ j=k := by dsimp [a,b]; omega
    simp only [h₁,if_false,h₂,sub_zero]
    split_ifs <;> simp [Real.pi_ne_zero]
  all_goals exact (continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _

/-- The same orthonormality for the literal normalized semicircle measure
in the axial coordinate u on the unit three-sphere. -/
theorem angular_semicircle_orthonormal (j k : ℕ) :
    (2/π)*(∫ u in (-1:ℝ)..1,
      (U ℝ j).eval u*(U ℝ k).eval u*Real.sqrt (1-u^2)) = if j=k then 1 else 0 := by
  let g := fun u : ℝ => (U ℝ j).eval u*(U ℝ k).eval u*Real.sqrt (1-u^2)
  have hg : Continuous g := ((U ℝ j).continuous.mul (U ℝ k).continuous).mul
    ((continuous_const.sub (continuous_id.pow 2)).sqrt)
  have h := intervalIntegral.integral_comp_mul_deriv (a := (0:ℝ)) (b := π)
    (fun θ _ => Real.hasDerivAt_cos θ) continuous_sin.neg.continuousOn hg
  rw [Real.cos_zero,Real.cos_pi] at h
  have hi : (∫ θ in (0:ℝ)..π, (g ∘ cos) θ*(-sin θ)) =
      -(∫ θ in (0:ℝ)..π, (U ℝ j).eval (cos θ)*(U ℝ k).eval (cos θ)*(sin θ)^2) := by
    rw [←intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le Real.pi_pos.le] at hθ
    simp only [g,Function.comp_apply,←Real.sin_eq_sqrt_one_sub_cos_sq hθ.1 hθ.2]
    ring
  have he := angular_zonal_orthonormal j k
  change (2/π)*(∫ u in (-1:ℝ)..1, g u) = _
  rw [hi,intervalIntegral.integral_symm (a := (-1:ℝ)) (b := 1),neg_inj] at h
  rw [←h]
  exact he

end UV
