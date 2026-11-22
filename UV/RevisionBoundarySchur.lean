import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Analysis.Complex.Basic

/-! Finite-section Schur elimination and reciprocal-arrow determinant.
These identities are the finite-dimensional part of the charged cycle test. -/

noncomputable section

open Matrix Polynomial
open scoped Matrix

namespace UV.RevisionBoundary

variable {r s R : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s] [CommRing R]

theorem finite_charged_elimination (B : Matrix r r R) (E : Matrix r s R)
    (F : Matrix s r R) (H : Matrix s s R) [Invertible H]
    [Invertible (B - E * ⅟H * F)] :
    ((Matrix.fromBlocks B E F H)⁻¹).toBlocks₁₁ = (B - E * ⅟H * F)⁻¹ ∧
      (Matrix.fromBlocks B E F H).det = H.det * (B - E * ⅟H * F).det := by
  letI := Matrix.fromBlocks₂₂Invertible B E F H
  refine ⟨?_, Matrix.det_fromBlocks₂₂ B E F H⟩
  rw [← Matrix.invOf_eq_nonsing_inv, ← Matrix.invOf_eq_nonsing_inv,
    Matrix.invOf_fromBlocks₂₂_eq, Matrix.toBlocks_fromBlocks₁₁]

theorem two_pivot_elimination_order (B : Matrix r r R) (E : Matrix r s R)
    (F : Matrix s r R) (H : Matrix s s R) [Invertible B] [Invertible H] :
    B.det * (H - F * ⅟B * E).det = H.det * (B - E * ⅟H * F).det :=
  (Matrix.det_fromBlocks₁₁ B E F H).symm.trans (Matrix.det_fromBlocks₂₂ B E F H)

/-- The full determinant keeps the eliminated-sector factor even when every
background has the prescribed retained inverse. -/
theorem retained_inverse_does_not_fix_determinant (K : Matrix r r R) (U : Matrix r s R)
    (V : Matrix s r R) (H : Matrix s s R) [Invertible K] [Invertible H] :
    (((Matrix.fromBlocks (K + U * H * V) (U * H) (H * V) H)⁻¹).toBlocks₁₁ = K⁻¹) ∧
      (Matrix.fromBlocks (K + U * H * V) (U * H) (H * V) H).det = H.det * K.det := by
  have h : K + U * H * V - (U * H) * ⅟H * (H * V) = K := by
    rw [Matrix.mul_assoc U H (⅟H), mul_invOf_self, Matrix.mul_one,
      ← Matrix.mul_assoc U H V, add_sub_cancel_right]
  letI : Invertible (K + U * H * V - (U * H) * ⅟H * (H * V)) := h.symm ▸ ‹Invertible K›
  simpa only [h] using (finite_charged_elimination
    (K + U * H * V) (U * H) (H * V) H)

def reciprocalDeterminant (A : Matrix r s ℂ) : ℂ[X] :=
  (Matrix.fromBlocks 1 (-((X : ℂ[X]) • A.map C))
    (-((X : ℂ[X]) • A.conjTranspose.map C)) 1).det

private theorem expansion_identity (A : Matrix r s ℂ) :
    reciprocalDeterminant A =
      expand ℂ 2 (Matrix.det (1 + (X : ℂ[X]) • (-(A.conjTranspose * A)).map C)) := by
  unfold reciprocalDeterminant
  rw [Matrix.det_fromBlocks_one₁₁, (expand ℂ 2).map_det]
  congr 1
  change 1 - (-(X • A.conjTranspose.map C)) * (-(X • A.map C)) =
    (1 + (X : ℂ[X]) • (-(A.conjTranspose * A)).map C).map (expand ℂ 2)
  rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, ← pow_two, ← Matrix.map_mul]
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    map_add, map_mul, expand_X, expand_C, Matrix.one_apply, Matrix.neg_apply, map_neg, mul_neg]
  by_cases h : i = j <;> simp [h, sub_eq_add_neg]

/-- Finite-section first and second coefficients of the closed determinant.
The second coefficient is also the logarithm coefficient, because the constant
term is one and the linear coefficient is zero. -/
theorem reciprocal_determinant_coefficients (A : Matrix r s ℂ) :
    (reciprocalDeterminant A).coeff 0 = 1 ∧
      (reciprocalDeterminant A).coeff 1 = 0 ∧
      (reciprocalDeterminant A).coeff 2 = - (A.conjTranspose * A).trace := by
  rw [expansion_identity]
  constructor
  · rw [coeff_expand (by decide : 0 < (2 : ℕ))]
    rw [if_pos (dvd_zero _), Nat.zero_div, coeff_zero_eq_eval_zero]
    change (evalRingHom (0 : ℂ)) (Matrix.det _) = 1
    rw [(evalRingHom (0 : ℂ)).map_det]
    convert (Matrix.det_one : (1 : Matrix s s ℂ).det = 1) using 1
    congr 1
    apply Matrix.ext
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  constructor
  · rw [coeff_expand (by decide : 0 < (2 : ℕ))]
    norm_num
  · rw [show (2 : ℕ) = 2 * 1 by norm_num, coeff_expand_mul' (by decide),
      Matrix.coeff_det_one_add_X_smul_one, Matrix.trace_neg]

open scoped ComplexConjugate in
theorem reciprocal_determinant_quadratic_hilbert_schmidt (A : Matrix r s ℂ) :
    (reciprocalDeterminant A).coeff 2 = -((∑ j : s, ∑ i : r, ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
  rw [(reciprocal_determinant_coefficients A).2.2]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_sum]


end UV.RevisionBoundary
