import UV.RevisionBoundarySchur

/-! Finite sections of the relative two-band determinant. The pure onsite
factor is removed at the same scalar background in each block. -/

noncomputable section
open Matrix
open scoped Matrix

namespace UV.SectorPlane

private theorem twoBand_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) [Invertible D] : D.det ≠ 0 := by
  intro h
  have he := congrArg Matrix.det (mul_invOf_self D)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at he
  exact zero_ne_one he

/-- The actual finite block determinant divided by its two onsite factors
is the relative Schur determinant with both onsite inverses retained. -/
theorem twoBand_finite_relative_schur {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (Dpos : Matrix ι ι ℂ) (Dneg : Matrix κ κ ℂ)
    (T : Matrix ι κ ℂ) [Invertible Dpos] [Invertible Dneg] :
    (Matrix.fromBlocks Dpos T Tᴴ Dneg).det / (Dpos.det * Dneg.det) =
      (1 - ⅟Dneg * Tᴴ * ⅟Dpos * T).det := by
  have hFactor : Dneg - Tᴴ * ⅟Dpos * T = Dneg * (1 - ⅟Dneg * Tᴴ * ⅟Dpos * T) := by
    simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]
  rw [Matrix.det_fromBlocks₁₁ Dpos T Tᴴ Dneg, hFactor, Matrix.det_mul]
  field_simp [twoBand_det_ne_zero Dpos, twoBand_det_ne_zero Dneg]

end UV.SectorPlane
