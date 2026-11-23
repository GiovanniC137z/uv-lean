import UV.ContinueNetworkFourier
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Retained score rows and seam rows in the same independent displacement
slots. The Schur calculation uses ordinary Euclidean Cartesian components. -/

noncomputable section

open Matrix MeasureTheory Set
open scoped Matrix BigOperators InnerProductSpace

namespace UV

variable {E S L : Type*} [Fintype E] [Fintype S] [Fintype L]
variable [DecidableEq E] [DecidableEq S]

/-- The actual positive-width row Gram matrix (ATA^T). -/
def retainedGram {R : Type*} (t : E → ℝ) (A : Matrix R E ℝ) : Matrix R R ℝ :=
  A * diagonal t * Aᵀ

/-- The seam–score off-diagonal block (CTJ^T). -/
def retainedCross (t : E → ℝ) (C : Matrix S E ℝ) (J : Matrix L E ℝ) : Matrix S L ℝ :=
  C * diagonal t * Jᵀ

/-- The conditional covariance (Q) of each Cartesian score component. -/
def retainedSchur (t : E → ℝ) (C : Matrix S E ℝ) (J : Matrix L E ℝ) : Matrix L L ℝ :=
  retainedGram t J - (retainedCross t C J)ᴴ * (retainedGram t C)⁻¹ * retainedCross t C J

theorem retainedGram_factor {R : Type*} (t : E → ℝ) (ht : ∀ e, 0 ≤ t e)
    (A : Matrix R E ℝ) :
    retainedGram t A =
      (A * diagonal (fun e => Real.sqrt (t e))) *
        (A * diagonal (fun e => Real.sqrt (t e)))ᵀ := by
  rw [transpose_mul, diagonal_transpose, ← Matrix.mul_assoc, Matrix.mul_assoc A,
    diagonal_mul_diagonal, retainedGram]
  simp_rw [Real.mul_self_sqrt (ht _)]

theorem retainedGram_posSemidef {R : Type*} [Fintype R] (t : E → ℝ)
    (ht : ∀ e, 0 ≤ t e) (A : Matrix R E ℝ) : (retainedGram t A).PosSemidef := by
  rw [retainedGram_factor t ht]
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    posSemidef_self_mul_conjTranspose (A * diagonal (fun e => Real.sqrt (t e)))

theorem retainedGram_rank {R : Type*} [Fintype R] (t : E → ℝ)
    (ht : ∀ e, 0 < t e) (A : Matrix R E ℝ) : (retainedGram t A).rank = A.rank := by
  rw [retainedGram_factor t (fun e => (ht e).le), rank_self_mul_transpose]
  apply rank_mul_eq_left_of_isUnit_det
  rw [det_diagonal, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr fun e _ => (Real.sqrt_pos.mpr (ht e)).ne'

theorem retainedGram_posDef_iff_rank {R : Type*} [Fintype R] [DecidableEq R] (t : E → ℝ)
    (ht : ∀ e, 0 < t e) (A : Matrix R E ℝ) :
    (retainedGram t A).PosDef ↔ A.rank = Fintype.card R := by
  rw [(retainedGram_posSemidef t (fun e => (ht e).le) A).posDef_iff_isUnit,
    ← retainedGram_rank t ht A]
  refine ⟨rank_of_isUnit _, fun h => mulVec_surjective_iff_isUnit.mp ?_⟩
  change Function.Surjective (retainedGram t A).mulVecLin
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  simpa only [Matrix.rank, Module.finrank_pi] using h

omit [Fintype S] [Fintype L] [DecidableEq S] in
theorem retainedGram_fromRows (t : E → ℝ) (C : Matrix S E ℝ) (J : Matrix L E ℝ) :
    retainedGram t (fromRows C J) = fromBlocks
      (retainedGram t C) (retainedCross t C J) (retainedCross t C J)ᴴ (retainedGram t J) := by
  have hcross : (retainedCross t C J)ᴴ = J * diagonal t * Cᵀ := by
    simp only [conjTranspose_eq_transpose_of_trivial, retainedCross, transpose_mul,
      transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
  rw [hcross]
  ext (i | i) (j | j) <;> rfl

theorem retainedSchur_posSemidef (t : E → ℝ) (ht : ∀ e, 0 < t e)
    (C : Matrix S E ℝ) (J : Matrix L E ℝ) (hC : C.rank = Fintype.card S) :
    (retainedSchur t C J).PosSemidef := by
  have hA := (retainedGram_posDef_iff_rank t ht C).mpr hC
  letI := hA.isUnit.invertible
  apply (PosDef.fromBlocks₁₁ (retainedCross t C J) (retainedGram t J) hA).mp
  rw [← retainedGram_fromRows]
  exact retainedGram_posSemidef t (fun e => (ht e).le) (fromRows C J)

theorem retainedSchur_det [DecidableEq L] (t : E → ℝ) (ht : ∀ e, 0 < t e)
    (C : Matrix S E ℝ) (J : Matrix L E ℝ) (hC : C.rank = Fintype.card S) :
    (retainedGram t C).det * (retainedSchur t C J).det =
      (retainedGram t (fromRows C J)).det := by
  have hA := (retainedGram_posDef_iff_rank t ht C).mpr hC
  letI := hA.isUnit.invertible
  rw [retainedGram_fromRows, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
  rfl

theorem retainedSchur_posDef_iff_rank [DecidableEq L] (t : E → ℝ) (ht : ∀ e, 0 < t e)
    (C : Matrix S E ℝ) (J : Matrix L E ℝ) (hC : C.rank = Fintype.card S) :
    (retainedSchur t C J).PosDef ↔ (fromRows C J).rank = Fintype.card S + Fintype.card L := by
  rw [← Fintype.card_sum, ← retainedGram_posDef_iff_rank t ht,
    (retainedSchur_posSemidef t ht C J hC).posDef_iff_isUnit,
    (retainedGram_posSemidef t (fun e => (ht e).le) (fromRows C J)).posDef_iff_isUnit,
    isUnit_iff_isUnit_det, isUnit_iff_isUnit_det, ← retainedSchur_det t ht C J hC,
    isUnit_iff_ne_zero, isUnit_iff_ne_zero, mul_ne_zero_iff]
  exact ⟨fun h => ⟨((retainedGram_posDef_iff_rank t ht C).mpr hC).det_pos.ne', h⟩, And.right⟩

/-- The weighted row residual in the actual columns of the score and seam matrices. -/
def retainedResidual (t : E → ℝ) (C : Matrix S E ℝ) (J : Matrix L E ℝ)
    (u : S → ℝ) (v : L → ℝ) : E → ℝ :=
  diagonal (fun e => Real.sqrt (t e)) *ᵥ (Jᵀ *ᵥ v - Cᵀ *ᵥ u)

theorem retainedSchur_completeSquares (t : E → ℝ) (ht : ∀ e, 0 < t e)
    (C : Matrix S E ℝ) (J : Matrix L E ℝ) (hC : C.rank = Fintype.card S)
    (u : S → ℝ) (v : L → ℝ) :
    let r := retainedResidual t C J u v
    let w := -u + ((retainedGram t C)⁻¹ * retainedCross t C J) *ᵥ v
    r ⬝ᵥ r = w ⬝ᵥ ((retainedGram t C) *ᵥ w) + v ⬝ᵥ ((retainedSchur t C J) *ᵥ v) := by
  dsimp only
  have hA := (retainedGram_posDef_iff_rank t ht C).mpr hC
  letI := hA.isUnit.invertible
  have hs := schur_complement_eq₁₁ (retainedCross t C J) (retainedGram t J)
    (-u) v hA.1
  simp only [star_trivial, ← dotProduct_mulVec] at hs
  rw [← retainedGram_fromRows, retainedGram_factor t (fun e => (ht e).le),
    ← mulVec_mulVec, dotProduct_mulVec, ← vecMul_transpose] at hs
  have hrows :
      (fromRows C J)ᵀ *ᵥ ((-u) ⊕ᵥ v) = Jᵀ *ᵥ v - Cᵀ *ᵥ u := by
    ext e
    simp [mulVec, dotProduct, Fintype.sum_sum_type, Finset.sum_neg_distrib, sub_eq_add_neg,
      add_comm]
  have hleft : ((-u) ⊕ᵥ v) ᵥ* (fromRows C J * diagonal (fun e => Real.sqrt (t e))) =
      retainedResidual t C J u v := by
    rw [← mulVec_transpose, transpose_mul, diagonal_transpose, ← mulVec_mulVec, hrows]
    rfl
  rw [hleft, vecMul_transpose, transpose_mul, diagonal_transpose, ← mulVec_mulVec, hrows] at hs
  simpa only [retainedResidual, retainedSchur, ← mulVec_mulVec] using hs

/-- The conditional quadratic form is the attained minimum of the squared
Euclidean norm of the weighted residual over all seam coefficients. -/
theorem retainedSchur_isLeast_residual (t : E → ℝ) (ht : ∀ e, 0 < t e)
    (C : Matrix S E ℝ) (J : Matrix L E ℝ) (hC : C.rank = Fintype.card S) (v : L → ℝ) :
    IsLeast (Set.range fun u =>
      retainedResidual t C J u v ⬝ᵥ retainedResidual t C J u v)
      (v ⬝ᵥ ((retainedSchur t C J) *ᵥ v)) := by
  let u₀ := ((retainedGram t C)⁻¹ * retainedCross t C J) *ᵥ v
  refine ⟨⟨u₀, ?_⟩, ?_⟩
  · simpa [u₀] using retainedSchur_completeSquares t ht C J hC u₀ v
  · rintro _ ⟨u, rfl⟩
    dsimp only
    rw [retainedSchur_completeSquares t ht C J hC u v]
    have hA := (retainedGram_posDef_iff_rank t ht C).mpr hC
    apply le_add_of_nonneg_left
    simpa only [star_trivial] using hA.posSemidef.2 (-u + u₀)

/-- A score vector has zero conditional variance exactly when its row score
lies in the span of the seam rows. -/
theorem retainedSchur_null_iff (t : E → ℝ) (ht : ∀ e, 0 < t e)
    (C : Matrix S E ℝ) (J : Matrix L E ℝ) (hC : C.rank = Fintype.card S) (v : L → ℝ) :
    v ⬝ᵥ ((retainedSchur t C J) *ᵥ v) = 0 ↔ ∃ u, Jᵀ *ᵥ v = Cᵀ *ᵥ u := by
  obtain ⟨⟨u₀, hu₀⟩, hleast⟩ := retainedSchur_isLeast_residual t ht C J hC v
  have hD : IsUnit (diagonal fun e => Real.sqrt (t e)) := by
    rw [isUnit_iff_isUnit_det, det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun e _ => (Real.sqrt_pos.mpr (ht e)).ne'
  constructor
  · intro hv
    have hr := dotProduct_self_eq_zero.mp (hu₀.trans hv)
    have hEq := mulVec_injective_iff_isUnit.mpr hD
    refine ⟨u₀, sub_eq_zero.mp (hEq ?_)⟩
    simpa only [mulVec_zero, retainedResidual] using hr
  · rintro ⟨u, hu⟩
    have hle := hleast (Set.mem_range_self u)
    have hnonneg := (retainedSchur_posSemidef t ht C J hC).2 v
    simp only [retainedResidual, hu, sub_self, mulVec_zero, dotProduct_zero] at hle
    exact le_antisymm hle (by simpa only [star_trivial] using hnonneg)

omit [DecidableEq E] [DecidableEq S] [Fintype L] in
/-- Adding seam rows to the score leaves its actual phase coefficients
unchanged on the sewn displacement space. -/
theorem retainedScore_shear_onSeam (C : Matrix S E ℝ) (J : Matrix L E ℝ)
    (U : Matrix L S ℝ) (x : E → ℝ) (hx : C *ᵥ x = 0) :
    (J + U * C) *ᵥ x = J *ᵥ x := by
  rw [add_mulVec, ← mulVec_mulVec, hx, mulVec_zero, add_zero]

end UV
