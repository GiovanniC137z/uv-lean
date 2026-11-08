import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-! A positive one-particle resolution supplies a Gram residue, independently
of the virtual kernel. The normalization below is constructed by the finite
Hermitian spectral theorem, retaining an invertible map on null directions. -/

noncomputable section
open Matrix
open scoped ComplexOrder InnerProductSpace

namespace UV

variable {n : Type*}

def physicalResidueGram {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : n → E) : Matrix n n ℂ := (Matrix.gram ℂ v).transpose

theorem physicalResidueGram_posSemidef [Fintype n] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v : n → E) :
    (physicalResidueGram v).PosSemidef :=
  (Matrix.posSemidef_gram ℂ v).transpose

theorem physicalResidueGram_field_map [Fintype n] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : n → E) (T : Matrix n n ℂ) :
    physicalResidueGram (fun i => ∑ j, T i j • v j) =
      T * physicalResidueGram v * T.conjTranspose := by
  ext i j
  simp only [physicalResidueGram, Matrix.transpose_apply, Matrix.gram_apply,
    inner_sum, sum_inner, inner_smul_left, inner_smul_right,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [starRingEnd_apply]
  ring

/-- The overlap series is genuine Hilbert-space Parseval, so this covers
finite and infinite positive one-particle resolutions alike. -/
theorem physicalResidueGram_overlap_sum {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (b : HilbertBasis ι ℂ E) (v : n → E) (i j : n) :
    HasSum (fun α => ⟪v j, b α⟫_ℂ * ⟪b α, v i⟫_ℂ) (physicalResidueGram v i j) :=
  b.hasSum_inner_mul_inner (v j) (v i)

variable [Fintype n] [DecidableEq n]

def residueSpectralMatrix (U : Matrix.unitaryGroup n ℂ) (d : n → ℝ) : Matrix n n ℂ :=
  (U : Matrix n n ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) * star (U : Matrix n n ℂ)

theorem residueSpectralMatrix_mul (U : Matrix.unitaryGroup n ℂ) (d e : n → ℝ) :
    residueSpectralMatrix U d * residueSpectralMatrix U e =
      residueSpectralMatrix U (fun i => d i * e i) := by
  unfold residueSpectralMatrix
  have hU := unitary.coe_star_mul_self U
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star (U : Matrix n n ℂ)), hU, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  simp only [Complex.ofReal_mul]

theorem residueSpectralMatrix_adjoint (U : Matrix.unitaryGroup n ℂ) (d : n → ℝ) :
    (residueSpectralMatrix U d).conjTranspose = residueSpectralMatrix U d := by
  change ((U : Matrix n n ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) *
    (U : Matrix n n ℂ).conjTranspose).conjTranspose = _
  apply Matrix.isHermitian_mul_mul_conjTranspose (U : Matrix n n ℂ)
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  simp [isSelfAdjoint_iff]

def residueNormalizerScalar (ev : ℝ) : ℝ := if ev = 0 then 1 else (Real.sqrt ev)⁻¹

theorem residueNormalizerScalar_ne_zero {ev : ℝ} (hev : 0 ≤ ev) :
    residueNormalizerScalar ev ≠ 0 := by
  unfold residueNormalizerScalar
  split_ifs with h
  · norm_num
  · exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne hev (Ne.symm h))))

theorem residueNormalizerScalar_normalizes {ev : ℝ} (hev : 0 ≤ ev) :
    residueNormalizerScalar ev * ev * residueNormalizerScalar ev =
      if ev = 0 then 0 else 1 := by
  unfold residueNormalizerScalar
  split_ifs with h
  · simp [h]
  · have hs : Real.sqrt ev ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne hev (Ne.symm h)))
    have hsq := Real.sq_sqrt hev
    field_simp
    nlinarith

/-- Constructed invertible normalization, together with its spectral range
projection. It is the identity on the range of the original residue. -/
theorem positive_residue_matrix_normalization {Z : Matrix n n ℂ} (hZ : Z.PosSemidef) :
    ∃ T P : Matrix n n ℂ, T.det ≠ 0 ∧
      T * Z * T.conjTranspose = P ∧ P.conjTranspose = P ∧ P * P = P ∧
      P * Z = Z ∧
      (∀ x : n → ℂ, P.mulVec (Z.mulVec x) = Z.mulVec x) ∧
      (∀ x : n → ℂ, Z.mulVec x = 0 → P.mulVec x = 0) := by
  let U := hZ.isHermitian.eigenvectorUnitary
  let ev := hZ.isHermitian.eigenvalues
  let t (i : n) := residueNormalizerScalar (ev i)
  let p (i : n) : ℝ := if ev i = 0 then 0 else 1
  let T := residueSpectralMatrix U t
  let P := residueSpectralMatrix U p
  have hev (i : n) : 0 ≤ ev i := hZ.eigenvalues_nonneg i
  have he : Z = residueSpectralMatrix U ev := hZ.isHermitian.spectral_theorem
  have ht : T.conjTranspose = T := residueSpectralMatrix_adjoint U t
  have hdetU : (U : Matrix n n ℂ).det ≠ 0 := by
    exact isUnit_iff_ne_zero.mp (Matrix.isUnit_det_of_left_inverse (unitary.coe_star_mul_self U))
  have hdet : T.det ≠ 0 := by
    dsimp [T, residueSpectralMatrix]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]
    apply mul_ne_zero
    · apply mul_ne_zero hdetU
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      exact_mod_cast residueNormalizerScalar_ne_zero (hev i)
    · exact star_ne_zero.mpr hdetU
  have hTZT : T * Z * T.conjTranspose = P := by
    rw [ht, he]
    change residueSpectralMatrix U t * residueSpectralMatrix U ev *
      residueSpectralMatrix U t = residueSpectralMatrix U p
    rw [residueSpectralMatrix_mul, residueSpectralMatrix_mul]
    congr 1
    funext i
    exact residueNormalizerScalar_normalizes (hev i)
  have hPP : P * P = P := by
    dsimp [P]
    rw [residueSpectralMatrix_mul]
    congr 1
    funext i
    dsimp [p]
    split_ifs <;> norm_num
  have hPZ : P * Z = Z := by
    rw [he]
    change residueSpectralMatrix U p * residueSpectralMatrix U ev = residueSpectralMatrix U ev
    rw [residueSpectralMatrix_mul]
    congr 1
    funext i
    dsimp [p]
    split_ifs with h
    · simp [h]
    · simp
  have hTZ : T * Z = Z * T := by
    rw [he]
    change residueSpectralMatrix U t * residueSpectralMatrix U ev =
      residueSpectralMatrix U ev * residueSpectralMatrix U t
    rw [residueSpectralMatrix_mul, residueSpectralMatrix_mul]
    congr 1
    funext i
    exact mul_comm _ _
  refine ⟨T, P, hdet, hTZT, residueSpectralMatrix_adjoint U p, hPP, hPZ,
    (fun x => by rw [Matrix.mulVec_mulVec, hPZ]), ?_⟩
  intro x hx
  rw [← hTZT, ht, Matrix.mul_assoc, ← hTZ]
  simp only [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

theorem residue_rank_congruence (Z T : Matrix n n ℂ) (hT : T.det ≠ 0) :
    (T * Z * T.conjTranspose).rank = Z.rank := by
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _
      (isUnit_iff_ne_zero.mpr (by simpa [Matrix.det_conjTranspose] using hT)),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (isUnit_iff_ne_zero.mpr hT)]

theorem singular_residue_cannot_normalize_identity (Z T : Matrix n n ℂ)
    (hZ : Z.rank < Fintype.card n) (hT : T.det ≠ 0) :
    T * Z * T.conjTranspose ≠ 1 := by
  intro he
  have hr := residue_rank_congruence Z T hT
  rw [he, Matrix.rank_one] at hr
  omega

/-- The dual source is changed by the inverse adjoint.  This is a genuine
Hermitian source pairing, distinct from the field congruence. -/
theorem physical_field_source_duality {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E ≃L[ℂ] E) (J φ : E) :
    ⟪T.symm.toContinuousLinearMap.adjoint J, T φ⟫_ℂ +
        ⟪T φ, T.symm.toContinuousLinearMap.adjoint J⟫_ℂ =
      ⟪J, φ⟫_ℂ + ⟪φ, J⟫_ℂ := by
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  simp only [ContinuousLinearEquiv.coe_coe, T.symm_apply_apply]

end UV
