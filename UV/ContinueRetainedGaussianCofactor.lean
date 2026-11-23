import UV.ContinueRetainedGaussianSchur

/-! The inverse Schur trace is the sum of retained score deletion minors.
Deleting a score preserves every seam row. -/

noncomputable section

open Matrix
open scoped Matrix BigOperators

namespace UV

private theorem retained_adjugate_diag {R : Type*} [Fintype R] [DecidableEq R]
    (A : Matrix R R ℝ) (i : R) :
    A.adjugate i i =
      (A.submatrix (Subtype.val : {j // j ≠ i} → R) Subtype.val).det := by
  let e := Equiv.sumCompl (fun j : R => j = i)
  let A' := A.updateRow i (Pi.single i 1)
  let P : Matrix {j : R // j ≠ i} {j : R // j ≠ i} ℝ := A.submatrix Subtype.val Subtype.val
  have he : A'.submatrix e e = fromBlocks (1 : Matrix {j // j = i} {j // j = i} ℝ) 0
      (A.submatrix (Subtype.val : {j // j ≠ i} → R) (Subtype.val : {j // j = i} → R)) P := by
    ext (j | j) (k | k)
    · have hjk : j = k := Subtype.ext (j.prop.trans k.prop.symm)
      simp [A', e, Equiv.sumCompl_apply_inl, k.prop, hjk]
    · simp [A', e, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr, j.prop, k.prop]
    · simp [A', e, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr, j.prop]
    · simp [A', P, e, Equiv.sumCompl_apply_inr, j.prop]
  rw [adjugate_apply]
  change A'.det = P.det
  rw [← det_submatrix_equiv_self e A', he, det_fromBlocks_zero₁₂, det_one, one_mul]

variable {E S L : Type*} [Fintype E] [Fintype S] [Fintype L]
variable [DecidableEq E] [DecidableEq S] [DecidableEq L]

theorem retainedSchur_inv_eq_block (t : E → ℝ) (ht : ∀ e, 0 < t e)
    (C : Matrix S E ℝ) (J : Matrix L E ℝ) (hC : C.rank = Fintype.card S)
    (hM : (fromRows C J).rank = Fintype.card S + Fintype.card L) :
    (retainedGram t (fromRows C J))⁻¹.submatrix Sum.inr Sum.inr = (retainedSchur t C J)⁻¹ := by
  have hA := (retainedGram_posDef_iff_rank t ht C).mpr hC
  have hQ := (retainedSchur_posDef_iff_rank t ht C J hC).mpr hM
  have hB := (retainedGram_posDef_iff_rank t ht (fromRows C J)).mpr (by simpa using hM)
  letI := hA.isUnit.invertible
  letI : Invertible (retainedGram t J - (retainedCross t C J)ᴴ * ⅟(retainedGram t C) *
      retainedCross t C J) := by
    rw [invOf_eq_nonsing_inv]
    exact hQ.isUnit.invertible
  letI : Invertible (fromBlocks (retainedGram t C) (retainedCross t C J)
      (retainedCross t C J)ᴴ (retainedGram t J)) := by
    rw [← retainedGram_fromRows]
    exact hB.isUnit.invertible
  rw [retainedGram_fromRows, ← invOf_eq_nonsing_inv, invOf_fromBlocks₁₁_eq]
  change ⅟(retainedGram t J - (retainedCross t C J)ᴴ * ⅟(retainedGram t C) *
    retainedCross t C J) = _
  rw [invOf_eq_nonsing_inv, invOf_eq_nonsing_inv]
  rfl

/-- Rows of the retained matrix after erasing a single loop score. -/
def retainedDeleteScore (C : Matrix S E ℝ) (J : Matrix L E ℝ) (j : L) :
    Matrix (S ⊕ {l : L // l ≠ j}) E ℝ :=
  fromRows C (J.submatrix Subtype.val id)

private def retainedDeleteScoreEquiv (j : L) : (S ⊕ {l : L // l ≠ j}) ≃
    {a : S ⊕ L // a ≠ Sum.inr j} where
  toFun := fun a => match a with
    | Sum.inl s => ⟨Sum.inl s, Sum.inl_ne_inr⟩
    | Sum.inr l => ⟨Sum.inr l.1, fun h => l.2 (Sum.inr.inj h)⟩
  invFun := fun a => match a with
    | ⟨Sum.inl s, _⟩ => Sum.inl s
    | ⟨Sum.inr l, hl⟩ => Sum.inr ⟨l, fun h => hl (congrArg Sum.inr h)⟩
  left_inv := by rintro (s | l) <;> rfl
  right_inv := by rintro ⟨(s | l), _⟩ <;> rfl

theorem retainedGram_deleteScore_det (t : E → ℝ) (C : Matrix S E ℝ) (J : Matrix L E ℝ)
    (j : L) :
    (retainedGram t (retainedDeleteScore C J j)).det =
      ((retainedGram t (fromRows C J)).submatrix
        (Subtype.val : {a : S ⊕ L // a ≠ Sum.inr j} → S ⊕ L) Subtype.val).det := by
  let e : (S ⊕ {l : L // l ≠ j}) ≃ {a : S ⊕ L // a ≠ Sum.inr j} :=
    retainedDeleteScoreEquiv j
  rw [← det_submatrix_equiv_self e]
  apply congrArg Matrix.det
  ext (s | l) (s' | l') <;> rfl

theorem retainedSchur_trace_inv_cofactor (t : E → ℝ) (ht : ∀ e, 0 < t e)
    (C : Matrix S E ℝ) (J : Matrix L E ℝ) (hC : C.rank = Fintype.card S)
    (hM : (fromRows C J).rank = Fintype.card S + Fintype.card L) :
    (retainedSchur t C J)⁻¹.trace =
      ∑ j : L, (retainedGram t (retainedDeleteScore C J j)).det /
        (retainedGram t (fromRows C J)).det := by
  rw [← retainedSchur_inv_eq_block t ht C J hC hM, Matrix.trace]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.diag_apply, Matrix.submatrix_apply, Matrix.inv_def, Matrix.smul_apply,
    Ring.inverse_eq_inv, retained_adjugate_diag, retainedGram_deleteScore_det]
  rw [smul_eq_mul, div_eq_mul_inv, mul_comm]

end UV
