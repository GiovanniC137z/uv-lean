import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic

/-! A rectangular full-column-rank routing actually contains a square
invertible selected row block. No selected minor is postulated. -/
noncomputable section
namespace UV

theorem exists_invertible_row_minor {I : Type*} [Fintype I]
    {L : ℕ} (C : Matrix I (Fin L) ℝ) (hC : C.rank = L) :
    ∃ s : Fin L ↪ I, Matrix.det (C.submatrix s id) ≠ 0 := by
  classical
  have htop : Submodule.span ℝ (Set.range C.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← C.rank_eq_finrank_span_row, hC]
    simp
  obtain ⟨J, a, ha, hspan, hli⟩ := exists_linearIndependent' ℝ C.row
  letI : Finite J := Finite.of_injective a ha
  letI : Fintype J := Fintype.ofFinite J
  let b : Module.Basis J ℝ (Fin L → ℝ) :=
    Module.Basis.mk hli (by rw [hspan, htop])
  have hcard : Fintype.card J = L := by
    rw [← Module.finrank_eq_card_basis b]
    simp
  let e : Fin L ≃ J := (finCongr hcard.symm).trans (Fintype.equivFin J).symm
  refine ⟨⟨a ∘ e, ha.comp e.injective⟩, ?_⟩
  have hrows : LinearIndependent ℝ (C.submatrix (a ∘ e) id).row := by
    simpa only [Function.comp_def, Matrix.row, Matrix.submatrix_apply, id_eq] using
      hli.comp e e.injective
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hrows))

theorem exists_invertible_row_minor_of_injective {I : Type*} [Fintype I]
    {L : ℕ} (C : Matrix I (Fin L) ℝ) (hC : Function.Injective C.mulVec) :
    ∃ s : Fin L ↪ I, Matrix.det (C.submatrix s id) ≠ 0 := by
  apply exists_invertible_row_minor C
  change Module.finrank ℝ (LinearMap.range C.mulVecLin) = L
  rw [LinearMap.finrank_range_of_inj hC]
  simp

end UV
