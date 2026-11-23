import UV.ContinueCollarCompactSpectrum
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Construct an orthonormal eigenbasis of a compact real symmetric
operator, also when some eigenspaces have multiplicity greater than one. -/

noncomputable section

open Set
open scoped InnerProductSpace

namespace UV.CollarEigenmode

universe u

theorem compact_symmetric_eigenbasis {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H) (hc : IsCompactOperator T) (hs : T.toLinearMap.IsSymmetric) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℝ H) (E : ι → ℝ),∀ i,T (b i)=E i • b i := by
  let V := fun e : ℝ => Module.End.eigenspace T.toLinearMap e
  have hV (e : ℝ) : IsClosed (V e : Set H) := by
    have he : (V e : Set H) = {x : H | T x=e • x} := by
      ext x; exact Module.End.mem_eigenspace_iff
    rw [he]
    exact isClosed_eq T.continuous (continuous_const.smul continuous_id)
  letI (e : ℝ) : CompleteSpace (V e) := (hV e).completeSpace_coe
  choose J b _ using fun e : ℝ => exists_hilbertBasis ℝ (V e)
  let v := fun i : Σ e,J e => ((b i.1 i.2 : V i.1) : H)
  have ho : Orthonormal ℝ v := hs.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal fun e => (b e).orthonormal
  let M := (Submodule.span ℝ (range v)).topologicalClosure
  have hin (e : ℝ) : V e ≤ M := by
    let N := M.comap (V e).subtype
    have hN : IsClosed (N : Set (V e)) := (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val
    have hspan : Submodule.span ℝ (range (b e)) ≤ N := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨e,i⟩,rfl⟩)
    have H := (Submodule.span ℝ (range (b e))).topologicalClosure_minimal hspan hN
    rw [(b e).dense_span] at H
    exact fun x hx => H (Submodule.mem_top : (⟨x,hx⟩ : V e) ∈ (⊤ : Submodule ℝ (V e)))
  have hall := (⨆ e,V e).topologicalClosure_minimal (iSup_le hin) (Submodule.isClosed_topologicalClosure _)
  rw [show (⨆ e,V e).topologicalClosure = ⊤ from compact_symmetric_dense_eigenspaces T hc hs] at hall
  let B := HilbertBasis.mk ho hall
  refine ⟨_,B,fun i => i.1,fun i => ?_⟩
  have he : B i=v i := congrFun (HilbertBasis.coe_mk ho hall) i
  rw [he]
  exact Module.End.mem_eigenspace_iff.mp (b i.1 i.2).property

end UV.CollarEigenmode
