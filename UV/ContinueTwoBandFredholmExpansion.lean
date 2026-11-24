import UV.ContinueTwoBandFredholmMinors
import Mathlib.LinearAlgebra.Multilinear.Basic

/-! Principal-minor expansion for the finite-section Fredholm limit.
The section on the internal label can differ from the external section. -/

noncomputable section
open Matrix Filter Set
open scoped Topology InnerProductSpace

namespace UV.SectorPlane

private theorem principal_minor_piecewise {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (s : Finset I) :
    Matrix.det (s.piecewise A (1 : Matrix I I ℂ)) = (A.submatrix (fun i : s => i.val) (fun j : s => j.val)).det := by
  classical
  let e := Equiv.Set.sumCompl (s : Set I)
  let B : Matrix s ((s : Set I)ᶜ : Set I) ℂ := fun i j => A i j
  have he : Matrix.submatrix (s.piecewise A (1 : Matrix I I ℂ)) e e =
      Matrix.fromBlocks (A.submatrix (fun i : s => i.val) (fun j : s => j.val)) B 0 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · change (if i.val ∈ s then A i.val else (1:Matrix I I ℂ) i.val) j.val = A i.val j.val
      rw [if_pos (show i.val ∈ s from i.property)]
    · change (if i.val ∈ s then A i.val else (1:Matrix I I ℂ) i.val) j.val = A i.val j.val
      rw [if_pos (show i.val ∈ s from i.property)]
    · have hne : i.val ≠ j.val := fun h => i.property (h ▸ j.property)
      change (if i.val ∈ s then A i.val else (1:Matrix I I ℂ) i.val) j.val = 0
      rw [if_neg (show i.val ∉ s from i.property),Matrix.one_apply_ne hne]
    · change (if i.val ∈ s then A i.val else (1:Matrix I I ℂ) i.val) j.val = (1:Matrix _ _ ℂ) i j
      simp only [if_neg (show i.val ∉ s from i.property),Matrix.one_apply,Subtype.ext_iff]
  rw [←Matrix.det_submatrix_equiv_self e,he,Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,mul_one]

theorem schur_det_principal_minors {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) :
    (1+A).det = ∑ s : Finset I, (A.submatrix (fun i : s => i.val) (fun j : s => j.val)).det := by
  rw [add_comm]
  have h := (Matrix.detRowAlternating (R:=ℂ) (n:=I)).toMultilinearMap.map_add_univ
    (A : I → I → ℂ) (1 : Matrix I I ℂ)
  exact h.trans (Finset.sum_congr rfl fun s _ => principal_minor_piecewise A s)

theorem schur_cut_minor_sum {I : Type*} [DecidableEq I] (s : Finset I)
    (A : I → I → ℂ) :
    (1 + Matrix.of (fun i j : s => A i j)).det =
      ∑ t ∈ s.powerset, Matrix.det (fun i j : t => A i j) := by
  classical
  rw [schur_det_principal_minors]
  let e : Finset s ≃ {t : Finset I // t ∈ s.powerset} :=
    { toFun := fun t => ⟨t.map ⟨Subtype.val,Subtype.val_injective⟩,
          Finset.mem_powerset.mpr (by intro i hi; obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hi; exact j.property)⟩
      invFun := fun t => s.attach.filter (fun i => i.val ∈ t.val)
      left_inv := by intro t; ext i; simp
      right_inv := by
        intro t
        apply Subtype.ext
        ext i
        have ht := Finset.mem_powerset.mp t.property
        simp only [Finset.mem_map,Finset.mem_filter,Finset.mem_attach,true_and,Function.Embedding.coeFn_mk]
        exact ⟨fun ⟨j,hj,he⟩ => he ▸ hj, fun hi => ⟨⟨i,ht hi⟩,hi,rfl⟩⟩ }
  rw [←Finset.sum_coe_sort s.powerset (fun t => Matrix.det (fun i j : t => A i j))]
  apply Fintype.sum_equiv e
  intro t
  let v : t ≃ (e t).val :=
    { toFun := fun i => ⟨i.val.val,Finset.mem_map.mpr ⟨i.val,i.property,rfl⟩⟩
      invFun := fun j => ⟨⟨j.val,(Finset.mem_powerset.mp (e t).property) j.property⟩, by
        obtain ⟨i,hi,he⟩ := Finset.mem_map.mp j.property
        exact (show i = (⟨j.val,(Finset.mem_powerset.mp (e t).property) j.property⟩ : s) from Subtype.ext he) ▸ hi⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Matrix.det_submatrix_equiv_self v (fun i j : (e t).val => A i j)

end UV.SectorPlane
