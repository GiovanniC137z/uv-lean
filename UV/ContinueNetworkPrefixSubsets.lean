import Mathlib.Data.Fin.Tuple.Sort

/-! Every nonempty set of routed factors occurs as an initial segment
of an actual ordering of the finite edge labels. -/

namespace UV

theorem route_subset_ordering {m : ℕ} (S : Finset (Fin m)) :
    ∃ σ : Equiv.Perm (Fin m), ∀ i : Fin m, σ i ∈ S ↔ i.val < S.card := by
  classical
  let f (j : Fin m) : ℕ := if j ∈ S then 0 else 1
  let σ := Tuple.sort f
  have hsorted : Monotone (f ∘ σ) := Tuple.monotone_sort f
  have hcard : Fintype.card {i : Fin m // (f ∘ σ) i ≤ 0} = S.card := by
    let e : {i : Fin m // (f ∘ σ) i ≤ 0} ≃ (↑S : Set (Fin m)) :=
      Equiv.subtypeEquiv σ (fun i => by
        change f (σ i) ≤ 0 ↔ σ i ∈ S
        by_cases h : σ i ∈ S <;> simp [f,h])
    simpa using Fintype.card_congr e
  refine ⟨σ, fun i => ?_⟩
  have H := Tuple.lt_card_le_iff_apply_le_of_monotone (f ∘ σ) 0 hsorted i
  rw [hcard] at H
  by_cases hi : σ i ∈ S <;> simpa [Function.comp_apply,f,hi] using H.symm

theorem route_subset_is_nonempty_prefix {m : ℕ} (S : Finset (Fin m)) (hS : S.Nonempty) :
    ∃ (σ : Equiv.Perm (Fin m)) (j : Fin m), j.val + 1 = S.card ∧
      (Finset.univ.filter (fun i : Fin m => i ≤ j)).map σ.toEmbedding = S := by
  obtain ⟨σ,hσ⟩ := route_subset_ordering S
  have hp := Finset.card_pos.mpr hS
  have hm : S.card ≤ m := by
    simpa only [Fintype.card_fin] using S.card_le_univ
  let j : Fin m := ⟨S.card - 1,by omega⟩
  have hj : j.val + 1 = S.card := by dsimp [j]; omega
  refine ⟨σ,j,hj,?_⟩
  ext e
  rw [Finset.mem_map]
  constructor
  · rintro ⟨i,hi,rfl⟩
    have he : i ≤ j := (Finset.mem_filter.mp hi).2
    have hval : i.val ≤ j.val := he
    exact (hσ i).2 (by omega)
  · intro he
    let i := σ.symm e
    have hs : σ i = e := σ.apply_symm_apply e
    have hi : i.val < S.card := (hσ i).1 (hs ▸ he)
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,show i.val ≤ j.val by omega⟩,hs⟩

theorem route_prefix_mem_iff {m : ℕ} (σ : Equiv.Perm (Fin m)) (j e : Fin m) :
    e ∈ (Finset.univ.filter (fun i : Fin m => i ≤ j)).map σ.toEmbedding ↔ σ.symm e ≤ j := by
  rw [Finset.mem_map]
  constructor
  · rintro ⟨i,hi,rfl⟩
    simpa only [Equiv.toEmbedding_apply,Equiv.symm_apply_apply] using (Finset.mem_filter.mp hi).2
  · intro h
    exact ⟨σ.symm e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,σ.apply_symm_apply e⟩

end UV
