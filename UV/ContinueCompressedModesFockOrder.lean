import UV.ContinueCompressedModesFockWick

/-! Every pairing uses different normal-ordered vertices. Its first slot
precedes its second in the original operator product, including terms
in which either vertex has already lost its partner to an earlier edge. -/

namespace UV.FermionWick
variable {α : Type*}

def ordered (R : α→α→Prop) : List (Block α) → Prop
  | [] => True
  | a::xs => (∀ x∈fields a, ∀ y∈slots xs, R x y) ∧ ordered R xs

private theorem hit_mem {xs : List (Block α)} {c : Cut α} (hc : c∈cuts xs) : c.hit∈slots xs :=
  (cut_slots_perm xs c hc).mem_iff.mp (List.mem_cons_self ..)

private theorem rest_subset {xs : List (Block α)} {c : Cut α} (hc : c∈cuts xs) : slots c.rest ⊆ slots xs :=
  fun _ hz => (cut_slots_perm xs c hc).mem_iff.mp (List.mem_cons_of_mem _ hz)

theorem cuts_ordered (R : α→α→Prop) (xs : List (Block α)) (ho : ordered R xs)
    (c : Cut α) (hc : c∈cuts xs) : ordered R c.rest := by
  induction xs generalizing c with
  | nil => simp [cuts] at hc
  | cons a xs ih =>
    obtain ⟨ha,ho⟩ := ho
    cases a with
    | one x =>
      rcases List.mem_cons.mp hc with rfl|h
      · exact ho
      · obtain ⟨c',hc',rfl⟩ := List.mem_map.mp h
        exact ⟨fun x hx y hy => ha x hx y (rest_subset hc' hy),ih ho c' hc'⟩
    | normal x y =>
      rcases List.mem_cons.mp hc with rfl|h
      · exact ⟨fun z hz w hw => ha z (by simpa [fields] using (Or.inr (by simpa [fields] using hz) : z=x ∨ z=y)) w hw,ho⟩
      rcases List.mem_cons.mp h with rfl|h
      · exact ⟨fun z hz w hw => ha z (by simpa [fields] using (Or.inl (by simpa [fields] using hz) : z=x ∨ z=y)) w hw,ho⟩
      · obtain ⟨c',hc',rfl⟩ := List.mem_map.mp h
        exact ⟨fun x hx y hy => ha x hx y (rest_subset hc' hy),ih ho c' hc'⟩

theorem successor_order (R : α→α→Prop) (xs : List (Block α)) (ho : ordered R xs)
    (p : Edge α × List (Block α)) (hp : p∈successors xs) :
    R p.1.first p.1.second ∧ ordered R p.2 := by
  cases xs with
  | nil => simp [successors] at hp
  | cons a xs =>
    obtain ⟨ha,ht⟩ := ho
    cases a with
    | one x =>
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
      exact ⟨ha x (by simp [fields]) c.hit (hit_mem hc),cuts_ordered R xs ht c hc⟩
    | normal x y =>
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
      refine ⟨ha x (by simp [fields]) c.hit (hit_mem hc),?_,cuts_ordered R xs ht c hc⟩
      intro z hz w hw
      have hz' : z=y := by simpa [fields] using hz
      exact ha z (by simp [fields,hz']) w (rest_subset hc hw)

theorem matching_edges_ordered (R : α→α→Prop) (n : ℕ) (xs : List (Block α)) (ho : ordered R xs)
    {es : List (Edge α)} (H : es∈matchings n xs) : ∀ e∈es, R e.first e.second := by
  induction n generalizing xs es with
  | zero =>
    cases xs <;> simp [matchings] at H
    simp [H]
  | succ n ih =>
    cases xs with
    | nil => simp [matchings] at H; simp [H]
    | cons b xs =>
      obtain ⟨p,hp,h⟩ := List.mem_flatMap.mp H
      obtain ⟨es,he,rfl⟩ := List.mem_map.mp h
      obtain ⟨h₁,h₂⟩ := successor_order R (b::xs) ho p hp
      intro e hm
      rcases List.mem_cons.mp hm with rfl|h
      · exact h₁
      · exact ih p.2 h₂ he e h

end UV.FermionWick
