import UV.ContinueCompressedModesFockCycles

/-! Explicit finite placement of all mode labels of every source vertex.
Single contractions carry the original fermionic sign and a bounded
one-sided evolution on a strictly ordered time simplex. -/

noncomputable section
namespace UV.FermionWick
variable {ν ι α : Type*}

def placements [Fintype ι] (Q : ν→ι→ι→ℂ) :
    List ν → List (ℂ × List (Block (Slot ν ι)))
  | [] => [(1,[])]
  | i::xs => (Finset.univ : Finset (ι×ι)).toList.flatMap (fun ab =>
      (placements Q xs).map (fun p => (Q i ab.1 ab.2*p.1,vertex i ab.1 ab.2::p.2)))

private theorem sum_flat {a:Type*} (l : List a) (g : a→List ℂ) :
    (l.flatMap g).sum=(l.map (fun x => (g x).sum)).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem sum_over [Fintype ι] (Q : ν→ι→ι→ℂ) (xs : List ν)
    (f : List (Block (Slot ν ι))→ℂ) : resolvedSum Q xs f =
    ((placements Q xs).map (fun p => p.1*f p.2)).sum := by
  induction xs generalizing f with
  | nil => simp [resolvedSum,placements]
  | cons i xs ih =>
    rw [resolvedSum,placements]
    simp only [List.map_flatMap,sum_flat,Function.comp_def,List.map_map,Finset.sum_map_toList,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [ih]
    simp only [smul_eq_mul]
    induction placements Q xs with
    | nil => simp
    | cons p ps ih => simp [ih,mul_add,mul_assoc]

theorem transfer_pairings [Fintype ι] [DecidableEq ι] (band : ι→Bool) (E : ι→ℝ) (t : ν→ℝ)
    (Q : ν→ι→ι→ℂ) (xs : List ν) :
    vacuum (transfer band E t Q xs) =
     ((placements Q xs).map (fun p => p.1*((matchings (slots p.2).length p.2).map
       (amplitude (seaCovariance band E t))).sum)).sum := by
  rw [transfer_wick,sum_over]

theorem placement_source [Fintype ι] [Nonempty ι] (Q : ν→ι→ι→ℂ) (xs : List ν) (hxs : xs.Nodup)
    (p : ℂ × List (Block (Slot ν ι))) (hp : p∈placements Q xs) :
    ∃ a b : ν→ι, p.2=sourceWord xs a b ∧ p.1=(xs.map (fun i => Q i (a i) (b i))).prod := by
  classical
  induction xs generalizing p with
  | nil =>
    simp [placements] at hp
    subst p
    exact ⟨fun _ => Classical.arbitrary ι,fun _ => Classical.arbitrary ι,rfl,rfl⟩
  | cons i xs ih =>
    obtain ⟨ab,_,h⟩ := List.mem_flatMap.mp hp
    obtain ⟨p',hp',rfl⟩ := List.mem_map.mp h
    obtain ⟨a,b,hl,hw⟩ := ih (List.nodup_cons.mp hxs).2 p' hp'
    let a' := Function.update a i ab.1
    let b' := Function.update b i ab.2
    have he (j : ν) (hj : j∈xs) : a' j=a j ∧ b' j=b j := by
      have hji : j≠i := by rintro rfl; exact (List.nodup_cons.mp hxs).1 hj
      simp [a',b',hji]
    refine ⟨a',b',?_,?_⟩
    · simp only [sourceWord,List.map_cons,hl]
      congr 1
      · simp [a',b']
      · exact List.map_congr_left (fun j hj => by rw [(he j hj).1,(he j hj).2])
    · simp only [List.map_cons,List.prod_cons,hw]
      congr 1
      · simp [a',b']
      · congr 1
        exact List.map_congr_left (fun j hj => by rw [(he j hj).1,(he j hj).2])

private theorem cut_sign (xs : List (Block α)) (c : Cut α) (hc : c∈cuts xs) : c.sign=1 ∨ c.sign= -1 := by
  induction xs generalizing c with
  | nil => simp [cuts] at hc
  | cons a xs ih =>
    cases a with
    | one x =>
      simp only [cuts,List.mem_cons,List.mem_map] at hc
      rcases hc with rfl|⟨c,hc,rfl⟩
      · exact Or.inl rfl
      · rcases ih c hc with h|h <;> simp [h]
    | normal x y =>
      simp only [cuts,List.mem_cons,List.mem_map] at hc
      rcases hc with rfl|rfl|⟨c,hc,rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact ih c hc

private theorem successor_sign (xs : List (Block α)) (p : Edge α × List (Block α)) (hp : p∈successors xs) :
    p.1.sign=1 ∨ p.1.sign= -1 := by
  cases xs with
  | nil => simp [successors] at hp
  | cons a xs =>
    cases a with
    | one x => obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp; exact cut_sign xs c hc
    | normal x y =>
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
      rcases cut_sign xs c hc with h|h <;> simp [h]

theorem matching_signs (n : ℕ) (xs : List (Block α)) (es : List (Edge α)) (h : es∈matchings n xs) :
    ∀e∈es, e.sign=1 ∨ e.sign= -1 := by
  induction n generalizing xs es with
  | zero => cases xs <;> simp [matchings] at h; simp [h]
  | succ n ih =>
    cases xs with
    | nil => simp [matchings] at h; simp [h]
    | cons a xs =>
      obtain ⟨p,hp,H⟩ := List.mem_flatMap.mp h
      obtain ⟨es,he,rfl⟩ := List.mem_map.mp H
      intro e hm
      rcases List.mem_cons.mp hm with rfl|hm
      · exact successor_sign _ _ hp
      · exact ih p.2 es he e hm

theorem matching_amplitude_contracts [DecidableEq ι] (band : ι→Bool) (E : ι→ℝ) (hE : ∀i,0≤E i)
    (t : ν→ℝ) (n : ℕ) (xs : List (Block (Slot ν ι)))
    (ho : ordered (fun x y => t y.vertex<t x.vertex) xs)
    (es : List (Edge (Slot ν ι))) (H : es∈matchings n xs) :
    ‖amplitude (seaCovariance band E t) es‖≤1 := by
  have horder := matching_edges_ordered _ n xs ho H
  have hsign := matching_signs n xs es H
  have he (e) (he:e∈es) : ‖edgeWeight (seaCovariance band E t) e‖≤1 := by
    rw [edgeWeight,norm_mul]
    have h : ‖(e.sign:ℂ)‖=1 := by rcases hsign e he with hh|hh <;> simp [hh]
    rw [h,one_mul,seaCovariance]
    split_ifs
    · rw [Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le,Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hE _)) (sub_nonneg.mpr (horder e he).le)
    · simp
  clear ho H horder hsign
  induction es with
  | nil => simp [amplitude]
  | cons e es ih =>
    have htail := ih (fun x hx => he x (List.mem_cons_of_mem _ hx))
    change ‖edgeWeight _ e * amplitude _ es‖≤1
    rw [norm_mul]
    exact (mul_le_mul (he e (List.mem_cons_self ..)) htail (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

end UV.FermionWick
