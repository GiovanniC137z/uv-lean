import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Fermionic Wick expansion of a product of *vacuum-normal-ordered*
one-body currents in the particle/hole Fock representation. The Fock
space is the exterior algebra; its vacuum functional extracts degree
zero. A two-field vertex is kept intact until it meets another vertex. -/

noncomputable section

namespace UV.FermionWick

variable {M α : Type*} [AddCommGroup M] [Module ℂ M]

abbrev Fock (M : Type*) [AddCommGroup M] [Module ℂ M] := ExteriorAlgebra ℂ M

def vacuum : Fock M →ₐ[ℂ] ℂ := ExteriorAlgebra.lift ℂ ⟨0,by simp⟩

def annihilate (d : Module.Dual ℂ M) : Fock M →ₗ[ℂ] Fock M :=
  CliffordAlgebra.contractLeft (Q := 0) d

def field (v : M) (d : Module.Dual ℂ M) : Fock M →ₗ[ℂ] Fock M :=
  LinearMap.mulLeft ℂ (ExteriorAlgebra.ι ℂ v)+annihilate d

theorem annihilate_field (δ d : Module.Dual ℂ M) (v : M) (z : Fock M) :
    annihilate δ (field v d z) = δ v • z-field v d (annihilate δ z) := by
  change annihilate δ (ExteriorAlgebra.ι ℂ v*z+annihilate d z)=_
  rw [map_add]
  change CliffordAlgebra.contractLeft (Q:=0) δ (CliffordAlgebra.ι 0 v*z)+
    CliffordAlgebra.contractLeft (Q:=0) δ (CliffordAlgebra.contractLeft (Q:=0) d z)=_
  rw [CliffordAlgebra.contractLeft_ι_mul,CliffordAlgebra.contractLeft_comm]
  change _ = δ v • z-(ExteriorAlgebra.ι ℂ v*annihilate δ z+annihilate d (annihilate δ z))
  abel

theorem vacuum_field (v : M) (d : Module.Dual ℂ M) (z : Fock M) :
    vacuum (field v d z)=vacuum (annihilate d z) := by
  change vacuum (ExteriorAlgebra.ι ℂ v*z+annihilate d z)=_
  simp [vacuum]

inductive Block (α : Type*) where
  | one (x : α)
  | normal (x y : α)

def blockOp (v : α→M) (d : α→Module.Dual ℂ M) : Block α → Fock M →ₗ[ℂ] Fock M
  | .one x => field (v x) (d x)
  | .normal x y => (field (v x) (d x)).comp (field (v y) (d y)) - (d x (v y)) • LinearMap.id

def state (v : α→M) (d : α→Module.Dual ℂ M) : List (Block α) → Fock M
  | [] => 1
  | a::xs => blockOp v d a (state v d xs)

theorem annihilate_normal (δ : Module.Dual ℂ M) (v : α→M) (d : α→Module.Dual ℂ M)
    (x y : α) (z : Fock M) :
    annihilate δ (blockOp v d (.normal x y) z) =
    δ (v x) • (field (v y) (d y) z) - δ (v y) • (field (v x) (d x) z) +
      blockOp v d (.normal x y) (annihilate δ z) := by
  simp only [blockOp,LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.id_apply,
    map_sub,map_smul,annihilate_field]
  abel

structure Cut (α : Type*) where
  hit : α
  rest : List (Block α)
  sign : ℤ

def cuts : List (Block α) → List (Cut α)
  | [] => []
  | .one x::xs => ⟨x,xs,1⟩ :: (cuts xs).map (fun c => ⟨c.hit,.one x::c.rest,-c.sign⟩)
  | .normal x y::xs => ⟨x,.one y::xs,1⟩ :: ⟨y,.one x::xs,-1⟩ ::
      (cuts xs).map (fun c => ⟨c.hit,.normal x y::c.rest,c.sign⟩)

private theorem sum_linear {V W β : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (T : V →ₗ[ℂ] W) (xs : List β) (g : β → V) :
    T ((xs.map g).sum) = (xs.map (fun x => T (g x))).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

private theorem sum_neg {V β : Type*} [AddCommGroup V] (xs : List β) (g : β→V) :
    (xs.map (fun x => -(g x))).sum = -(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,add_comm]

theorem annihilate_word (δ : Module.Dual ℂ M) (v : α→M) (d : α→Module.Dual ℂ M) (xs : List (Block α)) :
    annihilate δ (state v d xs) =
      ((cuts xs).map (fun c => ((c.sign:ℂ)*δ (v c.hit)) • state v d c.rest)).sum := by
  induction xs with
  | nil => exact CliffordAlgebra.contractLeft_one (Q:=0) (d:=δ)
  | cons a xs ih =>
    cases a with
    | one x =>
      simp only [state,blockOp,annihilate_field,cuts,List.map_cons,List.sum_cons,List.map_map,Function.comp_def,
        Int.cast_one,one_mul,Int.cast_neg,neg_mul,neg_smul]
      rw [ih,sum_linear,sum_neg]
      simp only [map_smul,sub_eq_add_neg]
    | normal x y =>
      change annihilate δ (blockOp v d (.normal x y) (state v d xs))=_
      rw [annihilate_normal,ih,sum_linear]
      simp only [cuts,List.map_cons,List.sum_cons,List.map_map,Function.comp_def,Int.cast_one,one_mul,
        Int.cast_neg,neg_mul,neg_smul,state,blockOp,map_smul]
      abel

structure Edge (α : Type*) where
  first : α
  second : α
  sign : ℤ

def edgeWeight (c : α→α→ℂ) (e : Edge α) := (e.sign:ℂ)*c e.first e.second

def successors : List (Block α) → List (Edge α × List (Block α))
  | [] => []
  | .one x::xs => (cuts xs).map (fun c => (⟨x,c.hit,c.sign⟩,c.rest))
  | .normal x y::xs => (cuts xs).map (fun c => (⟨x,c.hit,-c.sign⟩,.one y::c.rest))

theorem vacuum_step (v : α→M) (d : α→Module.Dual ℂ M) (a : Block α) (xs : List (Block α)) :
    vacuum (state v d (a::xs)) = ((successors (a::xs)).map (fun p =>
      edgeWeight (fun i j => d i (v j)) p.1 * vacuum (state v d p.2))).sum := by
  cases a with
  | one x =>
    change vacuum (field (v x) (d x) (state v d xs))=_
    rw [vacuum_field,annihilate_word]
    rw [show vacuum ((List.map _ (cuts xs)).sum) = vacuum.toLinearMap ((List.map _ (cuts xs)).sum) from rfl,sum_linear]
    simp [successors,edgeWeight,List.map_map,Function.comp_def]
  | normal x y =>
    have h : vacuum (blockOp v d (.normal x y) (state v d xs)) =
        -vacuum (field (v y) (d y) (annihilate (d x) (state v d xs))) := by
      simp only [blockOp,LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.id_apply,
        map_sub,map_smul]
      rw [vacuum_field,annihilate_field,map_sub,map_smul]
      abel
    rw [state,h,annihilate_word,sum_linear]
    change -vacuum.toLinearMap _=_
    rw [sum_linear,←sum_neg]
    simp [successors,edgeWeight,state,blockOp,List.map_map,Function.comp_def]

def fields : Block α → List α
  | .one x => [x]
  | .normal x y => [x,y]

def slots (xs : List (Block α)) := xs.flatMap fields

theorem cut_slots_perm (xs : List (Block α)) (c : Cut α) (hc : c∈cuts xs) :
    (c.hit::slots c.rest).Perm (slots xs) := by
  induction xs generalizing c with
  | nil => simp [cuts] at hc
  | cons a xs ih =>
    cases a with
    | one x =>
      simp only [cuts,List.mem_cons,List.mem_map] at hc
      rcases hc with rfl|⟨c,hc,rfl⟩
      · rfl
      · change (c.hit::x::slots c.rest).Perm (x::slots xs)
        exact (List.Perm.swap ..).trans ((ih c hc).cons x)
    | normal x y =>
      simp only [cuts,List.mem_cons,List.mem_map] at hc
      rcases hc with rfl|rfl|⟨c,hc,rfl⟩
      · rfl
      · exact List.Perm.swap ..
      · change (c.hit::x::y::slots c.rest).Perm (x::y::slots xs)
        exact (List.Perm.swap ..).trans (((List.Perm.swap ..).cons x).trans ((ih c hc).cons y |>.cons x))

theorem successor_slots_perm (xs : List (Block α)) (p : Edge α × List (Block α))
    (hp : p∈successors xs) :
    (p.1.first::p.1.second::slots p.2).Perm (slots xs) := by
  cases xs with
  | nil => simp [successors] at hp
  | cons a xs =>
    cases a with
    | one x =>
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
      exact (cut_slots_perm xs c hc).cons x
    | normal x y =>
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
      exact ((List.Perm.swap ..).cons x).trans ((cut_slots_perm xs c hc).cons y |>.cons x)

def matchings : ℕ → List (Block α) → List (List (Edge α))
  | 0,xs => if xs.isEmpty then [[]] else []
  | _+1,[] => [[]]
  | n+1,a::xs => (successors (a::xs)).flatMap (fun p => (matchings n p.2).map (p.1::·))

def amplitude (c : α→α→ℂ) (edges : List (Edge α)) := (edges.map (edgeWeight c)).prod

private theorem sum_children {β : Type*} (ps : List (Edge α × β)) (L : β→List (List (Edge α))) (c : α→α→ℂ) :
    ((ps.flatMap (fun p => (L p.2).map (p.1::·))).map (amplitude c)).sum =
      (ps.map (fun p => edgeWeight c p.1*((L p.2).map (amplitude c)).sum)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,ih]
    congr 1
    simp only [List.map_map,Function.comp_def,amplitude,List.map_cons,List.prod_cons]
    induction L p.2 with
    | nil => simp
    | cons x xs ih => simp [ih,mul_add,amplitude]

theorem vacuum_wick (v : α→M) (d : α→Module.Dual ℂ M) (n : ℕ) (xs : List (Block α))
    (hn : (slots xs).length≤n) : vacuum (state v d xs) =
    ((matchings n xs).map (amplitude (fun i j => d i (v j)))).sum := by
  induction n generalizing xs with
  | zero =>
    cases xs with
    | nil => simp [state,matchings,amplitude]
    | cons a xs => cases a <;> simp [slots,fields] at hn
  | succ n ih =>
    cases xs with
    | nil => simp [state,matchings,amplitude]
    | cons a xs =>
      rw [vacuum_step,matchings,sum_children]
      congr 1
      apply List.map_congr_left
      intro p hp
      have h := (successor_slots_perm (a::xs) p hp).length_eq
      simp only [List.length_cons] at h
      rw [ih p.2 (by omega)]

def endpoints (es : List (Edge α)) := es.flatMap (fun e => [e.first,e.second])

theorem matching_uses_all (n : ℕ) (xs : List (Block α)) (es : List (Edge α)) (h : es∈matchings n xs) :
    (endpoints es).Perm (slots xs) := by
  induction n generalizing xs es with
  | zero =>
    cases xs <;> simp [matchings] at h
    subst es
    rfl
  | succ n ih =>
    cases xs with
    | nil =>
      simp [matchings] at h
      subst es
      rfl
    | cons a xs =>
      obtain ⟨p,hp,hh⟩ := List.mem_flatMap.mp h
      obtain ⟨tail,ht,rfl⟩ := List.mem_map.mp hh
      exact ((ih p.2 tail ht).cons p.1.second |>.cons p.1.first).trans (successor_slots_perm _ _ hp)

end UV.FermionWick
