import UV.ContinueCompressedModesFockOrder
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Pi

/-! An occupied negative orbital is a hole. The two maps below therefore
exchange exterior creation and annihilation exactly on the filled band.
Interaction-picture propagation is attached before the contractions. -/

noncomputable section
namespace UV.FermionWick

variable {ν ι : Type*} [DecidableEq ι]

structure Slot (ν ι : Type*) where
  vertex : ν
  create : Bool
  orbital : ι

def interactionPhase (band : ι→Bool) (E : ι→ℝ) (t : ν→ℝ) (x : Slot ν ι) : ℝ :=
  Real.exp ((if x.create=band x.orbital then 1 else -1)*E x.orbital*t x.vertex)

def excitation (band : ι→Bool) (E : ι→ℝ) (t : ν→ℝ) (x : Slot ν ι) : ι→ℂ :=
  fun i => if x.create=band x.orbital ∧ i=x.orbital then (interactionPhase band E t x:ℂ) else 0

def removal (band : ι→Bool) (E : ι→ℝ) (t : ν→ℝ) (x : Slot ν ι) : Module.Dual ℂ (ι→ℂ) :=
  if x.create=band x.orbital then 0 else (interactionPhase band E t x:ℂ) • LinearMap.proj x.orbital

def seaCovariance (band : ι→Bool) (E : ι→ℝ) (t : ν→ℝ) (x y : Slot ν ι) : ℂ :=
  if x.orbital=y.orbital ∧ x.create≠band x.orbital ∧ y.create=band x.orbital then
    Real.exp (-E x.orbital*(t x.vertex-t y.vertex)) else 0

theorem elementary_contraction (band : ι→Bool) (E : ι→ℝ) (t : ν→ℝ) (x y : Slot ν ι) :
    removal band E t x (excitation band E t y)=seaCovariance band E t x y := by
  classical
  by_cases hxy : x.orbital=y.orbital
  · by_cases hx : x.create=band x.orbital
    · simp [removal,seaCovariance,hx]
    · by_cases hy : y.create=band x.orbital
      · rw [seaCovariance,if_pos ⟨hxy,hx,hy⟩]
        simp [removal,excitation,interactionPhase,hx,hxy.symm,hy]
        rw [←Complex.exp_add]
        congr 1
        ring
      · simp [removal,excitation,seaCovariance,hxy.symm,hx,hy]
  · by_cases hx : x.create=band x.orbital <;> simp [removal,excitation,seaCovariance,hxy,hx]

def vertex (i : ν) (a b : ι) : Block (Slot ν ι) :=
  .normal ⟨i,true,a⟩ ⟨i,false,b⟩

theorem sea_normal_order (band : ι→Bool) (E : ι→ℝ) (t : ν→ℝ) (i : ν) (a b : ι) :
    removal band E t (Slot.mk i true a) (excitation band E t (Slot.mk i false b)) =
      if a=b ∧ band a=false then 1 else 0 := by
  rw [elementary_contraction,seaCovariance]
  cases band a <;> simp

theorem current_wick (band : ι→Bool) (E : ι→ℝ) (t : ν→ℝ) (xs : List (Block (Slot ν ι))) :
    vacuum (state (excitation band E t) (removal band E t) xs) =
      ((matchings (slots xs).length xs).map (amplitude (seaCovariance band E t))).sum := by
  have h := vacuum_wick (excitation band E t) (removal band E t) (slots xs).length xs (le_refl _)
  simpa only [elementary_contraction] using h

theorem contraction_nonzero_iff (band : ι→Bool) (E : ι→ℝ) (t : ν→ℝ) (x y : Slot ν ι) :
    seaCovariance band E t x y ≠ 0 ↔
      x.orbital=y.orbital ∧ x.create≠band x.orbital ∧ y.create=band x.orbital := by
  unfold seaCovariance
  split_ifs with h
  · exact iff_of_true (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) h
  · exact iff_of_false (not_not_intro rfl) h

theorem nonzero_edge (band : ι→Bool) (E : ι→ℝ) (t : ν→ℝ) (es : List (Edge (Slot ν ι)))
    (hne : amplitude (seaCovariance band E t) es≠0) (e : Edge (Slot ν ι)) (he : e∈es) :
    e.first.orbital=e.second.orbital ∧ e.first.create≠band e.first.orbital ∧ e.second.create=band e.first.orbital := by
  apply (contraction_nonzero_iff band E t e.first e.second).mp
  intro h
  apply hne
  apply List.prod_eq_zero
  exact List.mem_map.mpr ⟨e,he,by simp [edgeWeight,h]⟩

/-- Arbitrary finite one-body source matrices, expanded in their elementary
orbital entries. The normal-ordering subtraction is orbital diagonal. -/
def energyCurrent {ι : Type*} [Fintype ι] [DecidableEq ι] (band : ι→Bool) (E : ι→ℝ) (t : ν→ℝ)
    (Q : ν→ι→ι→ℂ) (i : ν) : Fock (ι→ℂ) →ₗ[ℂ] Fock (ι→ℂ) :=
  ∑ a : ι, ∑ b : ι, Q i a b • blockOp (excitation band E t) (removal band E t) (vertex i a b)

def transfer {ι : Type*} [Fintype ι] [DecidableEq ι] (band : ι→Bool) (E : ι→ℝ) (t : ν→ℝ)
    (Q : ν→ι→ι→ℂ) : List ν → Fock (ι→ℂ)
  | [] => 1
  | i::xs => energyCurrent band E t Q i (transfer band E t Q xs)

def resolvedSum {ι : Type*} [Fintype ι] (Q : ν→ι→ι→ℂ) {V : Type*} [AddCommGroup V] [Module ℂ V] :
    List ν → (List (Block (Slot ν ι))→V) → V
  | [],f => f []
  | i::xs,f => ∑ a : ι, ∑ b : ι, Q i a b • resolvedSum Q xs (fun l => f (vertex i a b::l))

private theorem resolved_map {ι : Type*} [Fintype ι] {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (Q : ν→ι→ι→ℂ) (xs : List ν) (f : List (Block (Slot ν ι))→V)
    (A : V→ₗ[ℂ]W) : A (resolvedSum Q xs f) = resolvedSum Q xs (fun l => A (f l)) := by
  induction xs generalizing f with
  | nil => rfl
  | cons i xs ih => simp [resolvedSum,map_sum,map_smul,ih]

private theorem transfer_resolved {ι : Type*} [Fintype ι] [DecidableEq ι] (band : ι→Bool) (E : ι→ℝ)
    (t : ν→ℝ) (Q : ν→ι→ι→ℂ) (xs : List ν) : transfer band E t Q xs =
      resolvedSum Q xs (state (excitation band E t) (removal band E t)) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp [transfer,energyCurrent,LinearMap.sum_apply,LinearMap.smul_apply,ih,resolvedSum,resolved_map,state]

/-- Vacuum of the complete product of the matrix currents is a finite sum
of the signed, time-propagated Wick matchings of all orbital placements. -/
theorem transfer_wick {ι : Type*} [Fintype ι] [DecidableEq ι] (band : ι→Bool) (E : ι→ℝ)
    (t : ν→ℝ) (Q : ν→ι→ι→ℂ) (xs : List ν) :
    vacuum (transfer band E t Q xs) = resolvedSum Q xs (fun l =>
      ((matchings (slots l).length l).map (amplitude (seaCovariance band E t))).sum) := by
  rw [transfer_resolved]
  change vacuum.toLinearMap _=_
  rw [resolved_map]
  congr 1
  funext l
  exact current_wick band E t l

end UV.FermionWick
