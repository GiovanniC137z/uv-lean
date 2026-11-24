import UV.HeatFourier
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.LinearAlgebra.Finsupp.Defs

/-! The trace of a finitely supported word current is the identity
coefficient in the left regular group algebra. The physical Fourier
phases are kept in the amplitudes until the paired trace. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace UV.SewnWordTrace

def positiveWord {α : Type*} (w : List α) : FreeGroup α :=
  FreeGroup.mk (w.map fun a => (a,true))

theorem positiveWord_toWord {α : Type*} [DecidableEq α] (w : List α) :
    (positiveWord w).toWord = w.map (fun a => (a,true)) := by
  unfold positiveWord
  rw [FreeGroup.toWord_mk]
  apply FreeGroup.IsReduced.reduce_eq
  rw [FreeGroup.IsReduced,List.isChain_map]
  induction w using List.twoStepInduction <;> simp_all

theorem positiveWord_injective {α : Type*} : Function.Injective (positiveWord : List α → FreeGroup α) := by
  classical
  intro x y h
  have he := congrArg FreeGroup.toWord h
  simp only [positiveWord_toWord] at he
  simpa only [List.map_map,show Prod.fst ∘ (fun a : α => (a,true)) = id from rfl,List.map_id]
    using congrArg (List.map Prod.fst) he

theorem positiveWord_ne_identity {α : Type*} {w : List α} (h : w ≠ []) : positiveWord w ≠ 1 := by
  intro hw
  apply h
  exact positiveWord_injective (show positiveWord w = positiveWord [] from hw)

theorem positiveWord_mul {α : Type*} (x y : List α) :
    positiveWord (x ++ y) = positiveWord x * positiveWord y := by
  rw [positiveWord,positiveWord,positiveWord,List.map_append,FreeGroup.mul_mk]

def wordAdjoint {G : Type*} [Group G] : MonoidAlgebra ℂ G →+ MonoidAlgebra ℂ G :=
  (Finsupp.mapRange.addMonoidHom (starRingEnd ℂ).toAddMonoidHom).comp
    (Finsupp.domCongr (Equiv.inv G)).toAddMonoidHom

theorem wordAdjoint_apply {G : Type*} [Group G] (A : MonoidAlgebra ℂ G) (g : G) :
    wordAdjoint A g = conj (A g⁻¹) := by
  change (Finsupp.mapRange (starRingEnd ℂ) (map_zero _) (Finsupp.equivMapDomain (Equiv.inv G) A)) g = _
  rw [Finsupp.mapRange_apply,Finsupp.equivMapDomain_apply]
  rfl

@[simp] theorem wordAdjoint_single {G : Type*} [Group G] (g : G) (z : ℂ) :
    wordAdjoint (MonoidAlgebra.single g z) = MonoidAlgebra.single g⁻¹ (conj z) := by
  classical
  ext h
  rw [wordAdjoint_apply]
  by_cases he : g⁻¹ = h
  · subst h
    simp
  · have hn : g ≠ h⁻¹ := fun h' => he (inv_eq_iff_eq_inv.mpr h')
    simp [he,hn]

def wordTrace {G : Type*} [Group G] : MonoidAlgebra ℂ G →ₗ[ℂ] ℂ := Finsupp.lapply 1

theorem wordTrace_apply {G : Type*} [Group G] (A : MonoidAlgebra ℂ G) : wordTrace A = A 1 := rfl

theorem wordTrace_cyclic {G : Type*} [Group G] (A B : MonoidAlgebra ℂ G) :
    wordTrace (A*B) = wordTrace (B*A) := by
  classical
  rw [wordTrace_apply,wordTrace_apply,MonoidAlgebra.mul_apply_left,MonoidAlgebra.mul_apply_right]
  simp only [mul_one,one_mul,mul_comm]

/-- The identity coefficient is the scalar product of the two
prepared finitely supported vectors in the left regular representation. -/
theorem wordTrace_pairing {G : Type*} [Group G] (A B : MonoidAlgebra ℂ G) :
    wordTrace (wordAdjoint A * B) = ∑ g ∈ B.support, conj (A g)*B g := by
  classical
  rw [wordTrace_apply,MonoidAlgebra.mul_apply_right]
  simp [wordAdjoint_apply,Finsupp.sum]

theorem wordTrace_positive {G : Type*} [Group G] (A : MonoidAlgebra ℂ G) :
    0 ≤ (wordTrace (wordAdjoint A * A)).re := by
  rw [wordTrace_pairing]
  simp only [← Complex.normSq_eq_conj_mul_self,Complex.re_sum,Complex.ofReal_re]
  exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

theorem wordTrace_nonempty {α : Type*} {w : List α} (hw : w ≠ []) :
    wordTrace (MonoidAlgebra.single (positiveWord w) 1) = 0 := by
  classical
  simp [wordTrace_apply,positiveWord_ne_identity hw]

theorem wordTrace_generator_pairing {G : Type*} [Group G] (g h : G) [DecidableEq G] :
    wordTrace (wordAdjoint (MonoidAlgebra.single g 1) * MonoidAlgebra.single h 1) =
      if g = h then 1 else 0 := by
  rw [wordAdjoint_single,MonoidAlgebra.single_mul_single]
  simp only [wordTrace_apply, map_one, mul_one, MonoidAlgebra.single_apply, inv_mul_eq_one]

def wordCurrent {α : Type*} (S : Finset (List α)) (a : List α → ℂ)
    (d : List α → ScalarMomentum) (k : ScalarMomentum) : MonoidAlgebra ℂ (FreeGroup α) :=
  ∑ w ∈ S, MonoidAlgebra.single (positiveWord w) (a w * stableFourierPhase (d w) k)

/-- In the inclusive trace every distinct recorded positive word
contributes its exact squared amplitude at every physical momentum. -/
theorem word_trace_inclusive {α : Type*} (S : Finset (List α)) (a : List α → ℂ)
    (d : List α → ScalarMomentum) (k : ScalarMomentum) :
    wordTrace (wordAdjoint (wordCurrent S a d k) * wordCurrent S a d k) =
      ∑ w ∈ S, (Complex.normSq (a w) : ℂ) := by
  classical
  let c := fun w => a w * stableFourierPhase (d w) k
  change wordTrace (wordAdjoint (∑ w ∈ S, MonoidAlgebra.single (positiveWord w) (c w)) *
    (∑ w ∈ S, MonoidAlgebra.single (positiveWord w) (c w))) = _
  simp_rw [map_sum,wordAdjoint_single,Finset.sum_mul,Finset.mul_sum,map_sum,MonoidAlgebra.single_mul_single]
  apply Finset.sum_congr rfl
  intro w hw
  simp only [wordTrace_apply,MonoidAlgebra.single_apply,inv_mul_eq_one,
    positiveWord_injective.eq_iff]
  rw [Finset.sum_eq_single_of_mem w hw (fun v _ hv => if_neg (Ne.symm hv)),if_pos rfl]
  have hPhase : Complex.normSq (stableFourierPhase (d w) k) = 1 := by
    rw [Complex.normSq_eq_norm_sq,stableFourierPhase_norm,one_pow]
  rw [← Complex.normSq_eq_conj_mul_self]
  unfold c
  rw [Complex.normSq_mul,hPhase,mul_one]

end UV.SewnWordTrace
