import UV.ContinuePinnedNormalNetwork
import Mathlib.Logic.Equiv.Fin.Basic

/-! Every square grounded incidence minor has coefficient zero or one
after squaring, including matrices with parallel edges or self-loops. -/

noncomputable section
open Matrix
open scoped BigOperators Matrix
namespace UV

private def pinVertex {n : ℕ} (i : Fin (n+1)) : Option (Fin (n+1)) → Option (Fin n)
  | none => none
  | some j => if h : j = i then none else some ((finSuccAboveEquiv i).symm ⟨j,h⟩)

private theorem pinVertex_eq_some {n : ℕ} (i : Fin (n+1)) (u : Option (Fin (n+1))) (j : Fin n) :
    pinVertex i u = some j ↔ u = some (i.succAbove j) := by
  cases u with
  | none => simp [pinVertex]
  | some k =>
    by_cases hk : k = i
    · simp [pinVertex,hk,Fin.ne_succAbove]
    · simp only [pinVertex,dif_neg hk,Option.some.injEq,Equiv.symm_apply_eq,
        finSuccAboveEquiv_apply,Subtype.mk.injEq]

private theorem grounded_minor_pin_vertex {n : ℕ} (src dst : Fin (n+1) → Option (Fin (n+1)))
    (i e : Fin (n+1)) :
    (groundedNetworkIncidence src dst)ᵀ.submatrix i.succAbove e.succAbove =
      (groundedNetworkIncidence (pinVertex i ∘ src ∘ e.succAbove)
        (pinVertex i ∘ dst ∘ e.succAbove))ᵀ := by
  ext j k
  simp only [Matrix.submatrix_apply,transpose_apply,groundedNetworkIncidence,Function.comp_apply,pinVertex_eq_some]

private theorem det_sq_expand_at_single_column {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (i e : Fin (n+1)) (honly : ∀ j, j ≠ i → A j e = 0) (hs : (A i e)^2 = 1) :
    A.det^2 = (A.submatrix i.succAbove e.succAbove).det^2 := by
  have he : A.det = (-1:ℝ)^((i:ℕ)+(e:ℕ)) * A i e * (A.submatrix i.succAbove e.succAbove).det := by
    rw [Matrix.det_succ_column A e,Finset.sum_eq_single i]
    · intro j _ hj
      rw [honly j hj,mul_zero,zero_mul]
    · simp
  have hSign : ((-1:ℝ)^((i:ℕ)+(e:ℕ)))^2 = 1 := by
    rw [← pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  rw [he,mul_pow,mul_pow,hSign,hs,one_mul,one_mul]

/-- The actual grounded oriented incidence determinant has squared
value zero or one, at every finite square selection. -/
theorem grounded_incidence_det_sq {n : ℕ} (src dst : Fin n → Option (Fin n)) :
    let A := (groundedNetworkIncidence src dst)ᵀ
    A.det^2 = 0 ∨ A.det^2 = 1 := by
  induction n with
  | zero => exact Or.inr (by simp)
  | succ n ih =>
    let A := (groundedNetworkIncidence src dst)ᵀ
    change A.det^2 = 0 ∨ A.det^2 = 1
    by_cases hz : ∃ e, src e = dst e
    · obtain ⟨e,he⟩ := hz
      have h0 : A.det = 0 := Matrix.det_eq_zero_of_column_eq_zero e (fun i => by
        simp only [A,transpose_apply,groundedNetworkIncidence,he,sub_self])
      exact Or.inl (by simp [h0])
    by_cases hb : ∃ e i, (src e = none ∧ dst e = some i) ∨ (src e = some i ∧ dst e = none)
    · obtain ⟨e,i,hi⟩ := hb
      have hOnly (j : Fin (n+1)) (hj : j ≠ i) : A j e = 0 := by
        rcases hi with ⟨hs,hd⟩|⟨hs,hd⟩ <;> simp [A,groundedNetworkIncidence,hs,hd,Ne.symm hj]
      have hOne : (A i e)^2 = 1 := by
        have hn : (none : Option (Fin (n+1))) ≠ some i := Option.noConfusion
        rcases hi with ⟨hs,hd⟩|⟨hs,hd⟩ <;> norm_num [A,groundedNetworkIncidence,hs,hd,hn]
      rw [det_sq_expand_at_single_column A i e hOnly hOne]
      unfold A
      rw [grounded_minor_pin_vertex]
      exact ih _ _
    · have hEnds (e : Fin (n+1)) : ∃ i j, src e = some i ∧ dst e = some j := by
        cases hs : src e <;> cases hd : dst e
        · exact (hz ⟨e,hs.trans hd.symm⟩).elim
        · exact (hb ⟨e,_,Or.inl ⟨hs,hd⟩⟩).elim
        · exact (hb ⟨e,_,Or.inr ⟨hs,hd⟩⟩).elim
        · exact ⟨_,_,rfl,rfl⟩
      have hKer : Aᵀ *ᵥ (fun _ => (1:ℝ)) = 0 := by
        funext e
        obtain ⟨i,j,hs,hd⟩ := hEnds e
        unfold A
        rw [transpose_transpose,groundedNetworkIncidence_mulVec,hs,hd]
        simp [networkRootLift]
      have h0 : A.det = 0 := by
        by_contra hne
        have hU : IsUnit Aᵀ := (Matrix.isUnit_iff_isUnit_det _).mpr
          (isUnit_iff_ne_zero.mpr (by simpa only [Matrix.det_transpose] using hne))
        have hInj := Matrix.mulVec_injective_iff_isUnit.mpr hU
        have hOne : (fun _ => (1:ℝ)) = (0 : Fin (n+1) → ℝ) :=
          hInj (hKer.trans (Matrix.mulVec_zero _).symm)
        have h := congrFun hOne 0
        norm_num at h
      exact Or.inl (by simp [h0])

theorem pinnedHeldMinorCoefficient_zero_or_one {L N : ℕ} {B : Type*}
    (src dst : Fin N → Fin L ⊕ B) (S : Finset (Fin N)) :
    retainedMinorCoefficient (pinnedHeldIncidence src dst) S = 0 ∨
      retainedMinorCoefficient (pinnedHeldIncidence src dst) S = 1 := by
  classical
  unfold retainedMinorCoefficient
  split
  · rename_i hS
    let e : Fin L ≃ S := Fintype.equivOfCardEq (by simp [hS])
    change let A := (pinnedHeldIncidence src dst).submatrix id (Subtype.val ∘ e)
      A.det^2 = 0 ∨ A.det^2 = 1
    have he : (pinnedHeldIncidence src dst).submatrix id (Subtype.val ∘ e) =
        (groundedNetworkIncidence (pinnedHeldEndpoint ∘ src ∘ Subtype.val ∘ e)
          (pinnedHeldEndpoint ∘ dst ∘ Subtype.val ∘ e))ᵀ := by
      ext i j
      rfl
    dsimp only
    rw [he]
    exact grounded_incidence_det_sq _ _
  · exact Or.inl rfl

end UV
