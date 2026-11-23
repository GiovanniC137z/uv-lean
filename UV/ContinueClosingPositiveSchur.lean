import UV.ContinueClosingPositiveVertex
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! The block Hamiltonian, its exact bounded Schur inverse, and the
first and second compressed moment forms. -/

noncomputable section

open ContinuousLinearMap
open scoped InnerProductSpace

namespace UV.SectorPlane

variable {S H : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev ClosingSlots (S H : Type*) := WithLp 2 (S × H)

omit [CompleteSpace S] [CompleteSpace H] in
def closingSlotInclusion : S →L[ℂ] ClosingSlots S H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ S H).symm.toContinuousLinearMap.comp
    (inl ℂ S H)

omit [CompleteSpace S] [CompleteSpace H] in
@[simp] theorem closing_slot_inclusion_apply (v : S) :
    closingSlotInclusion (H := H) v = WithLp.toLp 2 (v, (0 : H)) := rfl

theorem closing_slot_inclusion_adjoint (w : ClosingSlots S H) :
    (closingSlotInclusion (S := S) (H := H)).adjoint w = (WithLp.ofLp w).1 := by
  apply ext_inner_left ℂ
  intro v
  simp [adjoint_inner_right]

def closingBlock (A : S →L[ℂ] S) (T : S →L[ℂ] H) (B : H →L[ℂ] H) :
    ClosingSlots S H →L[ℂ] ClosingSlots S H :=
  let E := WithLp.prodContinuousLinearEquiv 2 ℂ S H
  let pS := (fst ℂ S H).comp E.toContinuousLinearMap
  let pH := (snd ℂ S H).comp E.toContinuousLinearMap
  E.symm.toContinuousLinearMap.comp
    ((A.comp pS + T.adjoint.comp pH).prod (T.comp pS + B.comp pH))

@[simp] theorem closing_block_apply (A : S →L[ℂ] S) (T : S →L[ℂ] H)
    (B : H →L[ℂ] H) (v : S) (w : H) :
    closingBlock A T B (WithLp.toLp 2 (v, w)) =
      WithLp.toLp 2 (A v + T.adjoint w, T v + B w) := rfl

theorem closing_block_selfAdjoint (A : S →L[ℂ] S) (T : S →L[ℂ] H)
    (B : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (closingBlock A T B) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  symm
  apply (eq_adjoint_iff _ _).mpr
  intro x y
  obtain ⟨⟨xS, xH⟩, rfl⟩ := (WithLp.toLp_surjective (V := S × H) 2) x
  obtain ⟨⟨yS, yH⟩, rfl⟩ := (WithLp.toLp_surjective (V := S × H) 2) y
  simp only [closing_block_apply, WithLp.prod_inner_apply, WithLp.ofLp_toLp, inner_add_left, inner_add_right]
  have hA' : A.adjoint = A := hA.star_eq
  have hB' : B.adjoint = B := hB.star_eq
  rw [adjoint_inner_left T, ← adjoint_inner_right T, ← adjoint_inner_right A, hA',
    ← adjoint_inner_right B, hB']
  abel

@[simp] theorem closing_shift_block_apply (A : S →L[ℂ] S) (T : S →L[ℂ] H)
    (B : H →L[ℂ] H) (z : ℂ) (v : S) (w : H) :
    closingShift (closingBlock A T B) z (WithLp.toLp 2 (v, w)) =
      WithLp.toLp 2 ((closingShift A z) v + T.adjoint w, T v + (closingShift B z) w) := by
  apply WithLp.ofLp_injective 2
  simp [closingShift, add_assoc, add_left_comm]

/-- Gaussian elimination of the actual boundary block at a point of
the boundary resolvent set. -/
theorem closing_block_eliminate (A : S →L[ℂ] S) (T : S →L[ℂ] H)
    {B : H →L[ℂ] H} {z : ℂ} (hB : IsUnit (closingShift B z)) (v : S) :
    closingShift (closingBlock A T B) z
        (WithLp.toLp 2 (v, -closingResolvent B z (T v))) =
      closingSlotInclusion (H := H) (closingInverseSlot A T (closingResolvent B z) z v) := by
  have hR : closingShift B z (closingResolvent B z (T v)) = T v := by
    have h := Ring.mul_inverse_cancel (closingShift B z) hB
    exact congrArg (fun L : H →L[ℂ] H => L (T v)) h
  rw [closing_shift_block_apply, map_neg (closingShift B z), hR, add_neg_cancel,
    closing_slot_inclusion_apply]
  simp [closingInverseSlot, closingShift, sub_eq_add_neg]

/-- The finite-slot inverse is the actual compression of the inverse
of the full bounded self-adjoint block. -/
theorem closing_block_compressed_inverse (A : S →L[ℂ] S) (T : S →L[ℂ] H)
    (B : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {z : ℂ} (hz : z.im ≠ 0) :
    let D := closingInverseSlot A T (closingResolvent B z) z
    let J := closingSlotInclusion (S := S) (H := H)
    let G := J.adjoint.comp ((closingResolvent (closingBlock A T B) z).comp J)
    D * G = 1 ∧ G * D = 1 := by
  dsimp only
  let J := closingSlotInclusion (S := S) (H := H)
  let D := closingInverseSlot A T (closingResolvent B z) z
  let A₁ := closingShift (closingBlock A T B) z
  let R₁ := closingResolvent (closingBlock A T B) z
  have hu₁ : IsUnit A₁ := closing_shift_isUnit_of_nonreal _
    (closing_block_selfAdjoint A T B hA hB) hz
  have huB := closing_shift_isUnit_of_nonreal B hB hz
  have hleft (x : ClosingSlots S H) : A₁ (R₁ x) = x :=
    congrArg (fun L : ClosingSlots S H →L[ℂ] ClosingSlots S H => L x) (Ring.mul_inverse_cancel A₁ hu₁)
  have hright (x : ClosingSlots S H) : R₁ (A₁ x) = x :=
    congrArg (fun L : ClosingSlots S H →L[ℂ] ClosingSlots S H => L x) (Ring.inverse_mul_cancel A₁ hu₁)
  have hBleft (x : H) : closingResolvent B z (closingShift B z x) = x :=
    congrArg (fun L : H →L[ℂ] H => L x) (Ring.inverse_mul_cancel (closingShift B z) huB)
  change D * (J.adjoint.comp (R₁.comp J)) = 1 ∧ (J.adjoint.comp (R₁.comp J)) * D = 1
  constructor
  · apply ContinuousLinearMap.ext
    intro v
    let w := R₁ (J v)
    have he := hleft (J v)
    change A₁ w = J v at he
    have hw : w = WithLp.toLp 2 ((WithLp.ofLp w).1, (WithLp.ofLp w).2) := (WithLp.toLp_ofLp 2 w).symm
    rw [hw] at he
    change closingShift (closingBlock A T B) z
      (WithLp.toLp 2 ((WithLp.ofLp w).1, (WithLp.ofLp w).2)) = J v at he
    rw [closing_shift_block_apply] at he
    have h₁ := congrArg (fun u : ClosingSlots S H => (WithLp.ofLp u).1) he
    have h₂ := congrArg (fun u : ClosingSlots S H => (WithLp.ofLp u).2) he
    change closingShift A z (WithLp.ofLp w).1 + T.adjoint (WithLp.ofLp w).2 = v at h₁
    change T (WithLp.ofLp w).1 + closingShift B z (WithLp.ofLp w).2 = 0 at h₂
    have h₃ := congrArg (closingResolvent B z) (eq_neg_of_add_eq_zero_right h₂)
    rw [hBleft, map_neg] at h₃
    change D (J.adjoint w) = v
    rw [show J.adjoint w = _ from closing_slot_inclusion_adjoint w]
    rw [h₃] at h₁
    simpa [D, closingInverseSlot, closingShift, sub_eq_add_neg] using h₁
  · apply ContinuousLinearMap.ext
    intro v
    have he := closing_block_eliminate A T huB v
    have he' := congrArg R₁ he
    change R₁ (A₁ (WithLp.toLp 2 (v, -closingResolvent B z (T v)))) = R₁ (J (D v)) at he'
    rw [hright] at he'
    change J.adjoint (R₁ (J (D v))) = v
    rw [← he', show J.adjoint (WithLp.toLp 2 (v, -closingResolvent B z (T v))) = v from
      closing_slot_inclusion_adjoint _]

theorem closing_block_compressed_inverse_eq (A : S →L[ℂ] S) (T : S →L[ℂ] H)
    (B : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {z : ℂ} (hz : z.im ≠ 0) :
    let D := closingInverseSlot A T (closingResolvent B z) z
    let J := closingSlotInclusion (S := S) (H := H)
    J.adjoint.comp ((closingResolvent (closingBlock A T B) z).comp J) = Ring.inverse D := by
  dsimp only
  let D := closingInverseSlot A T (closingResolvent B z) z
  let J := closingSlotInclusion (S := S) (H := H)
  let G := J.adjoint.comp ((closingResolvent (closingBlock A T B) z).comp J)
  obtain ⟨h₁, h₂⟩ := closing_block_compressed_inverse A T B hA hB hz
  let u : (S →L[ℂ] S)ˣ := ⟨D, G, h₁, h₂⟩
  exact (Ring.inverse_unit u).symm

theorem closing_block_pole_state (A : S →L[ℂ] S) (T : S →L[ℂ] H)
    (B : H →L[ℂ] H) (E : ℝ)
    (hB : IsUnit (closingShift B (-(E : ℂ)))) (v : S) (hv : ‖v‖ = 1)
    (hD : closingInverseSlot A T (closingResolvent B (-(E : ℂ))) (-(E : ℂ)) v = 0) :
    let R := closingResolvent B (-(E : ℂ))
    let ψ := WithLp.toLp 2 (v, -R (T v))
    closingBlock A T B ψ = (E : ℂ) • ψ ∧
      (‖ψ‖ ^ 2)⁻¹ = closingSlotResidue T R v := by
  dsimp only
  constructor
  · have h := closing_block_eliminate A T hB v
    rw [hD, map_zero] at h
    simp only [closingShift, add_apply, neg_smul] at h
    exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg, add_comm] using h)
  · rw [WithLp.prod_norm_sq_eq_of_L2]
    simp [hv, closingSlotResidue]

theorem closing_block_first_moment (A : S →L[ℂ] S) (T : S →L[ℂ] H) (B : H →L[ℂ] H) :
    let J := closingSlotInclusion (S := S) (H := H)
    J.adjoint.comp ((closingBlock A T B).comp J) = A := by
  dsimp only
  apply ContinuousLinearMap.ext
  intro v
  simp [closing_slot_inclusion_adjoint]

theorem closing_block_second_moment (A : S →L[ℂ] S) (T : S →L[ℂ] H) (B : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) :
    let HJ := (closingBlock A T B).comp (closingSlotInclusion (S := S) (H := H))
    HJ.adjoint.comp HJ = A * A + T.adjoint.comp T := by
  dsimp only
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro u
  simp only [coe_comp', Function.comp_apply, adjoint_inner_right, closing_slot_inclusion_apply,
    closing_block_apply, map_zero, add_zero, WithLp.prod_inner_apply, WithLp.ofLp_toLp,
    add_apply, mul_apply, inner_add_right]
  have hA' : A.adjoint = A := hA.star_eq
  rw [← adjoint_inner_right A, hA']

omit [CompleteSpace S] [CompleteSpace H] in
theorem closing_block_second_moment_excess (T : S →L[ℂ] H) (hT : T ≠ 0) :
    ∃ v : S, 0 < ‖T v‖ ^ 2 := by
  by_contra! h
  apply hT
  apply ContinuousLinearMap.ext
  intro v
  exact norm_eq_zero.mp (by nlinarith [h v, norm_nonneg (T v)])

end UV.SectorPlane
