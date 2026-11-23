import UV.ContinueSourceReviewSchur

/-! Exact operator blocks of a self-adjoint dilation with a finite family
of domain vectors. The boundary operator is extended by zero on the slot
range, which decouples orthogonally from the physical boundary space. -/

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace
namespace UV.SectorPlane

variable {S H : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure ClosingUnboundedBlocks (K : H →ₗ.[ℂ] H) (J : S →ₗᵢ[ℂ] H) where
  A : S →L[ℂ] S
  T : S →L[ℂ] H
  B : H →ₗ.[ℂ] H
  slotSelfAdjoint : IsSelfAdjoint A
  boundarySelfAdjoint : IsSelfAdjoint B
  domain_eq : B.domain=K.domain
  orthogonalColumn : ∀ v, J.toContinuousLinearMap.adjoint (T v)=0
  killsSlots : ∀ (v:S), ∃ hv : J v ∈ B.domain, B ⟨J v,hv⟩=0
  complementDomain : ∀ y : K.domain, (y:H)-J (J.toContinuousLinearMap.adjoint y)∈B.domain
  boundaryEquation : ∀ y : K.domain,
    let x := J.toContinuousLinearMap.adjoint (y:H)
    T x + B ⟨(y:H)-J x,complementDomain y⟩ =
       K y - J (J.toContinuousLinearMap.adjoint (K y))
  slotEquation : ∀ y : K.domain,
    let x := J.toContinuousLinearMap.adjoint (y:H)
    A x + T.adjoint ((y:H)-J x) = J.toContinuousLinearMap.adjoint (K y)

set_option maxHeartbeats 650000 in
def closingUnboundedBlocks [FiniteDimensional ℂ S] (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K)
    (J : S →ₗᵢ[ℂ] H) (hJ : ∀ v, J v ∈ K.domain) : ClosingUnboundedBlocks K J := by
  let F := J.toContinuousLinearMap
  let L := closingUnboundedColumn K J hJ
  let A := F.adjoint.comp L
  let T := L - F.comp A
  let C := - (F.comp L.adjoint + L.comp F.adjoint) + F.comp (A.comp F.adjoint)
  let B := closingBoundedPerturb K C
  have hF (v : S) : F.adjoint (F v)=v := by
    apply ext_inner_left ℂ
    intro x
    rw [adjoint_inner_right]
    exact J.inner_map_map x v
  have hs (y : K.domain) : L.adjoint (y:H)=F.adjoint (K y) :=
    closing_unbounded_column_form K hK J hJ y
  have hA : A.adjoint=A := by
    ext v
    change (F.adjoint.comp L).adjoint v=_
    rw [adjoint_comp,adjoint_adjoint]
    exact hs ⟨J v,hJ v⟩
  have hT : T.adjoint=L.adjoint-A.comp F.adjoint := by simp [T,hA]
  have hC : C.adjoint=C := by
    dsimp only [C]
    rw [map_add,map_neg,map_add,adjoint_comp,adjoint_comp,adjoint_comp,adjoint_comp,
      adjoint_adjoint,adjoint_adjoint,hA,comp_assoc,add_comm (L.comp F.adjoint)]
  have hb : IsSelfAdjoint B := closing_selfAdjoint_bounded_perturb K hK C (ContinuousLinearMap.isSelfAdjoint_iff'.mpr hC)
  have horth (v:S) : F.adjoint (T v)=0 := by
    change F.adjoint (L v-F (A v))=0
    rw [map_sub,hF]; exact sub_self _
  have hB (y : K.domain) : B y = (K y-F (F.adjoint (K y)))-T (F.adjoint (y:H)) := by
    change K y+(-(F (L.adjoint (y:H))+L (F.adjoint (y:H)))+F (A (F.adjoint (y:H))))=_
    rw [hs]
    change _= _-(L (F.adjoint (y:H))-F (A (F.adjoint (y:H))))
    abel
  have hkill (v:S) : B ⟨J v,hJ v⟩=0 := by
    rw [hB]
    change (L v-F (A v))-T (F.adjoint (F v))=0
    rw [hF]; exact sub_self _
  have hd (y : K.domain) : (y:H)-J (F.adjoint y)∈K.domain := K.domain.sub_mem y.property (hJ _)
  refine ⟨A,T,B,ContinuousLinearMap.isSelfAdjoint_iff'.mpr hA,hb,rfl,horth,fun v => ⟨hJ v,hkill v⟩,hd,?_,?_⟩
  · intro y
    let v := F.adjoint (y:H)
    have hv := hkill v
    have hQ : B ⟨(y:H)-J v,hd y⟩ = B y-B ⟨J v,hJ v⟩ := by
      exact B.toFun.map_sub y ⟨J v,hJ v⟩
    dsimp only
    rw [hQ,hv,sub_zero,hB]
    abel
  · intro y
    let v := F.adjoint (y:H)
    have hLF : L.adjoint (F v)=A v := hs ⟨J v,hJ v⟩
    have hQ : F.adjoint ((y:H)-F v)=0 := by rw [map_sub,hF]; exact sub_self _
    change A v+T.adjoint ((y:H)-F v)=F.adjoint (K y)
    rw [hT,sub_apply]
    change A v + (L.adjoint ((y:H)-F v)-A (F.adjoint ((y:H)-F v))) = F.adjoint (K y)
    rw [hQ,map_zero,sub_zero,map_sub,hLF,hs]
    abel

end UV.SectorPlane
