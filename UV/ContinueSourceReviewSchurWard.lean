import UV.ContinueSourceReviewSchurComplement

/-! First and second compressed energy moments and the two-frequency
temporal Ward identity for the same unbounded charged boundary. -/

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace ComplexConjugate
namespace UV.SectorPlane

variable {S H : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem unbounded_resolvent_difference {B : H →ₗ.[ℂ] H} (z z' : ℂ)
    (R : ClosingUnboundedResolvent B z) (R' : ClosingUnboundedResolvent B z') :
    R'.map-R.map= -(z'-z) • (R'.map*R.map) := by
  ext v
  let x : B.domain := ⟨R.map v,R.inDomain v⟩
  have hp := R'.leftInverse x
  have hx := R.rightInverse v
  have h : z' • (x:H)+B x = v+(z'-z) • (x:H) := by
    rw [←hx]
    change z' • (x:H)+B x=z • (x:H)+B x+(z'-z) • (x:H)
    module
  rw [h,map_add,map_smul] at hp
  change R'.map v-(x:H) = -(z'-z) • R'.map (x:H)
  rw [neg_smul]
  calc _ = R'.map v-(R'.map v+(z'-z) • R'.map (x:H)) := congrArg (fun t : H => R'.map v-t) hp.symm
       _ = _ := by abel

theorem ClosingUnboundedBlocks.physical_temporal_ward {K : H →ₗ.[ℂ] H} {J : S →ₗᵢ[ℂ] H}
    (U : ClosingUnboundedBlocks K J) (q : ℝ) (z z' : ℂ) (hz : z.im ≠ 0) (hz' : z'.im ≠ 0) :
    let R := (closingNonrealResolvent U.boundaryRestriction U.restriction_selfAdjoint z hz).map
    let R' := (closingNonrealResolvent U.boundaryRestriction U.restriction_selfAdjoint z' hz').map
    (z'-z) • closingTemporalMark U.physicalColumn q R' R =
      (q : ℂ) • (closingInverseSlot U.A U.physicalColumn R' z'-closingInverseSlot U.A U.physicalColumn R z) :=
  closing_temporal_ward_of_diff _ _ _ _ _ _ _ (unbounded_resolvent_difference z z' _ _)

theorem ClosingUnboundedBlocks.energy_moments [FiniteDimensional ℂ S] {K : H →ₗ.[ℂ] H}
    {J : S →ₗᵢ[ℂ] H} (U : ClosingUnboundedBlocks K J) (hJ : ∀ v, J v ∈ K.domain) :
    let L := closingUnboundedColumn K J hJ
    U.A=J.toContinuousLinearMap.adjoint.comp L ∧
      L.adjoint.comp L=U.A*U.A+U.physicalColumn.adjoint.comp U.physicalColumn := by
  let F := J.toContinuousLinearMap
  let L := closingUnboundedColumn K J hJ
  have hF (v:S) : F.adjoint (F v)=v := by
    apply ext_inner_left ℂ
    intro u; rw [adjoint_inner_right]; exact J.inner_map_map u v
  have ha (v:S) : U.A v=F.adjoint (L v) := by
    have h := U.slotEquation ⟨J v,hJ v⟩
    change U.A (F.adjoint (F v))+U.T.adjoint (F v-F (F.adjoint (F v)))=F.adjoint (L v) at h
    simpa only [hF,sub_self,map_zero,add_zero] using h
  have hL (v:S) : F (U.A v)+U.T v=L v := by
    have h := U.boundaryEquation ⟨J v,hJ v⟩
    let w : U.B.domain := ⟨J v-J (F.adjoint (F v)),U.complementDomain ⟨J v,hJ v⟩⟩
    have heq : w=0 := by
      apply Subtype.ext
      change F v - F (F.adjoint (F v))=0
      rw [hF,sub_self]
    change U.T (F.adjoint (F v))+U.B w=L v-F (F.adjoint (L v)) at h
    rw [heq,LinearPMap.map_zero,add_zero,hF,←ha] at h
    rw [h]; abel
  refine ⟨ContinuousLinearMap.ext ha,?_⟩
  ext v
  apply ext_inner_left ℂ
  intro u
  change ⟪u,L.adjoint (L v)⟫_ℂ=⟪u,U.A (U.A v)+U.physicalColumn.adjoint (U.physicalColumn v)⟫_ℂ
  rw [adjoint_inner_right,inner_add_right,adjoint_inner_right]
  have hA : U.A.adjoint=U.A := U.slotSelfAdjoint.star_eq
  rw [←hA,adjoint_inner_right,hA]
  change ⟪L u,L v⟫_ℂ=⟪U.A u,U.A v⟫_ℂ+⟪U.T u,U.T v⟫_ℂ
  rw [←hL u,←hL v,inner_add_left,inner_add_right,inner_add_right]
  have horth (u v : S) : ⟪F u,U.T v⟫_ℂ=0 := by rw [←adjoint_inner_right,U.orthogonalColumn,inner_zero_right]
  have hr : ⟪U.T u,F (U.A v)⟫_ℂ=0 := by rw [←inner_conj_symm,horth,map_zero]
  rw [horth,hr,zero_add,add_zero]
  exact congrArg (fun t : ℂ => t+⟪U.T u,U.T v⟫_ℂ) (J.inner_map_map (U.A u) (U.A v))

end UV.SectorPlane
