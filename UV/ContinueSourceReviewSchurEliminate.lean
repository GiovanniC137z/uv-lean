import UV.ContinueSourceReviewSchurSplit
import UV.ContinueSourceReviewSchurResolvent

/-! Schur elimination of a self-adjoint boundary generator on its proper
domain, keeping the common nonreal frequency on the selected sector plane. -/

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace ComplexConjugate
namespace UV.SectorPlane

variable {S H : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem closing_unbounded_elimination [FiniteDimensional ℂ S] (K : H →ₗ.[ℂ] H)
    (J : S →ₗᵢ[ℂ] H) (U : ClosingUnboundedBlocks K J) (z : ℂ)
    (RK : ClosingUnboundedResolvent K z) (RB : ClosingUnboundedResolvent U.B z) :
    J.toContinuousLinearMap.adjoint.comp (RK.map.comp J.toContinuousLinearMap) =
      Ring.inverse (closingInverseSlot U.A U.T RB.map z) := by
  let F := J.toContinuousLinearMap
  let G := F.adjoint.comp (RK.map.comp F)
  let D := closingInverseSlot U.A U.T RB.map z
  have hF (v:S) : F.adjoint (F v)=v := by
    apply ext_inner_left ℂ
    intro x; rw [adjoint_inner_right]; exact J.inner_map_map x v
  have hdg : D*G=1 := by
    ext v
    let y : K.domain := ⟨RK.map (F v),RK.inDomain _⟩
    let x := F.adjoint (y:H)
    let w : U.B.domain := ⟨(y:H)-F x,U.complementDomain y⟩
    have hfull : z • (y:H)+K y=F v := RK.rightInverse _
    have hi := congrArg F.adjoint hfull
    rw [map_add,map_smul,hF] at hi
    have hlo : z • (w:H)+U.B w = - U.T x := by
      apply eq_neg_of_add_eq_zero_left
      have hr := U.boundaryEquation y
      change U.T x + U.B w = K y-F (F.adjoint (K y)) at hr
      calc _ = z • ((y:H)-F x)+(U.T x+U.B w) := by
             change (z • ((y:H)-F x)+U.B w)+U.T x=_
             abel
           _ = (z • (y:H) + K y) - F (z • x + F.adjoint (K y)) := by
             rw [hr,smul_sub,map_add,map_smul]
             abel
           _ = 0 := by rw [hfull,hi,sub_self]
    have hwo : (w:H) = -RB.map (U.T x) := by
      calc _ = RB.map (z • (w:H)+U.B w) := (RB.leftInverse w).symm
           _ = _ := by rw [hlo,map_neg]
    have he := U.slotEquation y
    change U.A x+U.T.adjoint (w:H)=F.adjoint (K y) at he
    rw [hwo,map_neg] at he
    change z • x + U.A x - U.T.adjoint (RB.map (U.T x))=v
    rw [←hi]
    change _=z • x + F.adjoint (K y)
    rw [←he]
    abel
  have he : D.toLinearMap*G.toLinearMap=1 := by
    ext x; exact DFunLike.congr_fun hdg x
  have hg : G*D=1 := by
    ext x; exact DFunLike.congr_fun (LinearMap.mul_eq_one_comm.mp he) x
  let u : (S →L[ℂ] S)ˣ := ⟨D,G,hdg,hg⟩
  exact (Ring.inverse_unit u).symm

/-- A finite-dimensional isometric column in the energy domain of any
self-adjoint, possibly unbounded dilation determines a single self-adjoint
boundary operator and its exact Schur formula for every nonreal z. -/
theorem closing_unbounded_dilation_schur [FiniteDimensional ℂ S] (K : H →ₗ.[ℂ] H)
    (hK : IsSelfAdjoint K) (J : S →ₗᵢ[ℂ] H) (hJ : ∀ v, J v∈K.domain) :
    ∃ (U : ClosingUnboundedBlocks K J), ∀ (z : ℂ) (hz : z.im ≠ 0),
      J.toContinuousLinearMap.adjoint.comp ((closingNonrealResolvent K hK z hz).map.comp J.toContinuousLinearMap) =
      Ring.inverse (closingInverseSlot U.A U.T (closingNonrealResolvent U.B U.boundarySelfAdjoint z hz).map z) :=
  ⟨closingUnboundedBlocks K hK J hJ,fun z hz =>
    closing_unbounded_elimination K J _ z (closingNonrealResolvent K hK z hz) (closingNonrealResolvent _ _ z hz)⟩

end UV.SectorPlane
