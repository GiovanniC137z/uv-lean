import UV.ContinueSourceReviewSchurEliminate

/-! Restriction of the constructed self-adjoint generator to the actual
orthogonal complement of the finite slot range. Its nonreal inverse is
the restriction of the decoupled ambient inverse. -/

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace ComplexConjugate
namespace UV.SectorPlane

variable {S H : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev ClosingBoundaryFiber (J : S →ₗᵢ[ℂ] H) := LinearMap.ker J.toContinuousLinearMap.adjoint

theorem closing_boundary_orthogonal (J : S →ₗᵢ[ℂ] H) :
    ClosingBoundaryFiber J = (LinearMap.range J.toContinuousLinearMap)ᗮ := J.toContinuousLinearMap.orthogonal_range.symm

variable {K : H →ₗ.[ℂ] H} {J : S →ₗᵢ[ℂ] H}

theorem ClosingUnboundedBlocks.range_in_fiber (U : ClosingUnboundedBlocks K J) (y : U.B.domain) :
    U.B y ∈ ClosingBoundaryFiber J := by
  change J.toContinuousLinearMap.adjoint (U.B y)=0
  apply ext_inner_left ℂ
  intro v
  obtain ⟨hv,hv₀⟩ := U.killsSlots v
  rw [adjoint_inner_right,inner_zero_right]
  have h := closing_symmetric_of_selfAdjoint U.B U.boundarySelfAdjoint ⟨J v,hv⟩ y
  rw [hv₀,inner_zero_left] at h
  exact h.symm

def ClosingUnboundedBlocks.boundaryRestriction (U : ClosingUnboundedBlocks K J) :
    ClosingBoundaryFiber J →ₗ.[ℂ] ClosingBoundaryFiber J :=
  let P := U.B.domain.comap (ClosingBoundaryFiber J).subtype
  let F : P →ₗ[ℂ] U.B.domain :=
    ((ClosingBoundaryFiber J).subtype.comp P.subtype).codRestrict U.B.domain (fun x => x.property)
  ⟨P,(U.B.toFun.comp F).codRestrict (ClosingBoundaryFiber J) (fun x => U.range_in_fiber (F x))⟩

theorem ClosingUnboundedBlocks.inverse_in_fiber (U : ClosingUnboundedBlocks K J)
    (z : ℂ) (hz : z ≠ 0) (R : ClosingUnboundedResolvent U.B z) (y : ClosingBoundaryFiber J) :
    R.map y ∈ ClosingBoundaryFiber J := by
  let w : U.B.domain := ⟨R.map y,R.inDomain _⟩
  have h := congrArg J.toContinuousLinearMap.adjoint (R.rightInverse y)
  have hb : J.toContinuousLinearMap.adjoint (U.B w)=0 := U.range_in_fiber w
  have hy : J.toContinuousLinearMap.adjoint (y:H)=0 := y.property
  change J.toContinuousLinearMap.adjoint (z • (w:H)+U.B w)=_ at h
  rw [map_add,map_smul,hb,add_zero,hy] at h
  exact (smul_eq_zero.mp h).resolve_left hz

def ClosingUnboundedBlocks.restrictedResolvent (U : ClosingUnboundedBlocks K J) (z : ℂ)
    (hz : z ≠ 0) (R : ClosingUnboundedResolvent U.B z) :
    ClosingUnboundedResolvent U.boundaryRestriction z := by
  let F := (R.map.comp (ClosingBoundaryFiber J).subtypeL).codRestrict (ClosingBoundaryFiber J)
    (fun y => U.inverse_in_fiber z hz R y)
  have hf (y) : F y ∈ U.boundaryRestriction.domain := R.inDomain _
  refine ⟨F,hf,?_,?_⟩
  · intro y; apply Subtype.ext; exact R.rightInverse (y:H)
  · intro x; apply Subtype.ext; exact R.leftInverse ⟨((x:ClosingBoundaryFiber J):H),x.property⟩

/-- Self-adjointness holds on the physical boundary Hilbert space,
after discarding the finite-dimensional zero summand. -/
theorem ClosingUnboundedBlocks.restriction_selfAdjoint (U : ClosingUnboundedBlocks K J) :
    IsSelfAdjoint U.boundaryRestriction := by
  let D := U.boundaryRestriction
  have hs : D.IsFormalAdjoint D := by
    intro x y
    exact closing_symmetric_of_selfAdjoint U.B U.boundarySelfAdjoint ⟨((x:ClosingBoundaryFiber J):H),x.property⟩
      ⟨((y:ClosingBoundaryFiber J):H),y.property⟩
  let Rplus := U.restrictedResolvent Complex.I Complex.I_ne_zero
    (closingNonrealResolvent U.B U.boundarySelfAdjoint Complex.I (by simp))
  let Rminus := U.restrictedResolvent (-Complex.I) (neg_ne_zero.mpr Complex.I_ne_zero)
    (closingNonrealResolvent U.B U.boundarySelfAdjoint (-Complex.I) (by simp))
  apply UV.unbounded_selfAdjoint_of_imaginary_resolvents' D hs
  · intro y
    exact ⟨⟨Rplus.map y,Rplus.inDomain y⟩,(add_comm _ _).trans (Rplus.rightInverse y)⟩
  · intro y
    refine ⟨⟨Rminus.map y,Rminus.inDomain y⟩,?_⟩
    change U.boundaryRestriction ⟨Rminus.map y,Rminus.inDomain y⟩ - Complex.I • Rminus.map y=y
    rw [sub_eq_neg_add,←neg_smul]
    exact Rminus.rightInverse y

def ClosingUnboundedBlocks.physicalColumn (U : ClosingUnboundedBlocks K J) :
    S →L[ℂ] ClosingBoundaryFiber J := U.T.codRestrict _ U.orthogonalColumn

omit [CompleteSpace H] in
theorem unbounded_resolvent_unique {V : H →ₗ.[ℂ] H} {z : ℂ}
    (G R : ClosingUnboundedResolvent V z) : G.map=R.map := by
  ext x
  have h := R.leftInverse ⟨G.map x,G.inDomain x⟩
  rw [G.rightInverse x] at h
  exact h.symm

/-- The inverse boundary term is calculated entirely on the physical
orthogonal complement. No auxiliary uncoupled slot appears. -/
theorem closing_orthogonal_boundary_schur [FiniteDimensional ℂ S] (U : ClosingUnboundedBlocks K J)
    (z : ℂ) (hz : z.im ≠ 0) (RK : ClosingUnboundedResolvent K z) :
    J.toContinuousLinearMap.adjoint.comp (RK.map.comp J.toContinuousLinearMap) =
      Ring.inverse (closingInverseSlot U.A U.physicalColumn
        (closingNonrealResolvent U.boundaryRestriction U.restriction_selfAdjoint z hz).map z) := by
  let R := closingNonrealResolvent U.B U.boundarySelfAdjoint z hz
  have hz₀ : z ≠ 0 := by rintro rfl; simp at hz
  let R' := U.restrictedResolvent z hz₀ R
  rw [unbounded_resolvent_unique (closingNonrealResolvent U.boundaryRestriction U.restriction_selfAdjoint z hz) R']
  have h : closingSandwich U.physicalColumn R'.map = closingSandwich U.T R.map := by
    ext v
    apply ext_inner_left ℂ
    intro a
    rw [closing_sandwich_apply,closing_sandwich_apply,adjoint_inner_right,adjoint_inner_right]
    rfl
  rw [closingInverseSlot,h]
  exact closing_unbounded_elimination K J U z RK R

end UV.SectorPlane
