import UV.ContinueClosingPositiveDilation
import UV.UnboundedSourceResolvent

/-! Unbounded self-adjoint charged dilations with finite-dimensional
domain slots. Splitting off a bounded self-adjoint block preserves the
operator domain, including its equality with the adjoint domain. -/

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace ComplexConjugate
namespace UV.SectorPlane

variable {S H : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def closingBoundedPerturb (K : H →ₗ.[ℂ] H) (C : H →L[ℂ] H) : H →ₗ.[ℂ] H :=
  ⟨K.domain,K.toFun+C.toLinearMap.comp K.domain.subtype⟩

theorem closing_symmetric_of_selfAdjoint (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) :
    K.IsFormalAdjoint K := by
  have h := LinearPMap.adjoint_isFormalAdjoint (T:=K) hK.dense_domain
  simpa only [LinearPMap.isSelfAdjoint_def.mp hK] using h

/-- Bounded self-adjoint perturbation changes neither the original
operator domain nor the domain equality with the actual Hilbert adjoint. -/
theorem closing_selfAdjoint_bounded_perturb (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K)
    (C : H →L[ℂ] H) (hC : IsSelfAdjoint C) : IsSelfAdjoint (closingBoundedPerturb K C) := by
  let D := closingBoundedPerturb K C
  have hsym := closing_symmetric_of_selfAdjoint K hK
  have hc (x y : H) : ⟪C x,y⟫_ℂ=⟪x,C y⟫_ℂ := by
    rw [←adjoint_inner_right, show C.adjoint=C from hC.star_eq]
  have hd : Dense (D.domain : Set H) := hK.dense_domain
  have hs : D.IsFormalAdjoint D := by
    intro x y
    change ⟪K x+C x,(y:H)⟫_ℂ=⟪(x:H),K y+C y⟫_ℂ
    rw [inner_add_left,inner_add_right,hsym x y,hc]
  have hle : D ≤ D.adjoint := hs.le_adjoint hd
  have hp (y) (hy : y ∈ D.adjoint.domain) : y ∈ K.domain := by
    rw [←LinearPMap.isSelfAdjoint_def.mp hK]
    apply LinearPMap.mem_adjoint_domain_of_exists
    refine ⟨D.adjoint ⟨y,hy⟩-C y,?_⟩
    intro x
    have h := LinearPMap.adjoint_isFormalAdjoint (T:=D) hd ⟨y,hy⟩ x
    change ⟪D.adjoint ⟨y,hy⟩,(x:H)⟫_ℂ = ⟪y,K x+C x⟫_ℂ at h
    rw [inner_sub_left,h,inner_add_right,hc,add_sub_cancel_right]
  have hrev : D.adjoint ≤ D := by
    refine ⟨hp,?_⟩
    intro x y h
    exact (hle.2 h.symm).symm
  exact LinearPMap.isSelfAdjoint_def.mpr (le_antisymm hrev hle)

/-- Finite-dimensional slots in the actual domain give a bounded KJ,
although K itself has no boundedness assumption. -/
def closingUnboundedColumn [FiniteDimensional ℂ S] (K : H →ₗ.[ℂ] H) (J : S →ₗᵢ[ℂ] H)
    (hJ : ∀ v, J v ∈ K.domain) : S →L[ℂ] H :=
  LinearMap.toContinuousLinearMap (K.toFun.comp (J.toLinearMap.codRestrict K.domain hJ))

theorem closing_unbounded_column_form [FiniteDimensional ℂ S] (K : H →ₗ.[ℂ] H)
    (hK : IsSelfAdjoint K) (J : S →ₗᵢ[ℂ] H) (hJ : ∀ v, J v ∈ K.domain) (y : K.domain) :
    (closingUnboundedColumn K J hJ).adjoint (y:H) = J.toContinuousLinearMap.adjoint (K y) := by
  apply ext_inner_left ℂ
  intro v
  rw [adjoint_inner_right,adjoint_inner_right]
  exact closing_symmetric_of_selfAdjoint K hK ⟨J v,hJ v⟩ y

end UV.SectorPlane
