import UV.ContinueSourceReviewSchurWard
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary

/-! The true unitary Cayley transform of the charged generator and its
two graph identities, using the nonreal resolvent on the actual domain. -/

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace ComplexConjugate
namespace UV.SectorPlane

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def closingCayley (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) : H →L[ℂ] H :=
  1-(2*Complex.I) • (closingNonrealResolvent K hK Complex.I (by simp)).map

theorem closing_cayley_on_graph (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (x : K.domain) :
    closingCayley K hK (Complex.I • (x:H)+K x) = -Complex.I • (x:H)+K x := by
  change (Complex.I • (x:H)+K x)-(2*Complex.I) •
      (closingNonrealResolvent K hK Complex.I _).map (Complex.I • (x:H)+K x)=_
  rw [(closingNonrealResolvent K hK Complex.I _).leftInverse x]
  module

theorem closing_cayley_graph_pair (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (x : K.domain) :
    let u := K x + Complex.I • (x:H)
    (1-closingCayley K hK) u = (2*Complex.I) • (x:H) ∧
      (1+closingCayley K hK) u = (2:ℂ) • K x := by
  simp only [sub_apply,add_apply,one_apply]
  rw [add_comm (K x),closing_cayley_on_graph]
  constructor <;> module

theorem closing_cayley_one_sub_injective (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) :
    Function.Injective (1-closingCayley K hK : H →L[ℂ] H) := by
  let R := closingNonrealResolvent K hK Complex.I (by simp)
  have he : 1-closingCayley K hK=(2*Complex.I) • R.map := by unfold closingCayley; abel
  intro u v h
  rw [he] at h
  change (2*Complex.I) • R.map u=(2*Complex.I) • R.map v at h
  have hh : R.map u=R.map v := smul_right_injective _ (by norm_num : (2:ℂ)*Complex.I≠0) h
  let x : K.domain := ⟨R.map u,R.inDomain _⟩
  let y : K.domain := ⟨R.map v,R.inDomain _⟩
  have he' : x=y := Subtype.ext hh
  calc u = Complex.I • (x:H)+K x := (R.rightInverse u).symm
       _ = Complex.I • (y:H)+K y := by rw [he']
       _ = v := R.rightInverse v

theorem closing_cayley_unitary (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) :
    closingCayley K hK ∈ unitary (H →L[ℂ] H) := by
  let U := closingCayley K hK
  let R := closingNonrealResolvent K hK Complex.I (by simp)
  let R' := closingNonrealResolvent K hK (-Complex.I) (by simp)
  let V : H →L[ℂ] H := 1+(2*Complex.I) • R'.map
  have hV (x : K.domain) : V (-Complex.I • (x:H)+K x)=Complex.I • (x:H)+K x := by
    change (-Complex.I • (x:H)+K x)+(2*Complex.I) • R'.map (-Complex.I • (x:H)+K x)=_
    rw [R'.leftInverse]; module
  have hadj : U.adjoint=V := by
    apply ext
    intro v
    apply ext_inner_left ℂ
    intro u
    rw [adjoint_inner_right]
    let a : K.domain := ⟨R.map u,R.inDomain _⟩
    let b : K.domain := ⟨R'.map v,R'.inDomain _⟩
    have hua : u=Complex.I • (a:H)+K a := (R.rightInverse u).symm
    have hvb : v=-Complex.I • (b:H)+K b := (R'.rightInverse v).symm
    rw [hua,hvb,hV]
    change ⟪closingCayley K hK (Complex.I • (a:H)+K a),_⟫_ℂ=_
    rw [closing_cayley_on_graph]
    simp only [inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,map_neg,Complex.conj_I,
      neg_neg,closing_symmetric_of_selfAdjoint K hK a b]
    ring
  rw [unitary.mem_iff]
  change U.adjoint*U=1 ∧ U*U.adjoint=1
  rw [hadj]
  constructor
  · ext u
    let a : K.domain := ⟨R.map u,R.inDomain _⟩
    calc V (U u)=V (U (Complex.I • (a:H)+K a)) := congrArg (fun t => V (U t)) (R.rightInverse u).symm
         _ = _ := by rw [show U (Complex.I • (a:H)+K a)=_ from closing_cayley_on_graph K hK a,
                            hV,R.rightInverse,one_apply]
  · ext v
    let b : K.domain := ⟨R'.map v,R'.inDomain _⟩
    calc U (V v)=U (V (-Complex.I • (b:H)+K b)) := congrArg (fun t => U (V t)) (R'.rightInverse v).symm
         _ = _ := by rw [hV,show U (Complex.I • (b:H)+K b)=_ from closing_cayley_on_graph K hK b,
                          R'.rightInverse,one_apply]

theorem closing_cayley_normal (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) :
    IsStarNormal (closingCayley K hK) :=
  (unitary_iff_isStarNormal_and_spectrum_subset_unitary.mp (closing_cayley_unitary K hK)).1

end UV.SectorPlane
