import UV.ContinueCayleyOperator
import UV.ContinueCayleyRealLaw
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-! The Cauchy symbol of the true Cayley unitary is continuous on its
whole compact spectrum and represents the actual nonreal resolvent. -/

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace ComplexConjugate
namespace UV.SectorPlane

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem closing_cayley_spectral_norm (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K)
    (u : spectrum ℂ (closingCayley K hK)) : ‖(u:ℂ)‖ = 1 :=
  mem_sphere_zero_iff_norm.mp (spectrum.subset_circle_of_unitary (closing_cayley_unitary K hK) u.property)

def closingCayleySpectralCauchy (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (z : ℂ) (hz : z.im ≠ 0) :
    C(spectrum ℂ (closingCayley K hK),ℂ) :=
  ⟨fun u => closingCayleyCauchySymbol z u,by
    unfold closingCayleyCauchySymbol
    fun_prop (disch := exact fun x => closing_cayley_denominator_ne hz (closing_cayley_spectral_norm K hK x))⟩

def closingCayleyDenominator (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (z : ℂ) : H →L[ℂ] H :=
  Complex.I • (1+closingCayley K hK)+z • (1-closingCayley K hK)

theorem closing_cayley_denominator_graph (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (z : ℂ) (x : K.domain) :
    closingCayleyDenominator K hK z (K x+Complex.I • (x:H)) =
      (2*Complex.I) • (z • (x:H)+K x) := by
  have h := closing_cayley_graph_pair K hK x
  simp only [closingCayleyDenominator,add_apply,smul_apply,one_apply]
  rw [show K x + Complex.I • (x:H)+closingCayley K hK (K x+Complex.I • (x:H)) = (2:ℂ) • K x from h.2,h.1]
  module

theorem closing_cayley_cfc_resolvent (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (z : ℂ) (hz : z.im ≠ 0) :
    cfcHom (closing_cayley_normal K hK) (closingCayleySpectralCauchy K hK z hz) =
      (closingNonrealResolvent K hK z hz).map := by
  let U := closingCayley K hK
  let P := cfcHom (R:=ℂ) (closing_cayley_normal K hK)
  let idS : C(spectrum ℂ U,ℂ) := (ContinuousMap.id ℂ).restrict _
  let N : C(spectrum ℂ U,ℂ) := 1-idS
  let D : C(spectrum ℂ U,ℂ) := Complex.I • (1+idS)+z • (1-idS)
  let g := closingCayleySpectralCauchy K hK z hz
  have hprod : g*D=N := by
    ext u
    change closingCayleyCauchySymbol z u * (Complex.I*(1+(u:ℂ))+z*(1-(u:ℂ)))=1-(u:ℂ)
    exact div_mul_cancel₀ _ (closing_cayley_denominator_ne hz (closing_cayley_spectral_norm K hK u))
  have hID : P idS=U := cfcHom_id (closing_cayley_normal K hK)
  have hD : P D=closingCayleyDenominator K hK z := by simp [D,map_smul,hID,U,closingCayleyDenominator]
  have hN : P N=1-U := by simp [N,hID]
  have h := congrArg P hprod
  change P (g*D)=P N at h
  rw [map_mul,hD,hN] at h
  let R := closingNonrealResolvent K hK z hz
  change P g=R.map
  ext y
  let x : K.domain := ⟨R.map y,R.inDomain _⟩
  have hEval := DFunLike.congr_fun h (K x+Complex.I • (x:H))
  change P g (closingCayleyDenominator K hK z (K x+Complex.I • (x:H)))=(1-closingCayley K hK) (K x+Complex.I • (x:H)) at hEval
  rw [closing_cayley_denominator_graph, (closing_cayley_graph_pair K hK x).1,R.rightInverse,map_smul] at hEval
  exact smul_right_injective _ (by norm_num : (2:ℂ)*Complex.I ≠ 0) hEval

end UV.SectorPlane
