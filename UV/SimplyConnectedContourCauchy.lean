import UV.SimplyConnectedContourFilling
import UV.RectifiableCauchyHomotopy

/-! Actual Cauchy theorem in a specified simply-connected analytic domain.
The standard topological predicate constructs the filling internally; the
user does not supply a null-homotopy, primitive or contour integral identity.
The independent Jordan-to-simply-connected-domain theorem remains separate. -/

noncomputable section
open Set
open scoped unitInterval NNReal

namespace UV

/-- A holomorphic finite-dimensional readout has zero actual integral along
every Lipschitz closed curve in a specified simply-connected open domain. -/
theorem simplyConnectedContour_cauchy
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]
    [FiniteDimensional ℂ Z]
    {a : ℂ} {γ : Path a a} {K : ℝ≥0} {U : Set ℂ} [SimplyConnectedSpace U]
    {f : ℂ → Z} (hLip : LipschitzWith K γ.extend) (hU : IsOpen U)
    (hγ : ∀ t : I, γ t ∈ U) (hf : AnalyticOnNhd ℂ f U) :
    parametrizedContourIntegral f γ = 0 := by
  obtain ⟨φ,hφ,hclosed⟩ := simplyConnected_path_nullhomotopy U γ hγ
  exact lipschitzContour_holomorphic_nullhomotopy hLip hU φ hφ hclosed hf

end UV
