import UV.JordanCauchyHomotopy
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Smooth homotopy invariance for actual complex contour integrals.
Holomorphy supplies the closed one-form condition; no Cauchy or residue
identity is part of the geometric homotopy data. -/

noncomputable section
open Set Filter Complex
open scoped Topology unitInterval

namespace UV

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]

/-- Complex holomorphy makes the actual contour one-form closed, so a
smooth homotopy through closed loops preserves its integral. -/
theorem parametrizedContourIntegral_holomorphic_homotopy
    {a b c d : ℂ} {γ₁ : Path a b} {γ₂ : Path c d} {U : Set ℂ} {f : ℂ → Z}
    (φ : (γ₁ : C(I, ℂ)).Homotopy γ₂)
    (hφU : ∀ s ∈ Ioo 0 1, ∀ t ∈ Ioo 0 1, φ (s, t) ∈ U)
    (hf : AnalyticOnNhd ℂ f (closure U))
    (hC2 : ContDiffOn ℝ 2
      (fun p : ℝ × ℝ => IccExtend zero_le_one (φ.extend p.1) p.2) (Icc 0 1))
    (hclosed : ∀ s : I, φ (s, 0) = φ (s, 1)) :
    parametrizedContourIntegral f γ₁ = parametrizedContourIntegral f γ₂ := by
  let e : Z →L[ℂ] ℂ →L[ℂ] Z := (ContinuousLinearMap.lsmul ℂ ℂ (E := Z)).flip
  let dω (z : ℂ) : ℂ →L[ℝ] ℂ →L[ℂ] Z :=
    (e.comp ((1 : ℂ →L[ℂ] ℂ).smulRight (deriv f z))).restrictScalars ℝ
  have hωe : contourOneForm f = fun z => e (f z) := rfl
  change curveIntegral (contourOneForm f) γ₁ = curveIntegral (contourOneForm f) γ₂
  apply jordan_curveIntegral_eq_of_closed_homotopy (dω := dω) φ hφU
  · intro z hz
    rw [hωe]
    exact ((e.hasFDerivAt.comp z
      (hf z (subset_closure hz)).differentiableAt.hasDerivAt.hasFDerivAt).restrictScalars ℝ).hasFDerivWithinAt
  · rw [hωe]
    exact e.continuous.comp_continuousOn hf.continuousOn
  · intro z _ u _ v _
    change v • (u • deriv f z) = u • (v • deriv f z)
    exact smul_comm v u _
  · exact hC2
  · exact hclosed

/-- A holomorphic function integrates to zero along an actual smooth
null-homotopic closed curve in its analytic domain. -/
theorem parametrizedContourIntegral_holomorphic_nullhomotopy
    {a b : ℂ} {γ : Path a a} {U : Set ℂ} {f : ℂ → Z}
    (φ : (γ : C(I, ℂ)).Homotopy (Path.refl b))
    (hφU : ∀ s ∈ Ioo 0 1, ∀ t ∈ Ioo 0 1, φ (s, t) ∈ U)
    (hf : AnalyticOnNhd ℂ f (closure U))
    (hC2 : ContDiffOn ℝ 2
      (fun p : ℝ × ℝ => IccExtend zero_le_one (φ.extend p.1) p.2) (Icc 0 1))
    (hclosed : ∀ s : I, φ (s, 0) = φ (s, 1)) :
    parametrizedContourIntegral f γ = 0 := by
  rw [parametrizedContourIntegral_holomorphic_homotopy φ hφU hf hC2 hclosed]
  exact curveIntegral_refl _ _

end UV
