import UV.ContinueCayleyCauchy
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-! Compact scalar spectral measures for the vector states of a unital
star representation. Specialization to the continuous functional calculus
of a normal operator needs no spectral resolution as an input. -/

noncomputable section
open MeasureTheory Set ContinuousLinearMap
open scoped CompactlySupported InnerProductSpace ComplexConjugate
namespace UV.SectorPlane

variable {X H : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def closingRealTest (f : C(X,ℝ)) : C(X,ℂ) :=
  ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

private def closingRealState (π : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    C_c(X,ℝ) →ₚ[ℝ] ℝ := by
  let L : C_c(X,ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => (⟪v, π (closingRealTest f.toContinuousMap) v⟫_ℂ).re
      map_add' := fun f g => by
        have h : closingRealTest (f+g).toContinuousMap =
            closingRealTest f.toContinuousMap + closingRealTest g.toContinuousMap := by
          ext x
          exact Complex.ofReal_add ..
        rw [h,map_add,add_apply,inner_add_right,Complex.add_re]
      map_smul' := fun a f => by
        have h : closingRealTest (a • f).toContinuousMap = (a : ℂ) • closingRealTest f.toContinuousMap := by
          ext x
          exact Complex.ofReal_mul ..
        rw [h,map_smul,smul_apply,inner_smul_right,Complex.re_ofReal_mul]
        rfl }
  apply PositiveLinearMap.mk₀ L
  intro f hf
  let g : C(X,ℂ) := closingRealTest ⟨fun x => Real.sqrt (f x), Real.continuous_sqrt.comp f.continuous⟩
  have hg : closingRealTest f.toContinuousMap = star g * g := by
    ext x
    change (f x : ℂ) = star (↑(Real.sqrt (f x)) : ℂ) * ↑(Real.sqrt (f x))
    rw [Complex.star_def,Complex.conj_ofReal,←Complex.ofReal_mul,Real.mul_self_sqrt (hf x)]
  change 0 ≤ (⟪v, π (closingRealTest f.toContinuousMap) v⟫_ℂ).re
  rw [hg,map_mul,map_star]
  change 0 ≤ (⟪v, (π g).adjoint ((π g) v)⟫_ℂ).re
  rw [adjoint_inner_right]
  exact inner_self_nonneg (𝕜 := ℂ) (x := π g v)

variable [MeasurableSpace X] [BorelSpace X]

def closingCompactState (π : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) : Measure X :=
  RealRMK.rieszMeasure (closingRealState π v)

instance (π : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) : IsFiniteMeasure (closingCompactState π v) := by
  let one := CompactlySupportedContinuousMap.ContinuousMap.liftCompactlySupported (1 : C(X,ℝ))
  have h := RealRMK.rieszMeasure_le_of_eq_one (closingRealState π v) (f := one)
    (fun _ => zero_le_one) isCompact_univ (fun _ _ => rfl)
  exact ⟨lt_of_le_of_lt h ENNReal.ofReal_lt_top⟩

private theorem closing_state_real (π : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) (f : C(X,ℝ)) :
    ∫ x, f x ∂closingCompactState π v = (⟪v, π (closingRealTest f) v⟫_ℂ).re :=
  RealRMK.integral_rieszMeasure (closingRealState π v) (CompactlySupportedContinuousMap.ContinuousMap.liftCompactlySupported f)

private theorem closing_state_real_complex (π : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) (f : C(X,ℝ)) :
    ((∫ x, f x ∂closingCompactState π v : ℝ) : ℂ) = ⟪v, π (closingRealTest f) v⟫_ℂ := by
  have hf : star (closingRealTest f) = closingRealTest f := by
    ext x
    exact Complex.conj_ofReal _
  have hA : IsSelfAdjoint (π (closingRealTest f)) := by rw [IsSelfAdjoint,←map_star,hf]
  have hs := hA.isSymmetric v v
  have hr : conj ⟪v, π (closingRealTest f) v⟫_ℂ = ⟪v, π (closingRealTest f) v⟫_ℂ :=
    (inner_conj_symm _ _).trans hs
  rw [closing_state_real]
  exact Complex.conj_eq_iff_re.mp hr

theorem closing_compact_state_integral (π : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) (f : C(X,ℂ)) :
    (∫ x, f x ∂closingCompactState π v) = ⟪v, π f v⟫_ℂ := by
  let a : C(X,ℝ) := ⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩
  let b : C(X,ℝ) := ⟨fun x => (f x).im, Complex.continuous_im.comp f.continuous⟩
  have h : f = closingRealTest a + Complex.I • closingRealTest b := by
    ext x
    simpa [closingRealTest,a,b,mul_comm] using (Complex.re_add_im (f x)).symm
  have ha := closing_state_real_complex π v a
  have hb := closing_state_real_complex π v b
  have hi : Integrable (fun x => f x) (closingCompactState π v) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ = ((∫ x, a x ∂closingCompactState π v : ℝ) : ℂ) + Complex.I * (∫ x, b x ∂closingCompactState π v : ℝ) := by
      rw [show (∫ x, a x ∂closingCompactState π v) = (∫ x, f x ∂closingCompactState π v).re from integral_re hi,
        show (∫ x, b x ∂closingCompactState π v) = (∫ x, f x ∂closingCompactState π v).im from integral_im hi,
        mul_comm Complex.I, Complex.re_add_im]
    _ = _ := by rw [ha,hb,h,map_add,map_smul,add_apply,smul_apply,inner_add_right,inner_smul_right]

theorem closing_compact_state_mass (π : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    (closingCompactState π v).real univ = ‖v‖^2 := by
  have h := closing_compact_state_integral π v 1
  simpa [inner_self_eq_norm_sq_to_K,← Complex.ofReal_pow] using congrArg Complex.re h

/-- The ordinary compact scalar spectral law integrates the continuous Cayley
Cauchy symbol to the actual unbounded-operator resolvent matrix element. -/
theorem closing_cayley_compact_state_resolvent (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K)
    (v : H) (z : ℂ) (hz : z.im ≠ 0) :
    (∫ u, closingCayleyCauchySymbol z u ∂closingCompactState
      (cfcHom (R := ℂ) (closing_cayley_normal K hK)) v) =
      ⟪v, (closingNonrealResolvent K hK z hz).map v⟫_ℂ := by
  have h := closing_compact_state_integral (cfcHom (R := ℂ) (closing_cayley_normal K hK)) v
    (closingCayleySpectralCauchy K hK z hz)
  rw [closing_cayley_cfc_resolvent] at h
  exact h

end UV.SectorPlane
