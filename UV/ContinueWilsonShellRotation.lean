import UV.ContinueWilsonHopInversion
import UV.ContinueWilsonRoutedPhoton
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

/-! Orthogonal invariance of the actual A4 shell multiplier, displacement
law and its pointwise continuous density on the carrier four-plane. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Real UV.SectorPlane
open scoped RealInnerProductSpace Topology

namespace UV

variable {ι : Type*} [Fintype ι]

theorem wilson_shell_radial (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    {p q : OSFourSpace} (h : ‖p‖ = ‖q‖) : wilsonShellPhotonForm L T p = wilsonShellPhotonForm L T q := by
  let v := L • T p
  let w := L • T q
  let R := (ℝ ∙ (v-w))ᗮ.reflection
  have he : R v = w := Submodule.reflection_sub (by simp [v,w,norm_smul,h])
  have hi := (wilson_ball_isometry R).integral_comp R.toHomeomorph.measurableEmbedding
    (fun y => Complex.exp (Complex.I*(⟪w,y⟫:ℝ)))
  have hp (y) : ⟪w,R y⟫ = ⟪v,y⟫ := by rw [←he,R.inner_map_map]
  simpa only [hp] using hi

theorem wilson_displacement_charFun (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (p : OSFourSpace) :
    charFun (wilsonDisplacementMeasure L T) p = (wilsonShellPhotonForm L T p)^2 := by
  rw [charFun_apply,wilsonShellPhotonForm,←wilson_displacement_characteristic L T p]
  congr 1
  funext y
  rw [real_inner_comm y p,mul_comm]

theorem wilson_displacement_orthogonal (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (R : OSFourSpace ≃ₗᵢ[ℝ] OSFourSpace) :
    MeasurePreserving R (wilsonDisplacementMeasure L T) (wilsonDisplacementMeasure L T) := by
  let μ := wilsonDisplacementMeasure L T
  haveI : IsProbabilityMeasure (μ.map R) := Measure.isProbabilityMeasure_map R.continuous.measurable.aemeasurable
  refine ⟨R.continuous.measurable,Measure.ext_of_charFun (funext fun p => ?_)⟩
  have he (y : OSFourSpace) : ⟪R y,p⟫ = ⟪y,R.symm p⟫ := by
    conv_lhs => rw [←R.apply_symm_apply p]
    exact R.inner_map_map _ _
  calc
    charFun (μ.map R) p = charFun μ (R.symm p) := by
      rw [charFun_apply,charFun_apply,integral_map R.continuous.measurable.aemeasurable (by fun_prop)]
      simp only [he]
    _ = _ := by simp only [μ,wilson_displacement_charFun,wilson_shell_radial L T (R.symm.norm_map p)]

theorem wilson_continuous_density_orthogonal {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (R : OSFourSpace ≃ₗᵢ[ℝ] OSFourSpace) (x : OSFourSpace) : wilsonContinuousDensity L T (R x) = wilsonContinuousDensity L T x := by
  let f := fun y => (wilsonContinuousDensity L T y : ℂ)
  let χ := wilsonShellPhotonForm L T
  have he : wilsonAngularTransform f = fun p => χ p ^ 2 := by
    funext p
    have h := wilson_displacement_characteristic L T p
    rw [←wilson_continuous_density_law hL T,integral_withDensity_eq_integral_toReal_smul
      (wilson_continuous_density_continuous hL T).measurable.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h
    simpa only [wilsonAngularTransform,f,χ,wilsonShellPhotonForm,thinPlaneWave,Complex.real_smul,
      ENNReal.toReal_ofReal (wilson_continuous_density_nonneg L T _),mul_comm] using h
  have hc : Continuous f := Complex.continuous_ofReal.comp (wilson_continuous_density_continuous hL T)
  have hi : Integrable f := ((wilson_continuous_density_continuous hL T).integrable_of_hasCompactSupport
    (wilson_continuous_density_compact hL T)).ofReal
  have ht : Integrable (wilsonAngularTransform f) := by
    apply (wilson_actual_shell_square_integrable hL T).mono' _ (Eventually.of_forall fun p => ?_)
    · rw [he]
      exact (wilson_shell_form_continuous L T).measurable.pow_const 2 |>.aestronglyMeasurable
    · rw [he,norm_pow]
  have hR := R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding
    (fun k => thinPlaneWave k (-(R x))*wilsonAngularTransform f k)
  have hpoint (p) : thinPlaneWave (R p) (-(R x))*wilsonAngularTransform f (R p) = thinPlaneWave p (-x)*wilsonAngularTransform f p := by
    rw [←map_neg R x]
    simp only [thinPlaneWave,R.inner_map_map,he,χ,wilson_shell_radial L T (R.norm_map p)]
  simp only [hpoint] at hR
  apply Complex.ofReal_injective
  change f (R x) = f x
  rw [←wilson_angular_inversion hc hi ht (R x),←wilson_angular_inversion hc hi ht x,hR]

end UV
