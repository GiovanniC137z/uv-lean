import UV.ContinueWilsonContinuousDensity
import UV.ContinueWilsonMarkedHop
import Mathlib.Analysis.Fourier.Inversion

/-! Fourier inversion of each marked spin hop, with the angular carrier
frequency and the four-dimensional Jacobian. In particular the return at
zero displacement has a specified value for a circulation of length one. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Metric Real UV.SectorPlane
open scoped RealInnerProductSpace FourierTransform

namespace UV

/-- Forward sign used by the Wilson plane wave, in angular frequency. -/
def wilsonAngularTransform (f : OSFourSpace → ℂ) (p : OSFourSpace) : ℂ :=
  ∫ x, thinPlaneWave p x * f x

theorem wilson_angular_fourier (f : OSFourSpace → ℂ) (p : OSFourSpace) :
    𝓕 f p = wilsonAngularTransform f ((-(2*π)) • p) := by
  rw [Real.fourierIntegral_eq',wilsonAngularTransform]
  congr 1
  funext x
  simp only [thinPlaneWave,real_inner_smul_left,real_inner_comm p x,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_neg]
  congr 2
  ring

theorem wilson_angular_inversion {f : OSFourSpace → ℂ} (hc : Continuous f) (hi : Integrable f)
    (ht : Integrable (wilsonAngularTransform f)) (x : OSFourSpace) :
    (((2*π)^4)⁻¹ : ℝ) • (∫ p, thinPlaneWave p (-x) * wilsonAngularTransform f p) = f x := by
  have hπ : (-(2*π) : ℝ) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (by norm_num) pi_ne_zero)
  have ht' : Integrable (𝓕 f) := by
    simp_rw [funext (wilson_angular_fourier f)]
    exact (integrable_comp_smul_iff volume _ hπ).mpr ht
  have h := hi.fourier_inversion ht' (hc.continuousAt (x := x))
  rw [Real.fourierIntegralInv_eq'] at h
  have he : (fun p : OSFourSpace => Complex.exp ((↑(2*π*⟪p,x⟫) : ℂ) * Complex.I) • 𝓕 f p) =
      fun p => (fun k => thinPlaneWave k (-x)*wilsonAngularTransform f k) ((-(2*π)) • p) := by
    funext p
    simp only [wilson_angular_fourier,thinPlaneWave,real_inner_smul_left,inner_neg_right,smul_eq_mul,
      Complex.ofReal_mul,Complex.ofReal_neg]
    congr 2
    ring
  rw [he] at h
  rw [Measure.integral_comp_smul (volume : Measure OSFourSpace)
    (fun k => thinPlaneWave k (-x)*wilsonAngularTransform f k) (-(2*π))] at h
  simpa only [finrank_euclideanSpace,Fintype.card_fin,show (-(2*π))^4 = (2*π)^4 by ring,
    abs_of_nonneg (inv_nonneg.mpr (by positivity : 0 ≤ (2*π)^4))] using h

variable {ι : Type*} [Fintype ι]

def wilsonMarkedEntryDensity (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (us : WilsonDirections) (i j : Fin 4) (x : OSFourSpace) : ℂ :=
  (wilsonContinuousDensity L T x : ℂ) * wilsonDirectionWeight us x * wilsonSpinWeight L x i j

theorem wilson_entry_density_continuous {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (us : WilsonDirections) (i j : Fin 4) : Continuous (wilsonMarkedEntryDensity L T us i j) := by
  apply ((Complex.continuous_ofReal.comp (wilson_continuous_density_continuous hL T)).mul (wilson_direction_weight_continuous us)).mul
  simp only [wilsonSpinWeight,diracSlash,Matrix.sub_apply,Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul]
  fun_prop

theorem wilson_entry_density_compact {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (us : WilsonDirections) (i j : Fin 4) : HasCompactSupport (wilsonMarkedEntryDensity L T us i j) := by
  apply HasCompactSupport.intro' (isCompact_closedBall (0:OSFourSpace) (2*L)) isClosed_closedBall
  intro x hx
  simp only [wilsonMarkedEntryDensity,wilson_continuous_density_support hL T (by simpa using hx),
    Complex.ofReal_zero,zero_mul]

theorem wilson_entry_density_transform {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (us : WilsonDirections) (i j : Fin 4) :
    wilsonAngularTransform (wilsonMarkedEntryDensity L T us i j) = wilsonMarkedSpinHop L T us i j := by
  funext p
  rw [wilsonAngularTransform,wilsonMarkedSpinHop,←wilson_continuous_density_law hL T,
    integral_withDensity_eq_integral_toReal_smul (wilson_continuous_density_continuous hL T).measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext x
  rw [ENNReal.toReal_ofReal (wilson_continuous_density_nonneg L T x),Complex.real_smul,wilsonMarkedEntryDensity]
  ring

theorem wilson_marked_hop_inversion {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (us : WilsonDirections) (i j : Fin 4) (x : OSFourSpace) :
    (((2*π)^4)⁻¹ : ℝ) • (∫ p, thinPlaneWave p (-x) * wilsonMarkedSpinHop L T us i j p) =
      wilsonMarkedEntryDensity L T us i j x := by
  rw [←wilson_entry_density_transform hL T]
  let hc := wilson_entry_density_continuous hL T us i j
  apply wilson_angular_inversion hc (hc.integrable_of_hasCompactSupport (wilson_entry_density_compact hL T us i j))
  rw [wilson_entry_density_transform hL T]
  exact wilson_marked_spin_hop_integrable hL T us i j

end UV
