import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Actual smeared covariance forms in a common spectral representation.
The construction of the joint spectral representation for arbitrary strongly
commuting unbounded operators is a separate obligation. -/

noncomputable section
open MeasureTheory

namespace UV

def spectralCovarianceIntegrand {X : Type*} (d : X → ℝ) (f g : X → ℂ) (x : X) : ℂ :=
  star (f x) * (d x : ℂ) * g x

def spectralCovarianceForm {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (d : X → ℝ) (f g : X → ℂ) : ℂ :=
  ∫ x, spectralCovarianceIntegrand d f g x ∂μ

def spectralTestMultiplier {X : Type*} (t : X → ℝ) (f : X → ℂ) (x : X) : ℂ :=
  (t x : ℂ) * f x

theorem free_source_spectral_factors {F : ℝ} (hF : 0 < F) (K : ℝ) :
    (Real.sqrt F)⁻¹ * (F / K) * (Real.sqrt F)⁻¹ = K⁻¹ ∧
      (Real.sqrt F)⁻¹ * (F / K) = Real.sqrt F / K ∧
      ((Real.sqrt F)⁻¹ * (F / K)) * K = Real.sqrt F * (K * K⁻¹) := by
  have hs : Real.sqrt F ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hF)
  have hsq := Real.sq_sqrt hF.le
  generalize Real.sqrt F = s at *
  constructor
  · rw [← hsq]
    field_simp
  · constructor
    · rw [← hsq]
      field_simp
    · rw [← hsq]
      field_simp

/-- The pointwise covariance identity precedes integration; it is not a
formal equality of unevaluated or default-zero partition integrals. -/
theorem normalized_spectral_covariance_integrand {X : Type*}
    (F K : X → ℝ) (f g : X → ℂ) {x : X} (hF : 0 < F x) :
    spectralCovarianceIntegrand (fun y => F y / K y)
      (spectralTestMultiplier (fun y => (Real.sqrt (F y))⁻¹) f)
      (spectralTestMultiplier (fun y => (Real.sqrt (F y))⁻¹) g) x =
      spectralCovarianceIntegrand (fun y => (K y)⁻¹) f g x := by
  have h := (free_source_spectral_factors hF (K x)).1
  unfold spectralCovarianceIntegrand spectralTestMultiplier
  simp only [star_mul, Complex.ofReal_inv, star_inv₀]
  have hs : star (Real.sqrt (F x) : ℂ) = (Real.sqrt (F x) : ℂ) := by simp
  rw [hs]
  have hc : ((Real.sqrt (F x))⁻¹ : ℂ) * ((F x / K x : ℝ) : ℂ) *
      ((Real.sqrt (F x))⁻¹ : ℂ) = ((K x)⁻¹ : ℂ) := by exact_mod_cast h
  calc
    _ = star (f x) * (((Real.sqrt (F x))⁻¹ : ℂ) * ((F x / K x : ℝ) : ℂ) *
        ((Real.sqrt (F x))⁻¹ : ℂ)) * g x := by ring
    _ = _ := by simpa only [Complex.ofReal_inv] using congrArg (fun z : ℂ => star (f x) * z * g x) hc

/-- On an admitted smeared test domain the physical-source covariance is the
undamped form. Integrability is transferred from that actual form. -/
theorem normalized_spectral_covariance {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F K : X → ℝ) (f g : X → ℂ)
    (hF : ∀ᵐ x ∂μ, 0 < F x)
    (hi : Integrable (spectralCovarianceIntegrand (fun y => (K y)⁻¹) f g) μ) :
    Integrable (spectralCovarianceIntegrand (fun y => F y / K y)
      (spectralTestMultiplier (fun y => (Real.sqrt (F y))⁻¹) f)
      (spectralTestMultiplier (fun y => (Real.sqrt (F y))⁻¹) g)) μ ∧
    spectralCovarianceForm μ (fun y => F y / K y)
      (spectralTestMultiplier (fun y => (Real.sqrt (F y))⁻¹) f)
      (spectralTestMultiplier (fun y => (Real.sqrt (F y))⁻¹) g) =
      spectralCovarianceForm μ (fun y => (K y)⁻¹) f g := by
  have he : (fun x => spectralCovarianceIntegrand (fun y => F y / K y)
      (spectralTestMultiplier (fun y => (Real.sqrt (F y))⁻¹) f)
      (spectralTestMultiplier (fun y => (Real.sqrt (F y))⁻¹) g) x) =ᵐ[μ]
      spectralCovarianceIntegrand (fun y => (K y)⁻¹) f g := by
    filter_upwards [hF] with x hx
    exact normalized_spectral_covariance_integrand F K f g hx
  exact ⟨hi.congr he.symm, integral_congr_ae he⟩

theorem mixed_source_spectral_covariance_integrand {X : Type*}
    (F K : X → ℝ) (f g : X → ℂ) {x : X} (hF : 0 < F x) :
    spectralCovarianceIntegrand (fun y => F y / K y)
      (spectralTestMultiplier (fun y => (Real.sqrt (F y))⁻¹) f) g x =
      spectralCovarianceIntegrand (fun y => Real.sqrt (F y) / K y) f g x := by
  have h := (free_source_spectral_factors hF (K x)).2.1
  unfold spectralCovarianceIntegrand spectralTestMultiplier
  simp only [star_mul, Complex.ofReal_inv, star_inv₀]
  have hs : star (Real.sqrt (F x) : ℂ) = (Real.sqrt (F x) : ℂ) := by simp
  rw [hs]
  have hc : ((Real.sqrt (F x))⁻¹ : ℂ) * ((F x / K x : ℝ) : ℂ) =
      ((Real.sqrt (F x) / K x : ℝ) : ℂ) := by exact_mod_cast h
  calc
    _ = star (f x) * (((Real.sqrt (F x))⁻¹ : ℂ) * ((F x / K x : ℝ) : ℂ)) * g x := by
      ring
    _ = _ := by simpa only [Complex.ofReal_inv] using congrArg (fun z : ℂ => star (f x) * z * g x) hc

theorem mixed_source_amputation {F K : ℝ} (hF : 0 < F) (hK : K ≠ 0) :
    ((Real.sqrt F)⁻¹ * (F / K)) * K = Real.sqrt F := by
  rw [(free_source_spectral_factors hF K).2.2, mul_inv_cancel₀ hK, mul_one]

end UV
