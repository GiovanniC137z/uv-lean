import UV.RootMagneticResponse
import UV.ContinueNormalHolonomyMagnetic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Magnetic-translation degeneracy on the plane. Landau gauge shifts the
oscillator centre by the conserved transverse physical wave number
divided by the signed root field. -/

noncomputable section
open MeasureTheory Real Filter

namespace UV.RootMagnetic

/-- The diagonal spectral density per horizontal area of a single
normalized Landau oscillator mode. The physical wave-number density
is dk/(2π). Translation of its centre yields |b|/(2π) for either root. -/
theorem root_landau_level_density (b x : ℝ) (φ : ℝ → ℂ) (hφ : ∫ u, ‖φ u‖^2 = 1) :
    (∫ k : ℝ, ‖φ (x+k/b)‖^2/(2*Real.pi)) = |b|/(2*Real.pi) := by
  rw [integral_div]
  have h := Measure.integral_comp_div (fun u : ℝ => ‖φ (x+u)‖^2) b
  have ht : (∫ u : ℝ, ‖φ (x+u)‖^2) = ∫ u : ℝ, ‖φ u‖^2 :=
    (measurePreserving_add_left volume x).integral_comp (Homeomorph.addLeft x).measurableEmbedding (fun u : ℝ => ‖φ u‖^2)
  simp only [ht,hφ,smul_eq_mul,mul_one] at h
  rw [h]

/-- The local scalar heat readout obtained by integrating the normalized
Landau fibres and the heat momenta in the two unmagnetized directions. -/
theorem root_landau_fiber_heat (b x : ℝ) {t : ℝ} (hb : b ≠ 0) (ht : 0 < t)
    (φ : ℕ → ℝ → ℂ) (hφ : ∀ n, ∫ u, ‖φ n u‖^2 = 1) :
    (∑' n : ℕ, ∫ k : ℝ, Real.exp (-((2*(n:ℝ)+1)*(|b| * t))) *
        (‖φ n (x+k/b)‖^2/(2*Real.pi)))/(4*Real.pi*t) =
      UV.ContinueNormalHolonomy.scalarMagneticDiagonal b t := by
  simp_rw [integral_const_mul,root_landau_level_density b x _ (hφ _),tsum_mul_right]
  rw [UV.ContinueNormalHolonomy.scalarMagneticDiagonal_landau hb ht]
  ring

end UV.RootMagnetic
