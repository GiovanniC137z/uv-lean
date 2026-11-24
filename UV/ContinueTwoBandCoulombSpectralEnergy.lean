import UV.ContinueTwoBandPositiveCoulomb
import UV.ContinueTwoBandSpectralIntegral

/-! The positive representation and the charged-frequency integral of
the relative two-slot trace on the same selected Euclidean plane. -/

noncomputable section
open MeasureTheory

namespace UV.SectorPlane

/-- At fixed transfer the fermion-loop sign times the actual subtracted
trace agrees with the occupied-to-empty weight times the convolution of
the two positive spectral densities. Both sides use the displayed Fourier
normalizations, with one further factor for the transferred frequency. -/
theorem twoBand_coulomb_spectral_section {m : ℝ} (hm : 0 < m) (v w Ω : ℝ) :
    -(∫ ξ, twoBandRelativeBubble m v w ξ (ξ+Ω)) / (2*Real.pi)^2 =
      twoBandTransitionWeight m v w *
        ∫ ξ, twoBandFrequencyPair (twoBandGap m v) (twoBandGap m w) (ξ,Ω) := by
  let A := twoBandGap m v
  let B := twoBandGap m w
  have hA : 0 < A := twoBand_gap_pos hm v
  have hB : 0 < B := twoBand_gap_pos hm w
  have he := (twoBand_relative_bubble_frequency_integral hm v w Ω).2
  change (∫ ξ, twoBandRelativeBubble m v w ξ (ξ+Ω))/(2*Real.pi) =
    -(1-(m^2+v*w)/(A*B))*(A+B)/((A+B)^2+Ω^2) at he
  have hf := twoBand_lorentzian_convolution hA hB Ω
  have e (ξ : ℝ) : twoBandFrequencyPair A B (ξ,Ω) =
      ((2*A/(ξ^2+A^2))*(2*B/((ξ+Ω)^2+B^2)))/(2*Real.pi)^2 := by
    unfold twoBandFrequencyPair twoBandLorentzDensity
    ring
  change _ = ((1-(m^2+v*w)/(A*B))/2) * ∫ ξ, twoBandFrequencyPair A B (ξ,Ω)
  simp_rw [e]
  rw [integral_div]
  rw [show ∀ x : ℝ, x/(2*Real.pi)^2 = (x/(2*Real.pi))/(2*Real.pi) from fun _ => by ring,
    neg_div, he, show ∀ x : ℝ, x/(2*Real.pi)^2 = (x/(2*Real.pi))/(2*Real.pi) from fun _ => by ring,
    hf, add_comm (Ω^2) ((A+B)^2)]
  ring

/-- The integrated order-two coefficient vanishes if either the charge
or the hopping is switched off. The strictly positive case holds for
every real hopping strength, at fixed positive widths and mass. -/
theorem twoBand_coulomb_energy_pos_iff {m σ a : ℝ} (hm : 0 < m) (hσ : 0 < σ)
    (ha : 0 < a) (g q : ℝ) :
    (0 < ∫ x, twoBandPositiveCoulombIntegrand m g σ q a x) ↔ q ≠ 0 ∧ g ≠ 0 := by
  refine ⟨fun h => ⟨?_,?_⟩,fun h => twoBand_positive_coulomb_energy_pos hm hσ ha h.2 h.1⟩
  · intro e
    subst q
    simp [twoBandPositiveCoulombIntegrand,twoBandCoulombSpatialDensity,twoBandCoulombMultiplier] at h
  · intro e
    subst g
    have hz : twoBandTransitionWeight m 0 0 = 0 := by
      unfold twoBandTransitionWeight
      rw [←pow_two (twoBandGap m 0),twoBand_gap_sq]
      simp [hm.ne']
    simp [twoBandPositiveCoulombIntegrand,twoBandCoulombSpatialDensity,
      twoBandSpatialWeight,twoBandSpatialHop,hz] at h

end UV.SectorPlane
