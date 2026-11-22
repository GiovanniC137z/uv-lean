import UV.RevisionOpeningCritical

/-! Conversion of the channel comparison to the manuscript's physical
invariant and mass parameters, including the true unsubtracted tail. -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped NNReal Nat

namespace UV

def openingOscillatorPairDensity (e m Δ b S : ℝ) : ℝ :=
  (e ^ 2 / (12 * Real.pi ^ 2)) * openingPairDensity (4 * Δ * b) (m ^ 2 / Δ) (S / (4 * Δ))

/-- Exact identification of the threshold-weighted series with the on-cut
Poisson channel sum. The square root vanishes at and above the closed-channel
boundary, so the written full series includes precisely the accessible weight. -/
theorem openingOscillatorPairDensity_channel_sum {e m Δ b S : ℝ} (hΔ : 0 < Δ)
    (hb : 0 ≤ b) (hS : 0 < S) :
    openingOscillatorPairDensity e m Δ b S = (e ^ 2 / (12 * Real.pi ^ 2)) * ∑' n : ℕ,
      Real.exp (- (b * S)) * (b * S) ^ n / n ! *
        (Real.sqrt (1 - 4 * (m ^ 2 + n * Δ) / S) * (1 + 2 * (m ^ 2 + n * Δ) / S)) := by
  unfold openingOscillatorPairDensity openingPairDensity
  congr 1
  apply tsum_congr
  intro n
  have hmean : 4 * Δ * b * (S / (4 * Δ)) = b * S := by field_simp
  have hx : ((n : ℝ) + m ^ 2 / Δ) / (S / (4 * Δ)) = 4 * (m ^ 2 + n * Δ) / S := by
    field_simp
    ring
  rw [hmean, hx, poissonPMFReal, Real.coe_toNNReal _ (mul_nonneg hb hS.le)]
  rw [openingWeight_eq_of_nonneg (by positivity)]
  congr 3
  ring

/-- Both the critical polynomial upper bound and the supercritical
exponential bound yield the finite dispersion tail in `S`. -/
theorem openingOscillatorPairDensity_tail_of_critical_or_above {e m Δ b : ℝ}
    (hΔ : 0 < Δ) (hcrit : 1 ≤ 4 * Δ * b) :
    IntegrableOn (fun S ↦ openingOscillatorPairDensity e m Δ b S / S) (Ioi (4 * Δ)) := by
  let c : ℝ := 4 * Δ
  let f : ℝ → ℝ := fun M ↦ openingPairDensity (4 * Δ * b) (m ^ 2 / Δ) M / M
  have hc : 0 < c := by dsimp [c]; positivity
  have hmass : 0 ≤ m ^ 2 / Δ := by positivity
  have hi : IntegrableOn f (Ioi 1) := by
    rcases eq_or_lt_of_le hcrit with he | hlt
    · dsimp [f]
      rw [← he]
      exact openingPairDensity_critical_tail hmass
    · exact openingPairDensity_supercritical_tail hlt hmass
  have hs : IntegrableOn (fun S ↦ f (c⁻¹ * S)) (Ioi c) := by
    apply (integrableOn_Ioi_comp_mul_left_iff f c (inv_pos.mpr hc)).mpr
    simpa [inv_mul_cancel₀ hc.ne'] using hi
  have hh : IntegrableOn (fun S ↦ (e ^ 2 / (12 * Real.pi ^ 2) * c⁻¹) * f (c⁻¹ * S))
      (Ioi c) := hs.const_mul _
  apply hh.congr_fun _ measurableSet_Ioi
  intro S hS
  have hS0 : S ≠ 0 := ne_of_gt (hc.trans hS)
  have hd : (4 * Δ : ℝ) ≠ 0 := hc.ne'
  unfold openingOscillatorPairDensity
  dsimp [f, c]
  rw [inv_mul_eq_div]
  field_simp

end UV
