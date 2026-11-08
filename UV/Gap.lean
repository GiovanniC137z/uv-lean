import UV.KernelMeasure

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal

namespace UV

/-- A strictly positive lower bound on Laplace depth implies positive support. -/
theorem positive_gap_ae_positive (ρ : Measure ℝ) {τstar : ℝ}
    (hτstar : 0 < τstar) (hgap : ∀ᵐ τ ∂ρ, τstar ≤ τ) :
    ∀ᵐ τ ∂ρ, 0 < τ :=
  hgap.mono fun _ hτ => hτstar.trans_le hτ

/-- The gap alternative supplies both nonnegative support and the separate
no-atom condition required by the selected-line theorem. -/
theorem positive_gap_support_no_atom (ρ : Measure ℝ) {τstar : ℝ}
    (hτstar : 0 < τstar) (hgap : ∀ᵐ τ ∂ρ, τstar ≤ τ) :
    ρ (Iio 0) = 0 ∧ ρ {0} = 0 := by
  have hp := positive_gap_ae_positive ρ hτstar hgap
  have hn : ρ {τ : ℝ | ¬ 0 < τ} = 0 := ae_iff.mp hp
  constructor
  · apply measure_mono_null _ hn
    intro τ hτ
    exact not_lt.mpr hτ.le
  · apply measure_mono_null _ hn
    intro τ hτ
    have hτ' : τ = 0 := hτ
    simp [hτ']

/-- Inverse powers decrease above a positive gap, giving the source's explicit
finite-mass estimate for every nonnegative inverse-moment order. -/
theorem positive_gap_inverseMoment_bound (ρ : Measure ℝ) {τstar r : ℝ}
    (hτstar : 0 < τstar) (hgap : ∀ᵐ τ ∂ρ, τstar ≤ τ) (hr : 0 ≤ r) :
    inverseMoment ρ r ≤ ENNReal.ofReal (τstar ^ (-r)) * ρ (Ioi 0) := by
  unfold inverseMoment
  calc
    (∫⁻ τ in Ioi 0, ENNReal.ofReal (τ ^ (-r)) ∂ρ) ≤
        ∫⁻ _τ in Ioi 0, ENNReal.ofReal (τstar ^ (-r)) ∂ρ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae hgap] with τ hτ
      exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_nonpos hτstar hτ (neg_nonpos.mpr hr))
    _ = _ := by simp

/-- Finite mass and a positive gap imply every nonnegative inverse moment,
without an endpoint moment premise. -/
theorem positive_gap_inverseMoment_finite (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {τstar r : ℝ} (hτstar : 0 < τstar)
    (hgap : ∀ᵐ τ ∂ρ, τstar ≤ τ) (hr : 0 ≤ r) :
    inverseMoment ρ r < ⊤ :=
  lt_of_le_of_lt (positive_gap_inverseMoment_bound ρ hτstar hgap hr)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ρ _))

/-- The complete quantitative gap conclusion, including finiteness of the
explicit upper bound itself. -/
theorem positive_gap_inverseMoment_bound_finite
    (ρ : Measure ℝ) [IsFiniteMeasure ρ] {τstar r : ℝ}
    (hτstar : 0 < τstar) (hgap : ∀ᵐ τ ∂ρ, τstar ≤ τ) (hr : 0 ≤ r) :
    inverseMoment ρ r ≤ ENNReal.ofReal (τstar ^ (-r)) * ρ (Ioi 0) ∧
      ENNReal.ofReal (τstar ^ (-r)) * ρ (Ioi 0) < ⊤ :=
  ⟨positive_gap_inverseMoment_bound ρ hτstar hgap hr,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ρ _)⟩

theorem positive_gap_selected_endpoint (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {τstar d : ℝ} (hτstar : 0 < τstar)
    (hgap : ∀ᵐ τ ∂ρ, τstar ≤ τ) (hd : 0 ≤ d) :
    inverseMoment ρ (1 + d / 2) < ⊤ :=
  positive_gap_inverseMoment_finite ρ hτstar hgap (by linarith)

end UV
