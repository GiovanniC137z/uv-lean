import UV.ContinueThinCurrentRadial

/-! Fatou's lower bound for an ensemble of squared arclength currents.
The number of signed edges may depend on the history. -/

noncomputable section

namespace UV

open MeasureTheory Set Filter
open scoped ENNReal Topology NNReal

theorem thinCurrent_ensemble_shell_lower {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℕ) (edges : (u : Ω) → Fin (N u) → ThinCurrentSegment)
    (hprep : ∀ᵐ u ∂μ, thinCurrentPrepared (edges u))
    {φ : ThinCurrentPlane → ℝ} (hsm : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hnn : ∀ p, 0 ≤ φ p) (hrad : thinRadialWindow φ)
    (hs : ∀ p, φ p ≠ 0 → 1 < ‖p‖ ∧ ‖p‖ < 2) (R : ℕ → ℝ) (ht : Tendsto R atTop atTop)
    (hF : ∀ n, AEMeasurable (fun u => ENNReal.ofReal
      ((thinCurrentShell (edges u) φ (R n)).toReal/(R n)^3)) μ) :
    (∫⁻ u, ENNReal.ofReal (thinWindowPerimeterCoefficient φ * thinCurrentPerimeter (edges u)) ∂μ) ≤
      liminf (fun n => ∫⁻ u, ENNReal.ofReal ((thinCurrentShell (edges u) φ (R n)).toReal/(R n)^3) ∂μ) atTop := by
  apply le_trans _ (lintegral_liminf_le' hF)
  apply le_of_eq
  apply lintegral_congr_ae
  filter_upwards [hprep] with u hu
  have h := (thinCurrentShell_radial_perimeter (edges u) hu hsm hnn hrad hs).comp ht
  exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp h).liminf_eq.symm

theorem thinCurrent_ensemble_diverges {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℕ) (edges : (u : Ω) → Fin (N u) → ThinCurrentSegment)
    (hprep : ∀ᵐ u ∂μ, thinCurrentPrepared (edges u))
    (hnet : μ {u | ∃ p, thinCurrentNormSq (edges u) p ≠ 0} ≠ 0)
    {φ : ThinCurrentPlane → ℝ} (hsm : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hnn : ∀ p, 0 ≤ φ p) (hne : ∃ p, φ p ≠ 0) (hrad : thinRadialWindow φ)
    (hs : ∀ p, φ p ≠ 0 → 1 < ‖p‖ ∧ ‖p‖ < 2) (ρ : Measure ℝ≥0) (hρ : ρ ≠ 0)
    (hm : AEMeasurable (fun u => thinCurrentResponse (edges u) (thinCurrentSpectrum ρ)) μ) :
    ∫⁻ u, thinCurrentResponse (edges u) (thinCurrentSpectrum ρ) ∂μ = ⊤ := by
  by_contra hc
  have h := ae_lt_top' hm hc
  have hz : ∀ᵐ u ∂μ, ¬ ∃ p, thinCurrentNormSq (edges u) p ≠ 0 := by
    filter_upwards [hprep,h] with u hu hb hnet'
    exact hb.ne (thinCurrent_uv_infinite (edges u) hu (thinCurrent_nonzero_has_piece (edges u) hnet')
      hsm hnn hne hrad hs ρ hρ)
  exact hnet (by simpa only [not_not] using ae_iff.mp hz)

end UV
