import UV.ContinueRepairResultSpectralBandGeometry

noncomputable section
open Set MeasureTheory Metric Matrix
open scoped ENNReal Matrix ComplexOrder

namespace UV.NextOpticalRadial

open ContinuationBoostSpectrum

/-- The exact radial no-go from unrestricted positive vector spectral
measures and nonzero trace on the *same* invariant band as the actual
pair marginal. The full tensor boost law is restricted using the
explicit Minkowski mass of the plane; no rest-frame disintegration
or density in invariant mass is a hypothesis. -/
theorem exact_shell_radial_no_positive_timelike_trace {E : Type*} [Norm E] (diamond : SectorPlane.Plane E)
    (u v : SectorPlane.Plane E → ℝ → ℝ) (optical : ChargeSpatialMomentum → ℝ)
    (huM : Measurable (u diamond)) (hvM : Measurable (v diamond)) (hu : ∀ r, 0 ≤ u diamond r)
    (hUnit : ∀ r, u diamond r^2+v diamond r^2=1)
    {m ω s₁ s₂ A : ℝ} (hm : 0 < m) (hs₁ : 0 < s₁) (hs₁₂ : s₁ ≤ s₂)
    (hA : 0 < A) (hOpt : ∀ p, |optical p| ≤ A)
    (p : ChargeSpatialMomentum) (hp : p ≠ 0) {test : ℝ} (hTest : test ≠ 0)
    (μ σ : Measure CurrentMomentum) [IsFiniteMeasureOnCompacts σ]
    (hMarg : Measure.map Prod.snd (μ.restrict (currentSpectralBand s₁ s₂)) =
      volume.withDensity (fun q => ENNReal.ofReal (optical q^2*canonicalPairBandDensity (u diamond) (v diamond) m q s₁ s₂)))
    (T : Set CurrentMomentum → DiracMatrix) (hT : ∀ K, IsCompact K → (T K).PosSemidef)
    (hTrace : ∀ K, IsCompact K → (T K).trace.re = σ.real K)
    (hCov : ∀ K, IsCompact K → ∀ i b, μ.real (currentBoost i b '' K) =
      (boostTimeRow i b ⬝ᵥ (T K *ᵥ boostTimeRow i b)).re)
    (hNonzero : σ (currentSpectralBand s₁ s₂) ≠ 0) :
    ¬ Integrable (fun k => (spatialMeasureFactor*test^2)*radialEuclideanDensity (u diamond) (v diamond) m ω p k) := by
  obtain ⟨K,hK,hKB,hpK⟩ := nonzero_compact_in_spectral_band σ hNonzero
  have hne : T K ≠ 0 := by
    intro he
    rw [←hTrace K hK,he,Matrix.trace_zero,Complex.zero_re] at hpK
    exact hpK.false
  exact exact_shell_radial_boost_obstruction diamond u v optical huM hvM hu hUnit hm hs₁ hs₁₂ hA hOpt p hp hTest
    _ hMarg hK (T K) (hT K hK) hne (fun i b => (restricted_time_boost μ hK hKB i b).trans (hCov K hK i b))

end UV.NextOpticalRadial
