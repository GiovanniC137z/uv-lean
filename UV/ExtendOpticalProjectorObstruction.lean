import UV.ExtendOpticalSpectralMatch

/-! A finite-slot canonical density on a locked sector plane cannot
dominate the time-component weight of a positive timelike band.
A common external optical test preserves this contradiction. -/

noncomputable section

open Filter Set MeasureTheory
open scoped Topology ENNReal Matrix

namespace UV.NextOpticalRadial

/-- Every nonzero compact timelike band forces an incompatible growth
of the full equal-time canonical weight on the same diamond. It
suffices that the positive band be part of the proposed full density. -/
theorem finite_slot_density_cannot_dominate_timelike_band
    {E : Type*} [Norm E] {d : ℕ} (diamond : SectorPlane.Plane E)
    (occupied : SectorPlane.Plane E → ChargeSpatialMomentum → Matrix (Fin d) (Fin d) ℂ)
    (P₀ : Matrix (Fin d) (Fin d) ℂ)
    (hm : ∀ i j, Measurable (fun k => occupied diamond k i j))
    (hAdj : ∀ k, (occupied diamond k)ᴴ = occupied diamond k)
    (hProj : ∀ k, occupied diamond k * occupied diamond k = occupied diamond k)
    (hRank : ∀ k k', (occupied diamond k).trace = (occupied diamond k').trace)
    (hL2 : Integrable (fun k => chargeInclusiveSquare (occupied diamond k-P₀)))
    (ρ : Measure ℝ) {s₁ s₂ S₀ : ℝ} (h₁ : 0 < s₁) (h₁₂ : s₁ ≤ s₂)
    (hFin : ρ (Icc s₁ s₂) ≠ ∞) (hPos : ρ (Icc s₁ s₂) ≠ 0) :
    ¬ (∀ S > S₀, 0 < S →
      (timelikeTimeSpectrum ρ S).real (Icc s₁ s₂) ≤
        ContinuationBoostSpectrum.canonicalDensity (occupied diamond)
          (S • (spatialAxis : ChargeSpatialMomentum))) := by
  intro h
  let C := 2 * ContinuationBoostSpectrum.spatialMeasureFactor *
    ∫ k, chargeInclusiveSquare (occupied diamond k - P₀)
  let c := ρ.real (Icc s₁ s₂)/4
  have hc : 0 < c := div_pos (ENNReal.toReal_pos hPos hFin) (by norm_num)
  let S := max S₀ (max (Real.sqrt s₂) (C/c)) + 1
  let p := S • (spatialAxis : ChargeSpatialMomentum)
  have hS₀ : S₀ < S := (le_max_left S₀ _).trans_lt (lt_add_one _)
  have hSroot : Real.sqrt s₂ < S :=
    ((le_max_left (Real.sqrt s₂) (C/c)).trans (le_max_right S₀ _)).trans_lt (lt_add_one _)
  have hS : 0 < S := (Real.sqrt_nonneg _).trans_lt hSroot
  have hS₂ : s₂ ≤ S^2 := by
    rw [← Real.sq_sqrt (h₁.le.trans h₁₂)]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) hS.le).mpr hSroot.le
  have hLow := compactTimelikeDensity_linear_lower ρ h₁ h₁₂ hS hS₂ hFin
  rw [← timelikeTimeSpectrum_real_band ρ h₁ hS hFin] at hLow
  have hHigh := (ContinuationBoostSpectrum.canonicalDensity_bounded
    (occupied diamond) P₀ hm hAdj hProj hRank hL2 p).2
  have hBoth : S*c ≤ C := hLow.trans ((h S hS₀ hS).trans hHigh)
  have hLarge : C/c < S :=
    ((le_max_right (Real.sqrt s₂) (C/c)).trans (le_max_right S₀ _)).trans_lt (lt_add_one _)
  exact (not_lt_of_ge hBoth) ((div_lt_iff₀ hc).mp hLarge)

/-- The actual optical projector cannot dominate a positive timelike
band after the same external spatial test has been applied to both
weights. The optical factor is positive at every finite momentum. -/
theorem opticalProjector_cannot_dominate_tested_timelike_band
    {E : Type*} [Norm E] (diamond : SectorPlane.Plane E)
    {m τ : ℝ} (hm : 0 < m) (hτ : 0 < τ) (a : ℝ)
    (ρ : Measure ℝ) {s₁ s₂ S₀ : ℝ} (h₁ : 0 < s₁) (h₁₂ : s₁ ≤ s₂)
    (hFin : ρ (Icc s₁ s₂) ≠ ∞) (hPos : ρ (Icc s₁ s₂) ≠ 0) :
    ¬ (∀ S > S₀, 0 < S →
      Real.exp (-2*a*S) * (timelikeTimeSpectrum ρ S).real (Icc s₁ s₂) ≤
      Real.exp (-2*a*S) *
        ContinuationBoostSpectrum.canonicalDensity
          (fun k => FurtherOptical.projector (FurtherOptical.coefficients m τ k))
          (S • (spatialAxis : ChargeSpatialMomentum))) := by
  intro h
  let P : SectorPlane.Plane E → ChargeSpatialMomentum → DiracMatrix :=
    fun _ k => FurtherOptical.projector (FurtherOptical.coefficients m τ k)
  have hOb := finite_slot_density_cannot_dominate_timelike_band diamond P
    (FurtherOptical.projector FurtherOptical.massAxis)
    (fun i j => (FurtherOptical.projectorEntry_continuous (τ := τ) hm i j).measurable)
    (fun k => FurtherOptical.projector_adjoint _) (fun k =>
      FurtherOptical.projector_idempotent _ (FurtherOptical.coefficients_norm_sq hm hτ.le k))
    (fun k k' => (FurtherOptical.projector_trace _).trans (FurtherOptical.projector_trace _).symm)
    (FurtherOptical.projector_departure_integrable hm hτ) ρ (S₀ := S₀) h₁ h₁₂ hFin hPos
  exact hOb fun S hS₀ hS => le_of_mul_le_mul_left (h S hS₀ hS) (Real.exp_pos _)

end UV.NextOpticalRadial
