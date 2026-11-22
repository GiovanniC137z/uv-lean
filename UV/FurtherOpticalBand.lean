import UV.FurtherOpticalProjector

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace UV.FurtherOptical

theorem pairWeight_continuous {m τ : ℝ} (hm : 0 < m) (hτ : 0 ≤ τ)
    (p : ChargeSpatialMomentum) : Continuous (pairWeight m τ p) := by
  have hC := coefficients_continuous (τ:=τ) hm
  rw [funext (pairWeight_eq_coefficientDistance hm hτ p)]
  exact (((hC.comp (continuous_id.add continuous_const)).sub hC).norm.pow 2).div_const 2

set_option maxHeartbeats 500000 in
/-- The local positive pair weight gives a strictly positive integral on
a positive-volume source region carrying only a compact timelike band. -/
theorem pair_positive_timelike_band_integral {m τ : ℝ} (hm : 0 < m) (hτ : 0 ≤ τ)
    {p : ChargeSpatialMomentum} (hp : p ≠ 0) :
    ∃ r s₁ s₂ : ℝ, 0 < r ∧ 0 < s₁ ∧ s₁ ≤ s₂ ∧
      (∀ k ∈ Metric.ball (0 : ChargeSpatialMomentum) r, pairInvariantSq m p k ∈ Icc s₁ s₂) ∧
      0 < ContinuationBoostSpectrum.spatialMeasureFactor *
        ∫ k in Metric.ball (0 : ChargeSpatialMomentum) r, pairWeight m τ p k := by
  obtain ⟨r, s₁, s₂, c, hr, hs₁, hn, hc, hband⟩ := pair_positive_timelike_ball hm hτ hp
  let S := Metric.ball (0:ChargeSpatialMomentum) r
  have hmS : MeasurableSet S := Metric.isOpen_ball.measurableSet
  have hfin : (volume : Measure ChargeSpatialMomentum) S < ∞ := Metric.isBounded_ball.measure_lt_top
  have hpos : 0 < (volume : Measure ChargeSpatialMomentum) S := Metric.measure_ball_pos volume 0 hr
  have hIntC : IntegrableOn (pairWeight m τ p) (Metric.closedBall (0:ChargeSpatialMomentum) r) :=
    (pairWeight_continuous hm hτ p).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 r)
  have hInt : IntegrableOn (pairWeight m τ p) S := hIntC.mono_set Metric.ball_subset_closedBall
  have hconst : IntegrableOn (fun _ : ChargeSpatialMomentum => c) S := integrableOn_const hfin.ne
  have hpoint : ∀ k ∈ S, c ≤ pairWeight m τ p k := fun k hk => (hband k hk).2
  have hlow : (∫ k in S, c) ≤ ∫ k in S, pairWeight m τ p k :=
    setIntegral_mono_on hconst hInt hmS hpoint
  have hcl : 0 < ∫ k in S, pairWeight m τ p k := by
    rw [setIntegral_const, smul_eq_mul] at hlow
    exact (mul_pos (ENNReal.toReal_pos hpos.ne' hfin.ne) hc).trans_le hlow
  refine ⟨r, s₁, s₂, hr, hs₁, hn, fun k hk => (hband k hk).1, ?_⟩
  have hfactor : 0 < ContinuationBoostSpectrum.spatialMeasureFactor := by
    unfold ContinuationBoostSpectrum.spatialMeasureFactor
    positivity
  exact mul_pos hfactor hcl

end UV.FurtherOptical
