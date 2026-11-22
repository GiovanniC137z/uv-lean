import UV.ExtendOpticalBandObstruction

/-! Positive measures of the actual radial pair and of the supplied
transverse timelike model. Equality on the timelike range transports
the measured compact-band weight to the scalar Lorentz comparison. -/

noncomputable section

open Filter Set MeasureTheory Metric
open scoped Topology ENNReal

namespace UV.NextOpticalRadial

theorem pairInvariantMass_measurable (m : ℝ) (p : ChargeSpatialMomentum) :
    Measurable (pairInvariantMass m p) := by
  unfold pairInvariantMass FurtherOptical.energy
  fun_prop

theorem compactPairBand_bounded_all_transfers {m s₁ s₂ : ℝ} (hs₂ : 0 ≤ s₂)
    (p : ChargeSpatialMomentum) :
    compactPairBand m p s₁ s₂ ⊆ closedBall (0 : ChargeSpatialMomentum) (Real.sqrt (s₂+‖p‖^2)) := by
  intro k hk
  rw [mem_closedBall, dist_zero_right]
  have hk' : pairInvariantMass m p k ≤ s₂ := hk.2
  rw [pairInvariantMass] at hk'
  have hE : ‖k‖ ≤ FurtherOptical.energy m (-k) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    change ‖k‖^2 ≤ FurtherOptical.energy m (-k)^2
    rw [FurtherOptical.energy_sq, norm_neg]
    linarith [sq_nonneg m]
  have h : ‖k‖ ≤ FurtherOptical.energy m (k+p) + FurtherOptical.energy m (-k) :=
    hE.trans (le_add_of_nonneg_left (Real.sqrt_nonneg (m^2+‖k+p‖^2)))
  have hNN : 0 ≤ s₂+‖p‖^2 := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hNN]
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by unfold FurtherOptical.energy; positivity)).mpr h
  linarith

theorem canonicalPairWeight_integrableOn {u v : ℝ → ℝ}
    (huMeas : Measurable u) (hvMeas : Measurable v) (hu : ∀ r, 0 ≤ u r)
    (hUnit : ∀ r, u r^2+v r^2=1) {m s₁ s₂ : ℝ} (hs₂ : 0 ≤ s₂)
    (p : ChargeSpatialMomentum) :
    IntegrableOn (radialPairWeight u v p) (compactPairBand m p s₁ s₂) := by
  have hm : Measurable (radialPairWeight u v p) := by
    have h := radialSpinor_measurable huMeas hvMeas
    unfold radialPairWeight
    exact (((h.comp (measurable_id.add measurable_const)).sub h).norm.pow_const 2).div_const 2
  have hFin : (volume : Measure ChargeSpatialMomentum) (compactPairBand m p s₁ s₂) ≠ ∞ :=
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne
      (measure_mono (compactPairBand_bounded_all_transfers hs₂ p))
  apply (integrableOn_const (C := (4:ℝ)) hFin).mono' hm.aestronglyMeasurable
  refine Eventually.of_forall fun k => ?_
  rw [Real.norm_of_nonneg (by unfold radialPairWeight; positivity)]
  refine (radialPairWeight_upper hu hUnit p k).trans ?_
  linarith [hUnit ‖k‖, hUnit ‖k+p‖, sq_nonneg (u ‖k‖), sq_nonneg (u ‖k+p‖)]

/-- The source pair's nonnegative measure in the invariant mass
variable, with the prescribed ((2pi)^{-3}) plane normalization. -/
def canonicalPairSpectrum (u v : ℝ → ℝ) (m : ℝ) (p : ChargeSpatialMomentum) : Measure ℝ :=
  ENNReal.ofReal ContinuationBoostSpectrum.spatialMeasureFactor •
    Measure.map (pairInvariantMass m p)
      (volume.withDensity (fun k => ENNReal.ofReal (radialPairWeight u v p k)))

/-- The time-time mass measure of a supplied transverse timelike
spectral law, after the positive mass-shell Jacobian. -/
def timelikeTimeSpectrum (ρ : Measure ℝ) (S : ℝ) : Measure ℝ :=
  ρ.withDensity fun s => ENNReal.ofReal (S^2/(2*Real.sqrt (S^2+s)))

theorem canonicalPairSpectrum_real_band {u v : ℝ → ℝ}
    (huMeas : Measurable u) (hvMeas : Measurable v) (hu : ∀ r, 0 ≤ u r)
    (hUnit : ∀ r, u r^2+v r^2=1) {m s₁ s₂ : ℝ} (hs₂ : 0 ≤ s₂)
    (p : ChargeSpatialMomentum) :
    (canonicalPairSpectrum u v m p).real (Icc s₁ s₂) = canonicalPairBandDensity u v m p s₁ s₂ := by
  have hi := canonicalPairWeight_integrableOn huMeas hvMeas hu hUnit (m := m) (s₁ := s₁) hs₂ p
  unfold canonicalPairSpectrum canonicalPairBandDensity Measure.real
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal ContinuationBoostSpectrum.spatialMeasureFactor_nonneg,
    Measure.map_apply (pairInvariantMass_measurable m p) measurableSet_Icc,
    show pairInvariantMass m p ⁻¹' Icc s₁ s₂ = compactPairBand m p s₁ s₂ from rfl,
    withDensity_apply _ (compactPairBand_measurable m p s₁ s₂),
    ← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall fun _ => by unfold radialPairWeight; positivity),
    ENNReal.toReal_ofReal (integral_nonneg fun _ => by unfold radialPairWeight; positivity)]

theorem timelikeTimeSpectrum_real_band (ρ : Measure ℝ) {s₁ s₂ S : ℝ}
    (h₁ : 0 < s₁) (hS : 0 < S) (hFin : ρ (Icc s₁ s₂) ≠ ∞) :
    (timelikeTimeSpectrum ρ S).real (Icc s₁ s₂) =
      ContinuationBoostSpectrum.timelikeDensity (ρ.restrict (Icc s₁ s₂)) S := by
  have hi := compactTimelikeWeight_integrable ρ h₁ hS hFin
  unfold timelikeTimeSpectrum ContinuationBoostSpectrum.timelikeDensity Measure.real
  rw [withDensity_apply _ measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun s => by positivity),
    ENNReal.toReal_ofReal (integral_nonneg fun _ => by positivity)]

/-- Nonintegrability follows from equality of the actual measured
timelike pair measure and a transverse Lorentz time-component measure.
The scalar optical amplitude may be intrinsic to the measured current
or set to one when the optical envelope is an external test. -/
theorem radialEuclideanDensity_not_integrable_of_timelike_measure_match
    {E : Type*} [Norm E] (diamond : SectorPlane.Plane E)
    (u v : SectorPlane.Plane E → ℝ → ℝ)
    (opticalAmplitude : SectorPlane.Plane E → ChargeSpatialMomentum → ℝ)
    (huMeas : Measurable (u diamond)) (hvMeas : Measurable (v diamond))
    (hu : ∀ r, 0 ≤ u diamond r) (hUnit : ∀ r, u diamond r^2+v diamond r^2=1)
    {A : ℝ} (hA : 0 < A) (hOptical : ∀ k, |opticalAmplitude diamond k| ≤ A)
    {m ω R : ℝ} (hm : 0 < m) (hR : 0 < R) (hRm : m ≤ R)
    (p : ChargeSpatialMomentum) (hp : p ≠ 0) (hRp : ‖p‖ ≤ R) (hRω : |ω| ≤ R)
    (hTest : opticalAmplitude diamond p ≠ 0)
    (ρ : Measure ℝ) {s₁ s₂ S₀ : ℝ}
    (h₁ : 0 < s₁) (h₁₂ : s₁ ≤ s₂) (hFin : ρ (Icc s₁ s₂) ≠ ∞)
    (hPos : ρ (Icc s₁ s₂) ≠ 0)
    (hMatch : ∀ S > S₀, 0 < S →
      let q := S • (spatialAxis : ChargeSpatialMomentum)
      (ENNReal.ofReal ((opticalAmplitude diamond q)^2) •
        canonicalPairSpectrum (u diamond) (v diamond) m q).restrict (Ioi 0) =
      (timelikeTimeSpectrum ρ S).restrict (Ioi 0)) :
    ¬ Integrable (fun k =>
      (ContinuationBoostSpectrum.spatialMeasureFactor * (opticalAmplitude diamond p)^2) *
        radialEuclideanDensity (u diamond) (v diamond) m ω p k) := by
  apply radialEuclideanDensity_not_integrable_of_compact_lorentz_band diamond u v opticalAmplitude
    huMeas hvMeas hu hUnit hA hOptical hm hR hRm p hp hRp hRω hTest ρ h₁ h₁₂ hFin hPos
  intro S hS₀ hS
  have hContain : Icc s₁ s₂ ⊆ Ioi (0:ℝ) := fun _ h => h₁.trans_le h.1
  let q := S • (spatialAxis : ChargeSpatialMomentum)
  let ν := canonicalPairSpectrum (u diamond) (v diamond) m q
  let w := (opticalAmplitude diamond q)^2
  have hEq := congrArg (fun μ : Measure ℝ => μ.real (Icc s₁ s₂)) (hMatch S hS₀ hS)
  change ((ENNReal.ofReal w • ν).restrict (Ioi 0)).real (Icc s₁ s₂) =
    ((timelikeTimeSpectrum ρ S).restrict (Ioi 0)).real (Icc s₁ s₂) at hEq
  simp only [Measure.real, Measure.restrict_apply measurableSet_Icc,
    inter_eq_left.mpr hContain, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (show 0 ≤ w from sq_nonneg _)] at hEq
  change w * (canonicalPairSpectrum (u diamond) (v diamond) m q).real (Icc s₁ s₂) =
    (timelikeTimeSpectrum ρ S).real (Icc s₁ s₂) at hEq
  rw [canonicalPairSpectrum_real_band huMeas hvMeas hu hUnit (h₁.le.trans h₁₂),
    timelikeTimeSpectrum_real_band ρ h₁ hS hFin] at hEq
  exact hEq

end UV.NextOpticalRadial
