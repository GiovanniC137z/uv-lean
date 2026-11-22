import UV.ExtendOpticalBandIntegral
import UV.NextOpticalAnnulus

/-! The source's compact-band upper bound and the ultraviolet
obstruction for the normalized canonical radial spinor on one diamond. -/

noncomputable section

open Filter Set MeasureTheory Metric
open scoped Topology ENNReal InnerProductSpace

namespace UV.NextOpticalRadial

/-- The normalized equal-time charge weight on an actual invariant
band of the pair states of the radial Hamiltonian. -/
def canonicalPairBandDensity (u v : ℝ → ℝ) (m : ℝ) (p : ChargeSpatialMomentum) (s₁ s₂ : ℝ) : ℝ :=
  ContinuationBoostSpectrum.spatialMeasureFactor *
    ∫ k in compactPairBand m p s₁ s₂, radialPairWeight u v p k

/-- Exchanging the two massive constituent momenta preserves the
momentum measure and the exact invariant band. -/
theorem compactPairBand_integral_exchange (m : ℝ) (p : ChargeSpatialMomentum) (s₁ s₂ : ℝ)
    (f : ℝ → ℝ) :
    (∫ k in compactPairBand m p s₁ s₂, f ‖k+p‖) =
      ∫ k in compactPairBand m p s₁ s₂, f ‖k‖ := by
  let B := compactPairBand m p s₁ s₂
  let I := B.indicator (fun k => f ‖k‖)
  let T := (Homeomorph.addRight p).toMeasurableEquiv.trans (MeasurableEquiv.neg ChargeSpatialMomentum)
  have hp : MeasurePreserving T (volume : Measure ChargeSpatialMomentum) volume :=
    (Measure.measurePreserving_neg volume).comp (measurePreserving_add_right volume p)
  rw [← integral_indicator (compactPairBand_measurable m p s₁ s₂),
    ← integral_indicator (compactPairBand_measurable m p s₁ s₂)]
  calc
    _ = ∫ k, I (T k) := by
      apply integral_congr_ae
      refine Eventually.of_forall fun k => ?_
      change B.indicator (fun k => f ‖k+p‖) k = B.indicator (fun k => f ‖k‖) (-(k+p))
      by_cases hk : k ∈ B
      · rw [indicator_of_mem hk, indicator_of_mem ((compactPairBand_exchange m p k s₁ s₂).2 hk),
          norm_neg]
      · rw [indicator_of_notMem hk,
          indicator_of_notMem (fun hh => hk ((compactPairBand_exchange m p k s₁ s₂).1 hh))]
    _ = _ := hp.integral_comp T.measurableEmbedding I

/-- The radial-band estimate for the actual normalized pair weight.
The two radial masses are equal by exchange of the constituent momenta. -/
theorem canonicalPairBandDensity_upper {u v : ℝ → ℝ}
    (huM : Measurable u) (hvM : Measurable v) (hu : ∀ r, 0 ≤ u r)
    (hUnit : ∀ r, u r^2+v r^2=1)
    {m S s₁ s₂ : ℝ} (hm : 0 < m) (hS : 0 < S) (hs₂ : 0 < s₂)
    (hLarge : s₂/m ≤ S) (hWidth : Real.sqrt (s₂/4) ≤ S) :
    canonicalPairBandDensity u v m (S • (spatialAxis : ChargeSpatialMomentum)) s₁ s₂ ≤
      (24*s₂*ContinuationBoostSpectrum.spatialMeasureFactor) *
        ∫ r in Icc ((m^2/(2*s₂))*S) (2*S), v r^2 := by
  let p := S • (spatialAxis : ChargeSpatialMomentum)
  let B := compactPairBand m p s₁ s₂
  let I := Icc ((m^2/(2*s₂))*S) (2*S)
  let f (r : ℝ) := v r^2
  have hB := compactPairBand_measurable m p s₁ s₂
  have hF : Measurable f := hvM.pow_const 2
  have hz (r : ℝ) : 0 ≤ f r := sq_nonneg _
  have hb (r : ℝ) : f r ≤ 1 := by dsimp only [f]; nlinarith [hUnit r, sq_nonneg (u r)]
  have hBounded : B ⊆ closedBall (0 : ChargeSpatialMomentum) (2*S) := by
    intro k hk
    rw [mem_closedBall, dist_zero_right]
    exact (compactPairBand_radial_support hm hS hs₂ hLarge hWidth hk).1.2
  have hBV : (volume : Measure ChargeSpatialMomentum) B ≠ ∞ :=
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hBounded)
  have hI : IntegrableOn f I := (integrableOn_const (C := (1:ℝ)) measure_Icc_lt_top.ne).mono'
    hF.aestronglyMeasurable (Eventually.of_forall fun r => by
      rw [Real.norm_of_nonneg (hz r)]; exact hb r)
  have h₁ : IntegrableOn (fun k : ChargeSpatialMomentum => f ‖k‖) B :=
    (integrableOn_const (C := (1:ℝ)) hBV).mono' (hF.comp measurable_norm).aestronglyMeasurable
      (Eventually.of_forall fun k => by rw [Real.norm_of_nonneg (hz _)]; exact hb _)
  have h₂ : IntegrableOn (fun k : ChargeSpatialMomentum => f ‖k+p‖) B :=
    (integrableOn_const (C := (1:ℝ)) hBV).mono'
      ((hF.comp measurable_norm).comp (measurable_id.add measurable_const)).aestronglyMeasurable
      (Eventually.of_forall fun k => by rw [Real.norm_of_nonneg (hz _)]; exact hb _)
  have hPairMeas : Measurable (radialPairWeight u v p) := by
    have hM := radialSpinor_measurable huM hvM
    unfold radialPairWeight
    exact (((hM.comp (measurable_id.add measurable_const)).sub hM).norm.pow_const 2).div_const 2
  have hPair : IntegrableOn (radialPairWeight u v p) B := by
    apply (integrableOn_const (C := (4:ℝ)) hBV).mono' hPairMeas.aestronglyMeasurable
    refine Eventually.of_forall fun k => ?_
    rw [Real.norm_of_nonneg (by unfold radialPairWeight; positivity)]
    exact (radialPairWeight_upper hu hUnit p k).trans (by linarith [hb ‖k‖, hb ‖k+p‖])
  have hRad := compactPairBand_lintegral_radial_le (s₁ := s₁) hm hS hs₂ hLarge hWidth
    hF.ennreal_ofReal
  have hRad' : (∫ k in B, f ‖k‖) ≤ (6*s₂)*(∫ r in I, f r) := by
    rw [← ofReal_integral_eq_lintegral_ofReal h₁ (Eventually.of_forall fun _ => hz _),
      ← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall hz),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 6*s₂)] at hRad
    exact (ENNReal.ofReal_le_ofReal_iff (by
      exact mul_nonneg (by positivity) (integral_nonneg hz))).mp hRad
  have hPair' : (∫ k in B, radialPairWeight u v p k) ≤ 4*(∫ k in B, f ‖k‖) := by
    calc
      _ ≤ ∫ k in B, 2*(f ‖k‖+f ‖k+p‖) :=
        setIntegral_mono_on hPair ((h₁.add h₂).const_mul _) hB
          (fun k _ => radialPairWeight_upper hu hUnit p k)
      _ = _ := by
        rw [integral_const_mul, integral_add h₁ h₂, compactPairBand_integral_exchange m p s₁ s₂]
        ring
  unfold canonicalPairBandDensity
  calc
    _ ≤ ContinuationBoostSpectrum.spatialMeasureFactor * (4*((6*s₂)*(∫ r in I, f r))) :=
      mul_le_mul_of_nonneg_left (hPair'.trans (mul_le_mul_of_nonneg_left hRad' (by norm_num)))
        ContinuationBoostSpectrum.spatialMeasureFactor_nonneg
    _ = _ := by ring

/-- The time-component Jacobian weight is integrable against every
finite positive timelike band. -/
theorem compactTimelikeWeight_integrable (ρ : Measure ℝ) {s₁ s₂ S : ℝ}
    (h₁ : 0 < s₁) (hS : 0 < S) (hFin : ρ (Icc s₁ s₂) ≠ ∞) :
    IntegrableOn (fun s : ℝ => S^2/(2*Real.sqrt (S^2+s))) (Icc s₁ s₂) ρ := by
  apply (integrableOn_const (C := S/2) hFin).mono'
    ((measurable_const.div (measurable_const.mul
      (Real.continuous_sqrt.measurable.comp (measurable_const.add measurable_id)))).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (μ := ρ) (measurableSet_Icc (a := s₁) (b := s₂))] with s hs
  have hs' : 0 ≤ s := h₁.le.trans hs.1
  have hRoot : S ≤ Real.sqrt (S^2+s) := by
    have hh := Real.sqrt_le_sqrt (le_add_of_nonneg_right hs' : S^2 ≤ S^2+s)
    rwa [Real.sqrt_sq hS.le] at hh
  have hD : 0 < 2*Real.sqrt (S^2+s) := mul_pos (by norm_num) (hS.trans_le hRoot)
  change ‖S^2/(2*Real.sqrt (S^2+s))‖ ≤ S/2
  rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg S) hD.le)]
  apply (div_le_iff₀ hD).2
  nlinarith [mul_nonneg hS.le (sub_nonneg.mpr hRoot)]

/-- For a finite positive mass band, the spacetime spectral density of
the transverse Lorentz form has a linear lower along large shifts.
Restricting the measure to the very same invariant band is part of the statement. -/
theorem compactTimelikeDensity_linear_lower (ρ : Measure ℝ) {s₁ s₂ S : ℝ}
    (h₁ : 0 < s₁) (h₁₂ : s₁ ≤ s₂) (hS : 0 < S) (hS₂ : s₂ ≤ S^2)
    (hFin : ρ (Icc s₁ s₂) ≠ ∞) :
    S * (ρ.real (Icc s₁ s₂) / 4) ≤
      ContinuationBoostSpectrum.timelikeDensity (ρ.restrict (Icc s₁ s₂)) S := by
  let B := Icc s₁ s₂
  let μ := ρ.restrict B
  have hAE : ∀ᵐ s ∂μ, s ∈ B := ae_restrict_mem measurableSet_Icc
  have hNonneg : ∀ᵐ s ∂μ, 0 ≤ s := hAE.mono fun _ hs => h₁.le.trans hs.1
  have hMass : μ B = ρ B := Measure.restrict_apply_self ρ B
  have h := ContinuationBoostSpectrum.timelikeDensity_linear_lower μ hS h₁ h₁₂ hS₂
    hNonneg (hMass ▸ hFin) (compactTimelikeWeight_integrable ρ h₁ hS hFin)
  unfold Measure.real at *
  rw [hMass] at h
  convert h using 1
  ring

/-- Nonintegrability of the source's unsubtracted Euclidean density
for the literal radial projector. The single match hypothesis is the
admission that the measured canonical band weight agrees with a
positive timelike Lorentz spectral band on this same sector plane. -/
theorem radialEuclideanDensity_not_integrable_of_compact_lorentz_band
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
      (opticalAmplitude diamond (S • (spatialAxis : ChargeSpatialMomentum)))^2 *
        canonicalPairBandDensity (u diamond) (v diamond) m
          (S • (spatialAxis : ChargeSpatialMomentum)) s₁ s₂ =
        ContinuationBoostSpectrum.timelikeDensity (ρ.restrict (Icc s₁ s₂)) S) :
    ¬ Integrable (fun k =>
      (ContinuationBoostSpectrum.spatialMeasureFactor * (opticalAmplitude diamond p)^2) *
        radialEuclideanDensity (u diamond) (v diamond) m ω p k) := by
  have hs₂ := h₁.trans_le h₁₂
  let U := max S₀ (max (s₂/m) (Real.sqrt s₂ + 1))
  let c := ρ.real (Icc s₁ s₂)/4
  let C := A^2*(24*s₂*ContinuationBoostSpectrum.spatialMeasureFactor)
  let a := m^2/(2*s₂)
  let Dband (e : SectorPlane.Plane E) (S : ℝ) :=
    (opticalAmplitude e (S • (spatialAxis : ChargeSpatialMomentum)))^2 *
      canonicalPairBandDensity (u e) (v e) m (S • (spatialAxis : ChargeSpatialMomentum)) s₁ s₂
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := div_pos (ENNReal.toReal_pos hPos hFin) (by norm_num)
  have hSF : 0 < ContinuationBoostSpectrum.spatialMeasureFactor := by
    unfold ContinuationBoostSpectrum.spatialMeasureFactor
    positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hSpos (S : ℝ) (hS : U < S) : 0 < S := by
    have h := (le_max_right (s₂/m) _).trans ((le_max_right S₀ _).trans hS.le)
    linarith [Real.sqrt_nonneg s₂]
  have hUpper (S : ℝ) (hS : U < S) :
      Dband diamond S ≤ C * ∫ r in Icc (a*S) (2*S), (v diamond r)^2 := by
    let q := S • (spatialAxis : ChargeSpatialMomentum)
    have hSL : s₂/m ≤ S := (le_max_left (s₂/m) _).trans ((le_max_right S₀ _).trans hS.le)
    have hSW : Real.sqrt (s₂/4) ≤ S := by
      apply (Real.sqrt_le_sqrt (by linarith [hs₂.le] : s₂/4 ≤ s₂)).trans
      have h := (le_max_right (s₂/m) (Real.sqrt s₂ + 1)).trans ((le_max_right S₀ _).trans hS.le)
      linarith
    have hB := canonicalPairBandDensity_upper huMeas hvMeas hu hUnit hm (hSpos _ hS)
      hs₂ hSL hSW (s₁ := s₁)
    have hO : (opticalAmplitude diamond q)^2 ≤ A^2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hA.le).2 (hOptical q)
    let B := 24*s₂*ContinuationBoostSpectrum.spatialMeasureFactor
    let rInt := ∫ r in Icc (a*S) (2*S), (v diamond r)^2
    have hBpos : 0 ≤ B := by dsimp [B]; positivity
    have hIntpos : 0 ≤ rInt := integral_nonneg fun _ => sq_nonneg _
    change (opticalAmplitude diamond q)^2 *
      canonicalPairBandDensity (u diamond) (v diamond) m q s₁ s₂ ≤ C * rInt
    calc
      _ ≤ A^2 * (B * rInt) :=
        mul_le_mul hO hB (by
          unfold canonicalPairBandDensity
          exact mul_nonneg hSF.le (integral_nonneg fun _ => by unfold radialPairWeight; positivity))
          (sq_nonneg _)
      _ = _ := by dsimp only [C, B]; ring
  have hLower (S : ℝ) (hS : U < S) : c*S ≤ Dband diamond S := by
    have hLeft := (le_max_left S₀ _).trans_lt hS
    have hS₂ : s₂ ≤ S^2 := by
      rw [← Real.sq_sqrt hs₂.le]
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (hSpos _ hS).le).mpr
      have h := (le_max_right (s₂/m) (Real.sqrt s₂ + 1)).trans ((le_max_right S₀ _).trans hS.le)
      linarith
    have h := compactTimelikeDensity_linear_lower ρ h₁ h₁₂ (hSpos _ hS) hS₂ hFin
    change c*S ≤ (opticalAmplitude diamond (S • (spatialAxis : ChargeSpatialMomentum)))^2 *
      canonicalPairBandDensity (u diamond) (v diamond) m
        (S • (spatialAxis : ChargeSpatialMomentum)) s₁ s₂
    rw [hMatch S hLeft (hSpos _ hS), mul_comm]
    exact h
  have hFalse := radialEuclideanDensity_not_integrable_of_band diamond u v Dband huMeas hvMeas hUnit
    hm.le hR hRm p hp hRp hRω ha hC hc hUpper hLower
  intro h
  exact hFalse ((integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (mul_ne_zero hSF.ne' (pow_ne_zero 2 hTest))) _).mp h)

end UV.NextOpticalRadial
