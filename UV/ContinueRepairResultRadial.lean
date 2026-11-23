import UV.ContinueRepairResultMeasureBoost
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! The upper estimate for the true invariant-mass band of the radial
particle-hole spectrum holds uniformly in the spatial transfer direction.
The finite Euclidean tail forces sublinear growth of its spatial marginal. -/

noncomputable section
open Filter Set MeasureTheory Metric
open scoped Topology ENNReal InnerProductSpace Pointwise

namespace UV.NextOpticalRadial

private def radialMassSlot (u : ℝ → ℝ) (k : ChargeSpatialMomentum) := if k=0 then 1 else u ‖k‖

private def radialSpatialSlot (v : ℝ → ℝ) (k : ChargeSpatialMomentum) : ChargeSpatialMomentum :=
  (v ‖k‖*‖k‖⁻¹) • k

private theorem radialSpinor_split (u v : ℝ → ℝ) (k : ChargeSpatialMomentum) :
    radialSpinor u v k = WithLp.toLp 2 (Fin.cons (radialMassSlot u k) (fun i => radialSpatialSlot v k i)) := by
  by_cases hk : k=0
  · subst k
    ext i; refine Fin.cases ?_ (fun j => ?_) i
    · simp [radialSpinor,FurtherOptical.massAxis,radialMassSlot]
    · simp [radialSpinor,FurtherOptical.massAxis,radialSpatialSlot]
  · unfold radialSpinor radialMassSlot spinCoefficients radialSpatialSlot radialUnit
    simp [hk,mul_assoc]

private theorem radialPairWeight_split (u v : ℝ → ℝ) (p k : ChargeSpatialMomentum) :
    radialPairWeight u v p k = ((radialMassSlot u (k+p)-radialMassSlot u k)^2 +
      ‖radialSpatialSlot v (k+p)-radialSpatialSlot v k‖^2)/2 := by
  rw [radialPairWeight,radialSpinor_split,radialSpinor_split,EuclideanSpace.norm_sq_eq,Fin.sum_univ_succ]
  change (‖radialMassSlot u (k+p)-radialMassSlot u k‖^2+
    ∑ i : Fin 3, ‖(radialSpatialSlot v (k+p)-radialSpatialSlot v k) i‖^2)/2 = _
  rw [←EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]

private theorem radialPairWeight_isometry (U : ChargeSpatialMomentum ≃ₗᵢ[ℝ] ChargeSpatialMomentum)
    (u v : ℝ → ℝ) (p k : ChargeSpatialMomentum) :
    radialPairWeight u v (U p) (U k) = radialPairWeight u v p k := by
  have he (x) : radialMassSlot u (U x) = radialMassSlot u x := by simp [radialMassSlot]
  have hs (x) : radialSpatialSlot v (U x) = U (radialSpatialSlot v x) := by simp [radialSpatialSlot]
  rw [radialPairWeight_split,radialPairWeight_split,←map_add,he,he,hs,hs,←map_sub,U.norm_map]

theorem canonicalPairBandDensity_isometry (U : ChargeSpatialMomentum ≃ₗᵢ[ℝ] ChargeSpatialMomentum)
    (u v : ℝ → ℝ) (m s₁ s₂ : ℝ) (p : ChargeSpatialMomentum) :
    canonicalPairBandDensity u v m (U p) s₁ s₂ = canonicalPairBandDensity u v m p s₁ s₂ := by
  unfold canonicalPairBandDensity
  congr 1
  rw [←integral_indicator (compactPairBand_measurable m (U p) s₁ s₂),
    ←integral_indicator (compactPairBand_measurable m p s₁ s₂)]
  rw [←U.measurePreserving.integral_comp U.toHomeomorph.measurableEmbedding
    ((compactPairBand m (U p) s₁ s₂).indicator (radialPairWeight u v (U p)))]
  apply integral_congr_ae
  refine Eventually.of_forall fun k => ?_
  have hb : U k ∈ compactPairBand m (U p) s₁ s₂ ↔ k ∈ compactPairBand m p s₁ s₂ := by
    simp only [compactPairBand,mem_preimage,pairInvariantMass,FurtherOptical.energy,←map_add,U.norm_map,norm_neg]
  change (compactPairBand m (U p) s₁ s₂).indicator _ (U k) = _
  by_cases hk : k ∈ compactPairBand m p s₁ s₂
  · rw [indicator_of_mem (hb.mpr hk),indicator_of_mem hk,radialPairWeight_isometry]
  · rw [indicator_of_notMem (fun h => hk (hb.mp h)),indicator_of_notMem hk]

theorem canonicalPairBandDensity_upper_all_directions {u v : ℝ → ℝ}
    (huM : Measurable u) (hvM : Measurable v) (hu : ∀ r, 0 ≤ u r) (hUnit : ∀ r, u r^2+v r^2=1)
    {m s₁ s₂ : ℝ} (hm : 0 < m) (p : ChargeSpatialMomentum) (hp : p ≠ 0) (hs₂ : 0 < s₂)
    (hLarge : s₂/m ≤ ‖p‖) (hWidth : Real.sqrt (s₂/4) ≤ ‖p‖) :
    canonicalPairBandDensity u v m p s₁ s₂ ≤ (24*s₂*ContinuationBoostSpectrum.spatialMeasureFactor) *
      ∫ r in Icc ((m^2/(2*s₂))*‖p‖) (2*‖p‖), v r^2 := by
  let q := ‖p‖ • (spatialAxis : ChargeSpatialMomentum)
  have he : ‖q‖ = ‖p‖ := by simp [q,norm_smul,spatialAxis.property]
  have hR := Submodule.reflection_sub he
  rw [←show canonicalPairBandDensity u v m _ s₁ s₂ = canonicalPairBandDensity u v m p s₁ s₂ from congrArg (fun t => canonicalPairBandDensity u v m t s₁ s₂) hR,
    canonicalPairBandDensity_isometry]
  exact canonicalPairBandDensity_upper huM hvM hu hUnit hm (norm_pos_iff.mpr hp) hs₂ hLarge hWidth

theorem canonicalPairBandDensity_sublinear {u v : ℝ → ℝ}
    (huM : Measurable u) (hvM : Measurable v) (hu : ∀ r, 0 ≤ u r) (hUnit : ∀ r, u r^2+v r^2=1)
    {m s₁ s₂ R : ℝ} (hm : 0 < m) (hs₂ : 0 < s₂)
    (hTail : IntegrableOn (fun r => v r^2/r) (Ioi R)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ p : ChargeSpatialMomentum, N ≤ ‖p‖ →
      canonicalPairBandDensity u v m p s₁ s₂ ≤ ε*‖p‖ := by
  let a := m^2/(2*s₂)
  let C := 24*s₂*ContinuationBoostSpectrum.spatialMeasureFactor
  have ha : 0 < a := by dsimp [a]; positivity
  have hC : 0 ≤ C := mul_nonneg (by positivity) ContinuationBoostSpectrum.spatialMeasureFactor_nonneg
  have hz := (mixingHarmonicBand_tendsto_zero (b := 2) v ha hTail).const_mul (2*C)
  rw [mul_zero] at hz
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hz.eventually_lt_const hε)
  let B := max 1 (max N (max (R/a+1) (max (s₂/m) (Real.sqrt (s₂/4)))))
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨B,by linarith,?_⟩
  intro p hP
  let S := ‖p‖
  have hS : 0 < S := lt_of_lt_of_le (by linarith : 0 < B) hP
  have hMax := (le_max_right (1:ℝ) _).trans hP
  have hSn := (le_max_left N _).trans hMax
  have hM := (le_max_right N _).trans hMax
  have hR := (le_max_left (R/a+1) _).trans hM
  have hW := (le_max_right (R/a+1) _).trans hM
  have hAx := canonicalPairBandDensity_upper_all_directions huM hvM hu hUnit hm p (norm_pos_iff.mp hS) hs₂
    ((le_max_left _ _).trans hW) ((le_max_right _ _).trans hW) (s₁ := s₁)
  let J := Icc (a*S) (2*S)
  have hJ : J ⊆ Ioi R := by
    intro r hr
    exact ((div_lt_iff₀ ha).mp (by dsimp [S]; linarith : R/a < S)).trans_le (by simpa [mul_comm] using hr.1)
  have hi := hTail.mono_set hJ
  have hvI : IntegrableOn (fun r => v r^2) J := (integrableOn_const (C := (1:ℝ)) measure_Icc_lt_top.ne).mono'
    (hvM.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun r => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]; nlinarith [hUnit r,sq_nonneg (u r)])
  have hI : (∫ r in J, v r^2) ≤ (2*S)*∫ r in J, v r^2/r := by
    rw [←integral_const_mul]
    refine setIntegral_mono_on hvI (hi.const_mul _) measurableSet_Icc fun r hr => ?_
    have hr₀ := (mul_pos ha hS).trans_le hr.1
    calc
      _ = r*(v r^2/r) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hr.2 (div_nonneg (sq_nonneg _) hr₀.le)
  have hLow := mul_le_mul_of_nonneg_left hI hC
  have ht := mul_le_mul_of_nonneg_right (hN S hSn).le hS.le
  change canonicalPairBandDensity u v m p s₁ s₂ ≤ C*∫ r in J, v r^2 at hAx
  change (2*C*(∫ r in J, v r^2/r))*S ≤ ε*S at ht
  exact hAx.trans (hLow.trans (by linarith only [ht]))

theorem canonicalPairBandDensity_global_sublinear {u v : ℝ → ℝ}
    (huM : Measurable u) (hvM : Measurable v) (hu : ∀ r, 0 ≤ u r) (hUnit : ∀ r, u r^2+v r^2=1)
    {m s₁ s₂ R : ℝ} (hm : 0 < m) (hs₂ : 0 < s₂)
    (hTail : IntegrableOn (fun r => v r^2/r) (Ioi R)) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p : ChargeSpatialMomentum,
      canonicalPairBandDensity u v m p s₁ s₂ ≤ D + ε*‖p‖ := by
  obtain ⟨N,hN,hU⟩ := canonicalPairBandDensity_sublinear (s₁ := s₁) huM hvM hu hUnit hm hs₂ hTail hε
  let W := closedBall (0 : ChargeSpatialMomentum) (Real.sqrt (s₂+N^2))
  let D := ContinuationBoostSpectrum.spatialMeasureFactor*(volume.real W*4)
  have hD : 0 ≤ D := mul_nonneg ContinuationBoostSpectrum.spatialMeasureFactor_nonneg (by positivity)
  refine ⟨D,hD,fun p => ?_⟩
  by_cases h : N ≤ ‖p‖
  · linarith [hU p h]
  · have hx := le_of_not_ge h
    let K := compactPairBand m p s₁ s₂
    have hsub : K ⊆ W := (compactPairBand_bounded_all_transfers hs₂.le p).trans
      (closedBall_subset_closedBall (Real.sqrt_le_sqrt (add_le_add_left ((sq_le_sq₀ (norm_nonneg p) hN).mpr hx) _)))
    have hV : volume K ≠ ∞ := ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hsub)
    have hI : (∫ k in K, radialPairWeight u v p k) ≤ ∫ _ in K, (4:ℝ) := by
      apply setIntegral_mono_on (canonicalPairWeight_integrableOn huM hvM hu hUnit hs₂.le p)
        (integrableOn_const hV) (compactPairBand_measurable m p s₁ s₂)
      intro k _
      have h := radialPairWeight_upper hu hUnit p k
      nlinarith [hUnit ‖k‖,hUnit ‖k+p‖,sq_nonneg (u ‖k‖),sq_nonneg (u ‖k+p‖)]
    rw [setIntegral_const,smul_eq_mul] at hI
    have hV' : volume.real K ≤ volume.real W :=
      (ENNReal.toReal_le_toReal hV measure_closedBall_lt_top.ne).mpr (measure_mono hsub)
    have hB : canonicalPairBandDensity u v m p s₁ s₂ ≤ D :=
      mul_le_mul_of_nonneg_left (hI.trans (mul_le_mul_of_nonneg_right hV' (by norm_num)))
        ContinuationBoostSpectrum.spatialMeasureFactor_nonneg
    exact hB.trans (le_add_of_nonneg_right (mul_nonneg hε.le (norm_nonneg _)))

end UV.NextOpticalRadial
