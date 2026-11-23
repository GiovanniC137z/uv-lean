import UV.ContinueRepairResultBoostTailGeometry

noncomputable section
open Filter Set MeasureTheory Metric Matrix
open scoped ENNReal Matrix ComplexOrder

namespace UV.NextOpticalRadial

open ContinuationBoostSpectrum

/-- The full radial no-go on one locked plane. Take a nonzero compact
tensor weight of the purported current on the selected timelike mass
band. Its canonical 00 marginal (including a bounded optical amplitude
when intrinsic) and its Lorentz transformation law contradict Euclidean
absolute integrability at any fixed nonzero tested transfer. For an
external optical test one takes the unsmeared marginal amplitude to be
one and retains the nonzero external multiplier at the tested transfer. -/
theorem exact_shell_radial_boost_obstruction {E : Type*} [Norm E] (diamond : SectorPlane.Plane E)
    (u v : SectorPlane.Plane E → ℝ → ℝ) (optical : ChargeSpatialMomentum → ℝ)
    (huM : Measurable (u diamond)) (hvM : Measurable (v diamond)) (hu : ∀ r, 0 ≤ u diamond r)
    (hUnit : ∀ r, u diamond r^2+v diamond r^2=1)
    {m ω s₁ s₂ A : ℝ} (hm : 0 < m) (hs₁ : 0 < s₁) (hs₁₂ : s₁ ≤ s₂)
    (hA : 0 < A) (hOpt : ∀ p, |optical p| ≤ A)
    (p : ChargeSpatialMomentum) (hp : p ≠ 0) {test : ℝ} (hTest : test ≠ 0)
    (μ : Measure CurrentMomentum)
    (hMarg : Measure.map Prod.snd μ = volume.withDensity (fun q => ENNReal.ofReal
      (optical q^2*canonicalPairBandDensity (u diamond) (v diamond) m q s₁ s₂)))
    {K : Set CurrentMomentum} (hK : IsCompact K) (T : DiracMatrix) (hT : T.PosSemidef) (hne : T ≠ 0)
    (hCov : ∀ i b, μ.real (currentBoost i b '' K) = (boostTimeRow i b ⬝ᵥ (T *ᵥ boostTimeRow i b)).re) :
    ¬ Integrable (fun k => (spatialMeasureFactor*test^2)*radialEuclideanDensity (u diamond) (v diamond) m ω p k) := by
  intro h
  have hSF : 0 < spatialMeasureFactor := by unfold spatialMeasureFactor; positivity
  let R := max 1 (max m (max ‖p‖ |ω|))
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  have hRm := le_max_right (1:ℝ) (max m (max ‖p‖ |ω|))
  have hRp := (le_max_right m _).trans hRm
  have hInt := (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr
    (mul_ne_zero hSF.ne' (pow_ne_zero 2 hTest))) _).mp h
  have hTail := radialEuclideanDensity_requires_mixing_tail diamond u v huM hvM hUnit hm.le hR
    ((le_max_left _ _).trans hRm) p hp ((le_max_left _ _).trans hRp) ((le_max_right _ _).trans hRp) hInt
  apply hne (compact_sublinear_lorentz_tensor_vanishes μ _ hMarg.le _ hK T hT hCov)
  intro ε hε
  obtain ⟨D,hD,hF⟩ := canonicalPairBandDensity_global_sublinear (s₁ := s₁) huM hvM hu hUnit hm
    (hs₁.trans_le hs₁₂) hTail (div_pos hε (sq_pos_of_pos hA) : 0 < ε/A^2)
  refine ⟨A^2*D,mul_nonneg (sq_nonneg _) hD,fun q => ?_⟩
  have hpos : 0 ≤ canonicalPairBandDensity (u diamond) (v diamond) m q s₁ s₂ :=
    mul_nonneg hSF.le (integral_nonneg fun _ => by unfold radialPairWeight; positivity)
  have hO : optical q^2 ≤ A^2 := by
    rw [←sq_abs]; exact (sq_le_sq₀ (abs_nonneg _) hA.le).mpr (hOpt q)
  apply (mul_le_mul hO (hF q) hpos (sq_nonneg _)).trans
  rw [mul_add]
  have he : A^2*(ε/A^2) = ε := by field_simp
  rw [←mul_assoc,he]

end UV.NextOpticalRadial
