import UV.RevisionSpectrumBudget
import UV.ContinuationSectorPlane
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.Measure.Complex

/-! Setwise-positive spectral completions on a fixed sector plane.
The cross measure is given by its compatible finite restrictions to
bounded nonnegative spectral mass-squared intervals. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace UV.RevisionSpectrum

/-- A locally finite two-channel positive matrix spectral measure on one
diamond. The diagonals are ordinary positive measures and cross entries
are represented by their actual bounded restrictions. The complex
two-by-two determinant condition is imposed on every Borel set. -/
structure SetwiseSpectralCompletion {E : Type*} [Norm E]
    (diamond : UV.SectorPlane.Plane E) where
  first : Measure ℝ
  second : Measure ℝ
  first_nonnegative : ∀ᵐ s ∂first, 0 ≤ s
  second_nonnegative : ∀ᵐ s ∂second, 0 ≤ s
  first_locallyFinite : IsLocallyFiniteMeasure first
  second_locallyFinite : IsLocallyFiniteMeasure second
  cross : ℕ → ComplexMeasure ℝ
  cross_compatible : ∀ n, (cross (n+1)).restrict (Icc 0 (n : ℝ)) = cross n
  cross_supported : ∀ n, (cross n).restrict (Icc 0 (n : ℝ)) = cross n
  setwise_positive : ∀ n B, MeasurableSet B →
    ‖cross n B‖ ^ 2 ≤ (first.restrict (Icc 0 (n : ℝ))).real B *
      (second.restrict (Icc 0 (n : ℝ))).real B

/-- The ordinary integral against a finite complex measure. -/
def finiteCrossIntegral (ν : ComplexMeasure ℝ) (f : ℝ → ℝ) : ℂ :=
  ((∫ s, f s ∂ν.re.toJordanDecomposition.posPart) -
    (∫ s, f s ∂ν.re.toJordanDecomposition.negPart) : ℝ) +
  (((∫ s, f s ∂ν.im.toJordanDecomposition.posPart) -
    (∫ s, f s ∂ν.im.toJordanDecomposition.negPart) : ℝ) : ℂ) * Complex.I

/-- The weighted transforms of a positive diagonal are integration in the
spectral mass-squared variable on the same fixed diamond. -/
def diagonalStieltjes (ν : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ s, stieltjesWeight x s ∂ν

/-- Truncate an ordinary locally finite cross spectral measure in its
nonnegative spectral mass-squared coordinate. -/
def SetwiseSpectralCompletion.crossSample {E : Type*} [Norm E]
    {diamond : UV.SectorPlane.Plane E} (C : SetwiseSpectralCompletion diamond)
    (x : ℝ) (n : ℕ) : ℂ :=
  finiteCrossIntegral (C.cross n) (stieltjesWeight x)

theorem diagonal_stieltjes_pos {ν : Measure ℝ} (hν : ν ≠ 0)
    (hs : ∀ᵐ s ∂ν, 0 ≤ s) {x : ℝ} (hx : 0 < x)
    (hi : Integrable (stieltjesWeight x) ν) :
    0 < diagonalStieltjes ν x := by
  have hpos := hs.mono fun s hs' => stieltjesWeight_pos hx hs'
  apply lt_of_le_of_ne (integral_nonneg_of_ae (hpos.mono fun s hs' => hs'.le))
  intro he
  have hz := (integral_eq_zero_iff_of_nonneg_ae (hpos.mono fun s hs' => hs'.le) hi).1 he.symm
  have : ∀ᵐ s ∂ν, False := (hpos.and hz).mono fun s h => h.1.ne' h.2
  simp [ae_iff, Measure.measure_univ_eq_zero, hν] at this

theorem diagonal_stieltjes_weighted_integrable {ν : Measure ℝ}
    (hs : ∀ᵐ s ∂ν, 0 ≤ s) {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hi : Integrable (stieltjesWeight y) ν) :
    Integrable (stieltjesWeight x) ν := by
  simpa only [id_eq, mul_one] using
    (stieltjes_integrable (μ := ν) (s := id) (f := fun _ => 1)
      measurable_id hs aestronglyMeasurable_const hx hy (by simpa using hi))

theorem diagonal_stieltjes_scaled_lower {ν : Measure ℝ} (hs : ∀ᵐ s ∂ν, 0 ≤ s)
    {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x)
    (hi : Integrable (stieltjesWeight y) ν) :
    (y/x) * diagonalStieltjes ν y ≤ diagonalStieltjes ν x := by
  have hx := hy.trans_le hyx
  simpa only [diagonalStieltjes, stieltjes, id_eq, mul_one] using
    (stieltjes_scaled_lower (μ := ν) (s := id) (f := fun _ => 1) hs
      (Eventually.of_forall fun _ => zero_le_one) hy hyx
      (by simpa using diagonal_stieltjes_weighted_integrable hs hx hy hi)
      (by simpa using hi))

theorem diagonal_stieltjes_nonneg {ν : Measure ℝ} (hs : ∀ᵐ s ∂ν, 0 ≤ s)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ diagonalStieltjes ν x := by
  exact integral_nonneg_of_ae (hs.mono fun s hs' => inv_nonneg.mpr (add_nonneg hx hs'))

theorem SetwiseSpectralCompletion.cross_zero_of_first_zero {E : Type*} [Norm E]
    {diamond : UV.SectorPlane.Plane E} (C : SetwiseSpectralCompletion diamond)
    (hzero : C.first = 0) (n : ℕ) : C.cross n = 0 := by
  ext1 B hB
  rw [VectorMeasure.zero_apply]
  have h := C.setwise_positive n B hB
  simp only [hzero, Measure.restrict_zero, measureReal_zero, Pi.zero_apply, zero_mul] at h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (C.cross n B)])

theorem SetwiseSpectralCompletion.cross_zero_of_second_zero {E : Type*} [Norm E]
    {diamond : UV.SectorPlane.Plane E} (C : SetwiseSpectralCompletion diamond)
    (hzero : C.second = 0) (n : ℕ) : C.cross n = 0 := by
  ext1 B hB
  rw [VectorMeasure.zero_apply]
  have h := C.setwise_positive n B hB
  simp only [hzero, Measure.restrict_zero, measureReal_zero, Pi.zero_apply, mul_zero] at h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (C.cross n B)])

theorem SetwiseSpectralCompletion.diagonals_nonzero {E : Type*} [Norm E]
    {diamond : UV.SectorPlane.Plane E} (C : SetwiseSpectralCompletion diamond)
    {y : ℝ} {v : ℂ} (hlim : Tendsto (C.crossSample y) atTop (𝓝 v))
    (hv : v ≠ 0) : C.first ≠ 0 ∧ C.second ≠ 0 := by
  have hcontr : ¬ (∀ n, C.cross n = 0) := by
    intro hz
    have heq : C.crossSample y = 0 := by
      funext n
      simp [SetwiseSpectralCompletion.crossSample, finiteCrossIntegral, hz n, SignedMeasure.toJordanDecomposition_zero]
    rw [heq] at hlim
    exact hv (tendsto_nhds_unique hlim tendsto_const_nhds)
  exact ⟨fun h => hcontr (C.cross_zero_of_first_zero h),
    fun h => hcontr (C.cross_zero_of_second_zero h)⟩

private def setwiseSpectralTail (R : ℝ) (q : UV.ScalarMomentum) : ℝ :=
  if R ≤ ‖q‖ then (‖q‖^4)⁻¹ else 0

private theorem setwise_spectral_tail_nonintegrable {R : ℝ} (hR : 0 < R) :
    ¬ Integrable (setwiseSpectralTail R) := by
  intro hi
  have hradial := (integrable_fun_norm_addHaar (E := UV.ScalarMomentum) volume
    (f := fun r : ℝ => if R ≤ r then (r^4)⁻¹ else 0)).mp hi
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul] at hradial
  have hinv : IntegrableOn (fun r : ℝ => r ^ (-(1:ℝ))) (Ioi R) := by
    apply (hradial.mono_set (Ioi_subset_Ioi hR.le)).congr_fun _ measurableSet_Ioi
    intro r hr
    change R < r at hr
    dsimp only
    rw [if_pos hr.le, Real.rpow_neg_one]
    field_simp [(hR.trans hr).ne']
  have h := (integrableOn_Ioi_rpow_iff hR).mp hinv
  norm_num at h

/-- The actual shifted four-dimensional diagonal contraction diverges
whenever both positive diagonal measures are nonzero. -/
theorem positive_diagonal_bubble_nonintegrable {ν₁ ν₂ : Measure ℝ}
    (hν₁ : ν₁ ≠ 0) (hν₂ : ν₂ ≠ 0)
    (hs₁ : ∀ᵐ s ∂ν₁, 0 ≤ s) (hs₂ : ∀ᵐ s ∂ν₂, 0 ≤ s)
    {y : ℝ} (hy : 0 < y)
    (hi₁ : Integrable (stieltjesWeight y) ν₁) (hi₂ : Integrable (stieltjesWeight y) ν₂)
    (p : UV.ScalarMomentum) :
    ¬ Integrable (fun q : UV.ScalarMomentum =>
      diagonalStieltjes ν₁ (‖q‖^2) * diagonalStieltjes ν₂ (‖q+p‖^2)) := by
  let R := 2 * ‖p‖ + Real.sqrt y + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let c₁ := diagonalStieltjes ν₁ y
  let c₂ := diagonalStieltjes ν₂ y
  have hc₁ : 0 < c₁ := diagonal_stieltjes_pos hν₁ hs₁ hy hi₁
  have hc₂ : 0 < c₂ := diagonal_stieltjes_pos hν₂ hs₂ hy hi₂
  let K := (y*c₁)*(y*c₂)/4
  have hK : 0 < K := by dsimp [K]; positivity
  intro hI
  apply setwise_spectral_tail_nonintegrable hR
  apply (hI.const_mul K⁻¹).mono'
  · apply Measurable.aestronglyMeasurable
    exact Measurable.ite (measurableSet_le measurable_const measurable_norm)
      (by fun_prop) measurable_const
  filter_upwards with q
  have hnonneg := mul_nonneg
    (diagonal_stieltjes_nonneg hs₁ (sq_nonneg ‖q‖))
    (diagonal_stieltjes_nonneg hs₂ (sq_nonneg ‖q+p‖))
  by_cases hq : R ≤ ‖q‖
  · have hqn : 0 < ‖q‖ := hR.trans_le hq
    have htr := norm_sub_le (q+p) p
    rw [add_sub_cancel_right] at htr
    have hplus := norm_add_le q p
    have hpy : Real.sqrt y ≤ ‖q+p‖ := by dsimp [R] at hq; linarith [norm_nonneg p]
    have hqy : Real.sqrt y ≤ ‖q‖ := by dsimp [R] at hq; linarith [norm_nonneg p]
    have hupper : ‖q+p‖ ≤ 2*‖q‖ := by
      dsimp [R] at hq
      linarith [Real.sqrt_nonneg y]
    have hpy' : y ≤ ‖q+p‖^2 := by
      rw [← Real.sq_sqrt hy.le]
      exact (sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).2 hpy
    have hqy' : y ≤ ‖q‖^2 := by
      rw [← Real.sq_sqrt hy.le]
      exact (sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).2 hqy
    have hupper' : ‖q+p‖^2 ≤ 4*‖q‖^2 := by
      calc
        _ ≤ (2*‖q‖)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hupper
        _ = _ := by ring
    have h₁ := diagonal_stieltjes_scaled_lower hs₁ hy hqy' hi₁
    have h₂ := diagonal_stieltjes_scaled_lower hs₂ hy hpy' hi₂
    have h₂' : (y/(4*‖q‖^2))*c₂ ≤ diagonalStieltjes ν₂ (‖q+p‖^2) :=
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left hy.le (hy.trans_le hpy') hupper') hc₂.le).trans h₂
    have hb := mul_le_mul h₁ h₂' (by positivity)
      (diagonal_stieltjes_nonneg hs₁ (sq_nonneg ‖q‖))
    have heq : (y/‖q‖^2*c₁)*(y/(4*‖q‖^2)*c₂) = K * (‖q‖^4)⁻¹ := by
      dsimp [K]
      field_simp [hqn.ne']
    rw [heq] at hb
    rw [setwiseSpectralTail, if_pos hq, Real.norm_of_nonneg (by positivity)]
    rw [← div_eq_inv_mul, le_div_iff₀ hK, mul_comm]
    exact hb
  · rw [setwiseSpectralTail, if_neg hq, norm_zero]
    exact mul_nonneg (inv_nonneg.mpr hK.le) hnonneg

/-- Divergence for the admitted damped cross family in an arbitrary
setwise-positive two-channel completion with finite weighted diagonals.
The local cutoffs specify integration of the ordinary cross measure. -/
theorem setwise_completed_bubble_nonintegrable {E : Type*} [Norm E]
    {diamond : UV.SectorPlane.Plane E} (C : SetwiseSpectralCompletion diamond)
    (a M m : ℝ) {y : ℝ} (hy : 0 < y)
    (hi₁ : Integrable (stieltjesWeight y) C.first)
    (hi₂ : Integrable (stieltjesWeight y) C.second)
    (hcross : Tendsto (C.crossSample y) atTop
      (𝓝 ((Real.exp (-a * (Real.sqrt (y + M^2)-M)) / (y+m^2) : ℝ) : ℂ)))
    (p : UV.ScalarMomentum) :
    ¬ Integrable (fun q : UV.ScalarMomentum =>
      diagonalStieltjes C.first (‖q‖^2) * diagonalStieltjes C.second (‖q+p‖^2)) := by
  have hv : 0 < Real.exp (-a * (Real.sqrt (y + M^2)-M)) / (y+m^2) := by positivity
  obtain ⟨h₁,h₂⟩ := C.diagonals_nonzero hcross (Complex.ofReal_ne_zero.mpr hv.ne')
  exact positive_diagonal_bubble_nonintegrable h₁ h₂ C.first_nonnegative
    C.second_nonnegative hy hi₁ hi₂ p

end UV.RevisionSpectrum
