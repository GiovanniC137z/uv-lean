import UV.ContinueCrossTailMeasure
import UV.AdvanceSpectrumTransform

/-! The signed cross law has a positive matrix completion on the fixed
sector plane with its full Jordan variation on each diagonal. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace UV.RevisionSpectrum

private theorem crossTail_window_finite (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] (n : ℕ) :
    IsFiniteMeasure (μ.restrict (spectralWindow n)) :=
  isFiniteMeasure_restrict.2 (isCompact_Icc.measure_lt_top.ne)

private def crossTailWindowJordan {a M m₂ : ℝ} (ha : 0 < a) (hm₂ : 0 ≤ m₂)
    (hadm : m₂ ≤ M^2 ∨ Real.sin (a*Real.sqrt (m₂-M^2)) = 0) (n : ℕ) :
    JordanDecomposition ℝ := by
  have hs := verify_cross_jordan_support (a:=a) (M:=M) hm₂
  have hi := verify_cross_jordan_representation ha hm₂ zero_lt_one hadm
  letI := verify_weighted_positive_spectrum_locallyFinite zero_lt_one hs.1 hi.1
  letI := verify_weighted_positive_spectrum_locallyFinite zero_lt_one hs.2 hi.2.1
  refine { posPart := (verifyCrossPositive a M m₂).restrict (spectralWindow n)
           negPart := (verifyCrossNegative a M m₂).restrict (spectralWindow n)
           posPart_finite := crossTail_window_finite _ n
           negPart_finite := crossTail_window_finite _ n
           mutuallySingular := ?_ }
  exact (verify_cross_jordan_mutuallySingular a M m₂).mono_ac
    Measure.absolutelyContinuous_restrict Measure.absolutelyContinuous_restrict

private theorem crossTail_window_jordan_apply (j : JordanDecomposition ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) :
    j.toSignedMeasure.toComplexMeasure 0 S = (j.posPart.real S-j.negPart.real S : ℝ) := by
  rw [SignedMeasure.toComplexMeasure_apply, JordanDecomposition.toSignedMeasure,
    Measure.toSignedMeasure_sub_apply hS, VectorMeasure.zero_apply]
  rfl

private theorem crossTail_window_restrict {a M m₂ : ℝ} (ha : 0 < a) (hm₂ : 0 ≤ m₂)
    (hadm : m₂ ≤ M^2 ∨ Real.sin (a*Real.sqrt (m₂-M^2)) = 0)
    {n N : ℕ} (hn : n ≤ N) :
    ((crossTailWindowJordan ha hm₂ hadm N).toSignedMeasure.toComplexMeasure 0).restrict
      (spectralWindow n) =
      (crossTailWindowJordan ha hm₂ hadm n).toSignedMeasure.toComplexMeasure 0 := by
  ext1 S hS
  have hw : MeasurableSet (spectralWindow n) := measurableSet_Icc
  rw [VectorMeasure.restrict_apply _ hw hS, crossTail_window_jordan_apply _ (hS.inter hw),
    crossTail_window_jordan_apply _ hS]
  simp only [crossTailWindowJordan, measureReal_restrict_apply hS,
    measureReal_restrict_apply (hS.inter hw)]
  rw [inter_assoc, inter_eq_left.2 (spectralWindow_mono hn)]

variable {E : Type*} [Norm E]

/-- The two equal diagonal measures are the actual Jordan total variation
and the real cross restrictions are computed from the signed law. -/
def crossTailMatrixCompletion (diamond : UV.SectorPlane.Plane E) {a M m₂ : ℝ}
    (ha : 0 < a) (hm₂ : 0 ≤ m₂)
    (hadm : m₂ ≤ M^2 ∨ Real.sin (a*Real.sqrt (m₂-M^2)) = 0) :
    SetwiseSpectralCompletion diamond := by
  have hs := verify_cross_jordan_support (a:=a) (M:=M) hm₂
  have hw := verify_cross_jordan_representation ha hm₂ zero_lt_one hadm
  have hpos : ∀ᵐ s ∂crossTailVariation a M m₂, 0 ≤ s := ae_add_measure_iff.2 hs
  have hi : Integrable (stieltjesWeight 1) (crossTailVariation a M m₂) := hw.1.add_measure hw.2.1
  have hfin := verify_weighted_positive_spectrum_locallyFinite zero_lt_one hpos hi
  refine ⟨crossTailVariation a M m₂, crossTailVariation a M m₂, hpos, hpos, hfin, hfin,
    fun n => (crossTailWindowJordan ha hm₂ hadm n).toSignedMeasure.toComplexMeasure 0,
    fun n => crossTail_window_restrict ha hm₂ hadm n.le_succ,
    fun n => crossTail_window_restrict ha hm₂ hadm (le_refl n), ?_⟩
  intro n S hS
  let j := crossTailWindowJordan ha hm₂ hadm n
  have hd : (crossTailVariation a M m₂).restrict (spectralWindow n) = j.posPart+j.negPart :=
    Measure.restrict_add _ _ _
  change ‖j.toSignedMeasure.toComplexMeasure 0 S‖^2 ≤
    ((crossTailVariation a M m₂).restrict (spectralWindow n)).real S *
    ((crossTailVariation a M m₂).restrict (spectralWindow n)).real S
  rw [crossTail_window_jordan_apply j hS, Complex.norm_real, Real.norm_eq_abs, hd,
    measureReal_add_apply, sq_abs]
  nlinarith [mul_nonneg (measureReal_nonneg (μ := j.posPart) (s := S))
    (measureReal_nonneg (μ := j.negPart) (s := S))]

theorem crossTailMatrixCompletion_diagonals (diamond : UV.SectorPlane.Plane E)
    {a M m₂ : ℝ} (ha : 0 < a) (hm₂ : 0 ≤ m₂)
    (hadm : m₂ ≤ M^2 ∨ Real.sin (a*Real.sqrt (m₂-M^2)) = 0) :
    (crossTailMatrixCompletion diamond ha hm₂ hadm).first = crossTailVariation a M m₂ ∧
    (crossTailMatrixCompletion diamond ha hm₂ hadm).second = crossTailVariation a M m₂ :=
  ⟨rfl,rfl⟩

private theorem crossTail_tendsto_window {μ : Measure ℝ} {w : ℝ → ℝ}
    (hi : Integrable w μ) (hs : ∀ᵐ s ∂μ, 0 ≤ s) :
    Tendsto (fun n => ∫ s in spectralWindow n, w s ∂μ) atTop (𝓝 (∫ s, w s ∂μ)) := by
  have ht := tendsto_setIntegral_of_monotone (μ := μ)
    (s := spectralWindow) (fun _ => measurableSet_Icc) spectralWindow_mono hi.integrableOn
  have heq : (⋃ n, spectralWindow n) = Ici 0 := by
    ext s
    simp only [mem_iUnion, spectralWindow, mem_Icc, mem_Ici]
    exact ⟨fun ⟨_,hs,_⟩ => hs,fun h => ⟨⌈s⌉₊,h,Nat.le_ceil s⟩⟩
  have hrestrict : μ.restrict (Ici 0) = μ := Measure.restrict_eq_self_of_ae_mem hs
  rw [heq, hrestrict] at ht
  exact ht

/-- The positive matrix completion has the prescribed signed cross
Stieltjes transform at every positive intrinsic Euclidean argument. -/
theorem crossTailMatrixCompletion_crossStieltjes (diamond : UV.SectorPlane.Plane E)
    {a M m₂ x : ℝ} (ha : 0 < a) (hm₂ : 0 ≤ m₂) (hx : 0 < x)
    (hadm : m₂ ≤ M^2 ∨ Real.sin (a*Real.sqrt (m₂-M^2)) = 0) :
    (crossTailMatrixCompletion diamond ha hm₂ hadm).crossStieltjes x =
      (verifyCrossCovariance a M m₂ x : ℂ) := by
  let C := crossTailMatrixCompletion diamond ha hm₂ hadm
  obtain ⟨hP,hN⟩ := verify_cross_jordan_support (a:=a) (M:=M) hm₂
  obtain ⟨hiP,hiN,hEq⟩ := verify_cross_jordan_representation ha hm₂ hx hadm
  have hi : Integrable (stieltjesWeight x) (crossTailVariation a M m₂) := hiP.add_measure hiN
  apply tendsto_nhds_unique (C.crossSample_tendsto hx hx hi hi)
  have ht := (crossTail_tendsto_window hiP hP).sub (crossTail_tendsto_window hiN hN)
  change Tendsto _ _ (𝓝 (diagonalStieltjes (verifyCrossPositive a M m₂) x -
    diagonalStieltjes (verifyCrossNegative a M m₂) x)) at ht
  rw [hEq] at ht
  apply (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).congr'
  filter_upwards with n
  let j := crossTailWindowJordan ha hm₂ hadm n
  change ((_ - _ : ℝ) : ℂ) = finiteCrossIntegral (j.toSignedMeasure.toComplexMeasure 0)
    (stieltjesWeight x)
  simp only [finiteCrossIntegral, SignedMeasure.re_toComplexMeasure, SignedMeasure.im_toComplexMeasure,
    JordanDecomposition.toJordanDecomposition_toSignedMeasure, SignedMeasure.toJordanDecomposition_zero,
    JordanDecomposition.zero_posPart, JordanDecomposition.zero_negPart, integral_zero_measure,
    sub_self, Complex.ofReal_zero, zero_mul, add_zero]
  rfl

end UV.RevisionSpectrum
