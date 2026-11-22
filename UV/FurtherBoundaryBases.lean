import UV.ContinuationBoundaryPairing

/-! The paired boundary moment for arbitrary Hilbert bases. Only countably
many of the continuous matrix-entry functions can contribute on the
separable momentum plane, even when the boundary spaces are nonseparable. -/

noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace UV.ContinuationBoundary

/-- Countably many evaluations detect the support of a finite positive sum
of continuous functions on a separable space. -/
theorem continuous_family_countable_nonzero {V ι : Type*} [TopologicalSpace V] [SeparableSpace V]
    (f : ι → V → ℝ≥0∞) (hf : ∀ i, Continuous (f i))
    (hsum : ∀ k : V, (∑' i, f i k) ≠ ∞) :
    {i | ∃ k, f i k ≠ 0}.Countable := by
  obtain ⟨S, hSc, hSd⟩ := exists_countable_dense V
  apply (hSc.biUnion (t := fun k _ ↦ Function.support (fun i ↦ f i k))
    (fun k _ ↦ Summable.countable_support_ennreal (hsum k))).mono
  rintro i ⟨k, hk⟩
  obtain ⟨x, hxS, hxf⟩ := hSd.exists_mem_open (hf i).isOpen_support ⟨k, hk⟩
  exact mem_iUnion₂.mpr ⟨x, hxS, hxf⟩

/-- Tonelli for the complete continuous family, with the active countable
set constructed from an arbitrary index type. -/
theorem lintegral_tsum_continuous_finite_family {V ι : Type*} [TopologicalSpace V]
    [SeparableSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
    (μ : Measure V) (f : ι → V → ℝ≥0∞) (hf : ∀ i, Continuous (f i))
    (hsum : ∀ k : V, (∑' i, f i k) ≠ ∞) (w : V → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ k, w k * (∑' i, f i k) ∂μ) = ∑' i, ∫⁻ k, w k * f i k ∂μ := by
  classical
  let S : Set ι := {i | ∃ k, f i k ≠ 0}
  have hS : S.Countable := continuous_family_countable_nonzero f hf hsum
  letI : Countable S := hS.to_subtype
  have hzero {i : ι} (h : i ∉ S) (k : V) : f i k = 0 := by
    by_contra hn
    exact h ⟨k, hn⟩
  have hsumS (k : V) : (∑' i : S, f i k) = ∑' i, f i k := by
    apply tsum_subtype_eq_of_support_subset (f := fun i ↦ f i k)
    intro i hi
    exact ⟨k, hi⟩
  have hRight : (∑' i : S, ∫⁻ k, w k * f i k ∂μ) = ∑' i, ∫⁻ k, w k * f i k ∂μ := by
    apply tsum_subtype_eq_of_support_subset (f := fun i ↦ ∫⁻ k, w k * f i k ∂μ)
    intro i hi
    by_contra hn
    apply hi
    simp_rw [hzero hn, mul_zero, lintegral_zero]
  simp_rw [← hsumS, ← ENNReal.tsum_mul_left]
  rw [lintegral_tsum (fun i : S ↦ (hw.mul (hf i).measurable).aemeasurable), hRight]

variable {V H I O ι κ : Type*} [TopologicalSpace V] [SeparableSpace V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup I] [InnerProductSpace ℂ I]
  [NormedAddCommGroup O] [InnerProductSpace ℂ O] [CompleteSpace O]

/-- Exact paired Hilbert–Schmidt moment for unrestricted input and output
Hilbert bases. Continuity is only required of the scalar physical phase
entries. -/
theorem paired_coefficient_weighted_moment_arbitrary_bases
    (u : HilbertBasis ι ℂ I) (v : HilbertBasis κ ℂ O)
    (W : I →L[ℂ] H) (L : H →L[ℂ] O) (U : V → H →L[ℂ] H)
    (hU : ∀ i j, Continuous (fun k => pairedEntry u v W L U k i j))
    (hW : hilbertSchmidtSquare u W ≠ ∞) (hC : ∀ k, ‖U k‖ ≤ 1)
    (μ : Measure V) (w : V → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ k, w k * pairedCoefficient u W L U k ∂μ) =
      ∑' i, ∑' j, ∫⁻ k, w k * ENNReal.ofReal (‖pairedEntry u v W L U k i j‖ ^ 2) ∂μ := by
  let f (p : ι × κ) (k : V) := ENNReal.ofReal (‖pairedEntry u v W L U k p.1 p.2‖ ^ 2)
  have hf (p : ι × κ) : Continuous (f p) :=
    ENNReal.continuous_ofReal.comp ((hU p.1 p.2).norm.pow 2)
  have hsum (k : V) : (∑' p, f p k) = pairedCoefficient u W L U k := by
    rw [paired_coefficient_entry_expansion u v, ENNReal.tsum_prod']
  have hfin (k : V) : (∑' p, f p k) ≠ ∞ := by
    rw [hsum]
    exact paired_coefficient_finite u W L U k hW (hC k)
  have h := lintegral_tsum_continuous_finite_family μ f hf hfin w hw
  simp_rw [hsum] at h
  rw [ENNReal.tsum_prod'] at h
  exact h

end UV.ContinuationBoundary
