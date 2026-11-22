import UV.FurtherBoundaryFourier

/-! Euclidean Fourier coordinate normalization on the fixed independent
momentum space. The map multiplies the coordinate by (2π); the norm in
the physical weight is the norm after this map. -/

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace UV.ContinuationBoundary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Lebesgue measure on physical momentum with the dimension-dependent
Fourier normalization. -/
def physicalMomentumMeasure : Measure E :=
  ENNReal.ofReal ((2 * Real.pi : ℝ) ^ Module.finrank ℝ E)⁻¹ • volume

theorem map_unitary_frequency_to_physical_momentum :
    Measure.map (fun q : E => (2 * Real.pi) • q) volume = physicalMomentumMeasure := by
  have h : 0 < 2 * Real.pi := mul_pos two_pos Real.pi_pos
  rw [Measure.map_addHaar_smul volume h.ne', physicalMomentumMeasure,
    abs_of_pos (inv_pos.mpr (pow_pos h _))]

theorem lintegral_physical_momentum {f : E → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ k, f k ∂physicalMomentumMeasure) =
      ∫⁻ q : E, f ((2 * Real.pi) • q) := by
  rw [← map_unitary_frequency_to_physical_momentum]
  exact lintegral_map hf (continuous_const_smul _).measurable

/-- Positive phase in the physical momentum variable, with argument
(kcdot x) and the manuscript's positive sign. -/
def physicalOverlapPhase (ν : ComplexMeasure E) (k : E) : ℂ :=
  charFun ν.re.toJordanDecomposition.posPart k -
    charFun ν.re.toJordanDecomposition.negPart k +
    Complex.I * (charFun ν.im.toJordanDecomposition.posPart k -
      charFun ν.im.toJordanDecomposition.negPart k)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem complex_overlap_phase_eq_physical (ν : ComplexMeasure E) (q : E) :
    complexOverlapPhase ν q = physicalOverlapPhase ν ((2 * Real.pi) • q) := by
  simp only [complexOverlapPhase, physicalOverlapPhase, positivePhase_eq_charFun]

theorem continuous_physical_overlap_phase (ν : ComplexMeasure E) :
    Continuous (physicalOverlapPhase ν) := by
  unfold physicalOverlapPhase
  exact (continuous_charFun.sub continuous_charFun).add
    ((continuous_charFun.sub continuous_charFun).const_mul _)

theorem overlap_energy_eq_physical_momentum (N : ℕ) (ν : ComplexMeasure E) :
    overlapEnergy N ν =
      ∫⁻ k, ENNReal.ofReal ((1 + ‖k‖ ^ 2) ^ N * ‖physicalOverlapPhase ν k‖ ^ 2)
        ∂physicalMomentumMeasure := by
  have hm : Measurable (fun k : E =>
      ENNReal.ofReal ((1 + ‖k‖ ^ 2) ^ N * ‖physicalOverlapPhase ν k‖ ^ 2)) :=
    (ENNReal.continuous_ofReal.comp
      (((continuous_const.add (continuous_norm.pow 2)).pow N).mul
      ((continuous_physical_overlap_phase ν).norm.pow 2))).measurable
  rw [lintegral_physical_momentum hm]
  simp only [overlapEnergy, complex_overlap_phase_eq_physical]

end UV.ContinuationBoundary
