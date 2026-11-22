import UV.ExtendShellMeasure

/-! Covariant delta normalization of a single particle on the discrete
support ledger. The positive-shell density and the inverse delta
coefficient cancel on each regular spatial momentum. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory Set
open scoped ENNReal

variable {E H : Type*} [NormedAddCommGroup E]

/-- The diagonal support and spin factors multiply the ordinary spatial
delta. The support labels are the sector and offset of the fixed copy. -/
def Plane.shellStateNormalization (diamond diamond' : Plane E) (h h' : H)
    (m : ℝ) (p : Spatial) : Measure Spatial := by
  classical
  exact if diamond.s = diamond'.s ∧ diamond.b_s = diamond'.b_s ∧ h = h' then
    ENNReal.ofReal ((2 * Real.pi) ^ 3 * (2 * shellFrequency m p)) • Measure.dirac p
  else 0

/-- The spatial delta evaluates the test with the exact covariant
coefficient on the diagonal support and spin, and is zero elsewhere. -/
theorem Plane.shell_state_normalization_test (diamond diamond' : Plane E) (h h' : H)
    (m : ℝ) (p : Spatial) (f : Spatial → ℂ) :
    letI := Classical.propDecidable
    (∫ q, f q ∂diamond.shellStateNormalization diamond' h h' m p) =
      if diamond.s = diamond'.s ∧ diamond.b_s = diamond'.b_s ∧ h = h' then
        ((2 * Real.pi) ^ 3 * (2 * shellFrequency m p)) • f p
      else 0 := by
  classical
  by_cases hd : diamond.s = diamond'.s ∧ diamond.b_s = diamond'.b_s ∧ h = h'
  · have hp : 0 ≤ shellFrequency m p := Real.sqrt_nonneg _
    rw [if_pos hd, Plane.shellStateNormalization, if_pos hd, integral_smul_measure,
      integral_dirac, ENNReal.toReal_ofReal (by positivity)]
  · rw [if_neg hd, Plane.shellStateNormalization, if_neg hd, integral_zero_measure]

/-- Integrating the delta against the scalar density of the positive
shell recovers the normalized spin and support selector exactly. -/
theorem Plane.shell_state_normalization_resolves (diamond diamond' : Plane E) (h h' : H)
    (m : ℝ) (p : Spatial) (hp : 0 < shellFrequency m p) (f : Spatial → ℂ) :
    letI := Classical.propDecidable
    (∫ q, (((2 * Real.pi) ^ 3 * (2 * shellFrequency m q))⁻¹) • f q
      ∂diamond.shellStateNormalization diamond' h h' m p) =
      if diamond.s = diamond'.s ∧ diamond.b_s = diamond'.b_s ∧ h = h' then f p else 0 := by
  classical
  rw [diamond.shell_state_normalization_test diamond' h h' m p]
  split
  · rw [smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
  · rfl

end UV.SectorPlane
