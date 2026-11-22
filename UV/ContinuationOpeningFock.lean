import UV.RevisionOpening
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! The normalized oscillator comparison vector in the number basis. Its
coefficients reproduce the exact Poisson weights at the prescribed on-cut
phase. Identifying the vector with the exponential of the oscillator
position operator uses an additional unbounded-operator theorem. -/

noncomputable section
open ProbabilityTheory
open scoped ENNReal NNReal Nat ComplexInnerProductSpace

namespace UV

def openingCoherentCoefficient (z : ℂ) (n : ℕ) : ℂ :=
  (Real.exp (-‖z‖ ^ 2 / 2) : ℂ) * z ^ n / (Real.sqrt (n ! : ℝ) : ℂ)

theorem openingCoherentCoefficient_poisson (z : ℂ) (n : ℕ) :
    ‖openingCoherentCoefficient z n‖ ^ 2 = poissonPMFReal (‖z‖ ^ 2).toNNReal n := by
  unfold openingCoherentCoefficient poissonPMFReal
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), div_pow, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg _), Real.coe_toNNReal _ (sq_nonneg _), pow_two (Real.exp _),
    ← Real.exp_add]
  have hpow : (‖z‖ ^ n) ^ 2 = (‖z‖ ^ 2) ^ n := by
    rw [← pow_mul, mul_comm n 2, pow_mul]
  rw [hpow, show -‖z‖ ^ 2 / 2 + -‖z‖ ^ 2 / 2 = -‖z‖ ^ 2 by ring]

/-- The infinite channel vector belongs to the physical positive ℓ² space. -/
def openingCoherentVector (z : ℂ) : ℓ²(ℕ, ℂ) := by
  refine ⟨openingCoherentCoefficient z, ?_⟩
  apply memℓp_gen
  have h := (poissonPMFRealSum (‖z‖ ^ 2).toNNReal).summable
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat, openingCoherentCoefficient_poisson]
  exact h

theorem openingCoherentVector_norm (z : ℂ) : ‖openingCoherentVector z‖ = 1 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (openingCoherentVector z)
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at h
  change ‖openingCoherentVector z‖ ^ 2 = ∑' n : ℕ, ‖openingCoherentCoefficient z n‖ ^ 2 at h
  simp_rw [openingCoherentCoefficient_poisson, (poissonPMFRealSum _).tsum_eq] at h
  nlinarith [norm_nonneg (openingCoherentVector z)]

def openingNumberState (n : ℕ) : ℓ²(ℕ, ℂ) := lp.single 2 n (1 : ℂ)

theorem openingNumberState_overlap (n : ℕ) (z : ℂ) :
    inner ℂ (openingNumberState n) (openingCoherentVector z) = openingCoherentCoefficient z n := by
  rw [openingNumberState, lp.inner_single_left]
  change inner ℂ (1 : ℂ) (openingCoherentCoefficient z n) = _
  simp

/-- The comparison uses the original real phase parameter on the invariant
`S`. The norm-square law follows with the unit state above. -/
theorem openingNumberState_on_cut_poisson {ω ξ b S : ℝ} (hω : 0 < ω)
    (hphase : ξ ^ 2 / (2 * ω) = b * S) (n : ℕ) :
    ‖inner ℂ (openingNumberState n)
      (openingCoherentVector (((ξ / Real.sqrt (2 * ω) : ℝ) : ℂ) * Complex.I))‖ ^ 2 =
      poissonPMFReal (b * S).toNNReal n := by
  rw [openingNumberState_overlap, openingCoherentCoefficient_poisson, norm_mul, Complex.norm_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (by positivity), hphase]

end UV
