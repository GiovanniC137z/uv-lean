import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Algebra.GroupWithZero.Commute

/-! Free source normalization on a bounded reducing operator block.
The normalizer is the actual inverse of the C*-algebra functional-calculus
positive square root. Invertibility is required explicitly, as it holds on
a bounded joint spectral cut separated from zero. This file does not posit
an unbounded joint spectral theorem or assume a covariance identity. -/

noncomputable section
open scoped InnerProductSpace

namespace UV

/-- A commuting unit has an inverse in the same commutant. -/
theorem source_commute_ringInverse_right {A : Type*} [MonoidWithZero A]
    {a b : A} (h : Commute a b) (hb : IsUnit b) : Commute a (Ring.inverse b) := by
  rw [Ring.inverse_of_isUnit hb]
  apply Commute.units_inv_right
  simpa only [hb.unit_spec] using h

/-- Taking the actual inverse preserves self-adjointness. -/
theorem source_ringInverse_selfAdjoint {A : Type*} [Semiring A] [StarRing A]
    {a : A} (ha : IsSelfAdjoint a) : IsSelfAdjoint (Ring.inverse a) := by
  change star (Ring.inverse a) = Ring.inverse a
  rw [← Ring.inverse_star, ha.star_eq]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The source endpoint operator on a bounded spectral block. `Ring.inverse`
is the unit inverse whenever the positive multiplier is invertible. -/
def sourceOperatorNormalizer (F : A) : A := Ring.inverse (CFC.sqrt F)

theorem sourceOperatorNormalizer_selfAdjoint (F : A) :
    IsSelfAdjoint (sourceOperatorNormalizer F) :=
  source_ringInverse_selfAdjoint (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg F))

theorem sourceOperator_sqrt_isUnit {F : A} (hF : 0 ≤ F) (hunit : IsUnit F) :
    IsUnit (CFC.sqrt F) := (CFC.isUnit_sqrt_iff F hF).mpr hunit

theorem sourceOperatorNormalizer_mul_sqrt {F : A} (hF : 0 ≤ F) (hunit : IsUnit F) :
    sourceOperatorNormalizer F * CFC.sqrt F = 1 :=
  Ring.inverse_mul_cancel _ (sourceOperator_sqrt_isUnit hF hunit)

theorem sourceOperator_sqrt_mul_normalizer {F : A} (hF : 0 ≤ F) (hunit : IsUnit F) :
    CFC.sqrt F * sourceOperatorNormalizer F = 1 :=
  Ring.mul_inverse_cancel _ (sourceOperator_sqrt_isUnit hF hunit)

theorem sourceOperator_sqrt_commute {F Δ : A} (hcomm : Commute F Δ) :
    Commute (CFC.sqrt F) Δ := by
  rw [CFC.sqrt_eq_cfc]
  exact hcomm.cfc_nnreal NNReal.sqrt

theorem sourceOperatorNormalizer_commute {F Δ : A} (hF : 0 ≤ F) (hunit : IsUnit F)
    (hcomm : Commute F Δ) : Commute (sourceOperatorNormalizer F) Δ := by
  exact (source_commute_ringInverse_right (sourceOperator_sqrt_commute hcomm).symm
    (sourceOperator_sqrt_isUnit hF hunit)).symm

/-- The mixed source--auxiliary covariance retains one square-root multiplier. -/
theorem sourceOperator_mixed_covariance {F : A} (hF : 0 ≤ F) (hunit : IsUnit F) (Δ : A) :
    sourceOperatorNormalizer F * (F * Δ) = CFC.sqrt F * Δ := by
  calc
    _ = (sourceOperatorNormalizer F * CFC.sqrt F) * (CFC.sqrt F * Δ) := by
      rw [mul_assoc, ← mul_assoc (CFC.sqrt F) (CFC.sqrt F) Δ,
        CFC.sqrt_mul_sqrt_self F hF]
    _ = _ := by rw [sourceOperatorNormalizer_mul_sqrt hF hunit, one_mul]

/-- Actual operator covariance equality, derived from CFC and commutation. -/
theorem sourceOperator_normalized_covariance {F Δ : A}
    (hF : 0 ≤ F) (hunit : IsUnit F) (hcomm : Commute F Δ) :
    sourceOperatorNormalizer F * (F * Δ) * star (sourceOperatorNormalizer F) = Δ := by
  rw [(sourceOperatorNormalizer_selfAdjoint F).star_eq,
    sourceOperator_mixed_covariance hF hunit Δ,
    (sourceOperator_sqrt_commute hcomm).eq, mul_assoc,
    sourceOperator_sqrt_mul_normalizer hF hunit, mul_one]

/-- Ordinary right amputation leaves the square-root multiplier. -/
theorem sourceOperator_mixed_amputation {F Δ : A}
    (hF : 0 ≤ F) (hunit : IsUnit F) (hΔ : IsUnit Δ) :
    (sourceOperatorNormalizer F * (F * Δ)) * Ring.inverse Δ = CFC.sqrt F := by
  rw [sourceOperator_mixed_covariance hF hunit Δ,
    Ring.mul_inverse_cancel_right Δ (CFC.sqrt F) hΔ]

/-- The complete bounded commuting-block calculation. -/
theorem free_source_normalization_bounded {F Δ : A}
    (hF : 0 ≤ F) (hunit : IsUnit F) (hcomm : Commute F Δ) (hΔ : IsUnit Δ) :
    IsSelfAdjoint (sourceOperatorNormalizer F) ∧
    Commute (sourceOperatorNormalizer F) Δ ∧
    sourceOperatorNormalizer F * (F * Δ) * star (sourceOperatorNormalizer F) = Δ ∧
    sourceOperatorNormalizer F * (F * Δ) = CFC.sqrt F * Δ ∧
    (sourceOperatorNormalizer F * (F * Δ)) * Ring.inverse Δ = CFC.sqrt F :=
  ⟨sourceOperatorNormalizer_selfAdjoint F, sourceOperatorNormalizer_commute hF hunit hcomm,
    sourceOperator_normalized_covariance hF hunit hcomm,
    sourceOperator_mixed_covariance hF hunit Δ, sourceOperator_mixed_amputation hF hunit hΔ⟩

/-- A bounded kinetic block gives its actual inverse covariance; commutation
with that covariance follows from commutation with the kinetic operator. -/
theorem free_source_normalization_bounded_kinetic {F K₀ : A}
    (hF : 0 ≤ F) (hFunit : IsUnit F) (hKunit : IsUnit K₀) (hcomm : Commute F K₀) :
    IsSelfAdjoint (sourceOperatorNormalizer F) ∧
    sourceOperatorNormalizer F * (F * Ring.inverse K₀) * star (sourceOperatorNormalizer F) =
      Ring.inverse K₀ ∧
    sourceOperatorNormalizer F * (F * Ring.inverse K₀) = CFC.sqrt F * Ring.inverse K₀ ∧
    (sourceOperatorNormalizer F * (F * Ring.inverse K₀)) * K₀ = CFC.sqrt F := by
  refine ⟨sourceOperatorNormalizer_selfAdjoint F,
    sourceOperator_normalized_covariance hF hFunit (source_commute_ringInverse_right hcomm hKunit),
    sourceOperator_mixed_covariance hF hFunit _, ?_⟩
  rw [sourceOperator_mixed_covariance hF hFunit, mul_assoc,
    Ring.inverse_mul_cancel K₀ hKunit, mul_one]

/-- The bounded operator result applies to arbitrary complex Hilbert spaces,
including infinite-dimensional reducing spectral subspaces. -/
theorem free_source_normalization_hilbert_block {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {F Δ : H →L[ℂ] H}
    (hF : 0 ≤ F) (hunit : IsUnit F) (hcomm : Commute F Δ) (hΔ : IsUnit Δ) :
    IsSelfAdjoint (sourceOperatorNormalizer F) ∧
    Commute (sourceOperatorNormalizer F) Δ ∧
    sourceOperatorNormalizer F * (F * Δ) * star (sourceOperatorNormalizer F) = Δ ∧
    sourceOperatorNormalizer F * (F * Δ) = CFC.sqrt F * Δ ∧
    (sourceOperatorNormalizer F * (F * Δ)) * Ring.inverse Δ = CFC.sqrt F :=
  free_source_normalization_bounded hF hunit hcomm hΔ

/-- A positive lower spectral bound gives invertibility; this is the actual
condition furnished by a bounded spectral cut separated from zero. -/
theorem sourceOperator_isUnit_of_gap {F : A} (hF : 0 ≤ F) {δ : ℝ} (hδ : 0 < δ)
    (hgap : algebraMap ℝ A δ ≤ F) : IsUnit F := by
  apply spectrum.isUnit_of_zero_notMem (R := ℝ)
  intro hzero
  have hδzero : δ ≤ (0:ℝ) :=
    (algebraMap_le_iff_le_spectrum (R := ℝ) (a := F)
      (IsSelfAdjoint.of_nonneg hF)).mp hgap 0 hzero
  exact (not_le_of_gt hδ) hδzero

/-- The auxiliary covariance is itself a positive operator whenever both
commuting factors are positive. -/
theorem sourceOperator_auxiliary_covariance_nonneg {F Δ : A}
    (hF : 0 ≤ F) (hΔ : 0 ≤ Δ) (hcomm : Commute F Δ) : 0 ≤ F*Δ := by
  have hp := conjugate_nonneg_of_nonneg hΔ (CFC.sqrt_nonneg F)
  have he : CFC.sqrt F * Δ * CFC.sqrt F = F*Δ := by
    rw [(sourceOperator_sqrt_commute hcomm).eq, mul_assoc,
      CFC.sqrt_mul_sqrt_self F hF, ← hcomm.eq]
  rwa [he] at hp

/-- The surviving mixed amputation is the identity exactly when the damping
multiplier is the identity. -/
theorem sourceOperator_mixed_amputation_eq_one_iff {F Δ : A}
    (hF : 0 ≤ F) (hunit : IsUnit F) (hΔ : IsUnit Δ) :
    (sourceOperatorNormalizer F * (F*Δ)) * Ring.inverse Δ = 1 ↔ F=1 := by
  rw [sourceOperator_mixed_amputation hF hunit hΔ, CFC.sqrt_eq_one_iff F hF]

/-- Both inverse hypotheses in the bounded kinetic calculation follow from
positive lower bounds, without an assumed covariance equality. -/
theorem free_source_normalization_spectral_cut {F K₀ : A}
    (hF : 0 ≤ F) (hK : 0 ≤ K₀) {δF δK : ℝ} (hδF : 0 < δF) (hδK : 0 < δK)
    (hgapF : algebraMap ℝ A δF ≤ F) (hgapK : algebraMap ℝ A δK ≤ K₀)
    (hcomm : Commute F K₀) :
    IsSelfAdjoint (sourceOperatorNormalizer F) ∧
    sourceOperatorNormalizer F * (F * Ring.inverse K₀) * star (sourceOperatorNormalizer F) =
      Ring.inverse K₀ ∧
    sourceOperatorNormalizer F * (F * Ring.inverse K₀) = CFC.sqrt F * Ring.inverse K₀ ∧
    (sourceOperatorNormalizer F * (F * Ring.inverse K₀)) * K₀ = CFC.sqrt F :=
  free_source_normalization_bounded_kinetic hF (sourceOperator_isUnit_of_gap hF hδF hgapF)
    (sourceOperator_isUnit_of_gap hK hδK hgapK) hcomm

/-- The smeared Hermitian covariance pairing on an actual Hilbert block. -/
theorem free_source_normalization_smeared {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {F Δ : H →L[ℂ] H}
    (hF : 0 ≤ F) (hunit : IsUnit F) (hcomm : Commute F Δ) (f g : H) :
    ⟪(sourceOperatorNormalizer F).adjoint f,
      (F*Δ) ((sourceOperatorNormalizer F).adjoint g)⟫_ℂ = ⟪f, Δ g⟫_ℂ := by
  rw [ContinuousLinearMap.adjoint_inner_left]
  change ⟪f, (sourceOperatorNormalizer F * (F*Δ) * star (sourceOperatorNormalizer F)) g⟫_ℂ = _
  rw [sourceOperator_normalized_covariance hF hunit hcomm]

/-- The mixed smeared pairing displays the same half-factor before
amputation, rather than silently identifying auxiliary and source fields. -/
theorem free_source_mixed_smeared {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {F : H →L[ℂ] H}
    (hF : 0 ≤ F) (hunit : IsUnit F) (Δ : H →L[ℂ] H) (f g : H) :
    ⟪(sourceOperatorNormalizer F).adjoint f, (F*Δ) g⟫_ℂ =
      ⟪f, (CFC.sqrt F * Δ) g⟫_ℂ := by
  rw [ContinuousLinearMap.adjoint_inner_left]
  change ⟪f, (sourceOperatorNormalizer F * (F*Δ)) g⟫_ℂ = _
  rw [sourceOperator_mixed_covariance hF hunit Δ]

/- The common-core union for arbitrary strongly commuting unbounded F and K₀
is not constructed here. It requires a joint projection-valued spectral
measure, density/reduction of the joint compact cuts, compatible restricted
functional calculi, and the maximal self-adjoint inverse-square-root domain.
The current mathlib LinearPMap adjoint/closure/core theory does not supply
that joint Borel spectral calculus. -/

end UV
