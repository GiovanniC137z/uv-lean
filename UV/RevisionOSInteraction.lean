import UV.RevisionOSMoments

/-! Spacetime integration for the scalar reflection witnesses. The source data
include the Gaussian covariance form and the absolute product moments needed
for Fubini. The slope is taken after the single global normalization. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace UV

variable {Y Ω ι : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]

def osSpatialPotential (ν : Measure Y) (D : Y → Ω → ℝ) (ω : Ω) : ℝ :=
  ∫ x, D x ω ∂ν

theorem osSpatialPotential_center {ν : Measure Y} [SFinite ν] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {D : Y → Ω → ℝ}
    (hD : Integrable (Function.uncurry D) (ν.prod μ))
    (hmean : ∀ᵐ x ∂ν, (∫ ω, D x ω ∂μ) = 0) :
    (∫ ω, osSpatialPotential ν D ω ∂μ) = 0 := by
  change (∫ ω, ∫ x, D x ω ∂ν ∂μ) = 0
  rw [← integral_integral_swap hD]
  exact (integral_congr_ae hmean).trans (integral_zero Y ℝ)

theorem osSpatialPotential_lower {ν : Measure Y} [SFinite ν] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {D : Y → Ω → ℝ} {B : Y → ℝ}
    (hD : Integrable (Function.uncurry D) (ν.prod μ)) (hB : Integrable B ν)
    (hDB : ∀ ω x, B x ≤ D x ω) :
    ∀ᵐ ω ∂μ, (∫ x, B x ∂ν) ≤ osSpatialPotential ν D ω := by
  filter_upwards [hD.prod_left_ae] with ω hω
  exact integral_mono hB hω (hDB ω)

/-- Fubini expresses the mixed moment with a spacetime potential as an
integral of local insertions, and supplies the mixed integrability. -/
theorem osSpatialPotential_mixed_integral {ν : Measure Y} [SFinite ν] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {D : Y → Ω → ℝ} {A : Ω → ℝ}
    (hDA : Integrable (fun p : Y × Ω ↦ A p.2 * D p.1 p.2) (ν.prod μ)) :
    Integrable (fun ω ↦ A ω * osSpatialPotential ν D ω) μ ∧
    (∫ ω, A ω * osSpatialPotential ν D ω ∂μ) = ∫ x, ∫ ω, A ω * D x ω ∂μ ∂ν := by
  have hEq (ω : Ω) : A ω * osSpatialPotential ν D ω = ∫ x, A ω * D x ω ∂ν := by
    rw [integral_const_mul]
    rfl
  simp only [hEq]
  exact ⟨hDA.integral_prod_right, (integral_integral_swap hDA).symm⟩

/-- Weak-coupling failure for a source with positive mixed insertion. The
kernel-specific value of `S` is obtained by the Wick identities below. -/
theorem osSpatialPotential_negative_reflection {ν : Measure Y} [SFinite ν] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {D : Y → Ω → ℝ} {A : Ω → ℝ} {S : Y → ℝ} {L : ℝ}
    (hD : Integrable (Function.uncurry D) (ν.prod μ)) (hA : Integrable A μ)
    (hDA : Integrable (fun p : Y × Ω ↦ A p.2 * D p.1 p.2) (ν.prod μ))
    (hL : ∀ᵐ ω ∂μ, -L ≤ osSpatialPotential ν D ω) (hL0 : 0 ≤ L)
    (hnull : (∫ ω, A ω ∂μ) = 0)
    (hS : ∀ᵐ x ∂ν, (∫ ω, A ω * D x ω ∂μ) = S x)
    (hpositive : 0 < ∫ x, S x ∂ν) :
    HasDerivWithinAt (osGibbsExpectation μ (osSpatialPotential ν D) A)
      (-(∫ x, S x ∂ν)) (Ioi 0) 0 ∧
    (∀ᶠ g : ℝ in 𝓝[Ioi 0] 0, osGibbsExpectation μ (osSpatialPotential ν D) A g < 0) := by
  obtain ⟨hi, hm⟩ := osSpatialPotential_mixed_integral hDA
  have he := hm.trans (integral_congr_ae hS)
  constructor
  · rw [← he]
    exact osGibbsExpectation_hasRightDeriv_of_null hD.integral_prod_right hA hi hL hL0 hnull
  · exact osGibbsExpectation_eventually_neg_of_null hD.integral_prod_right hA hi hL hL0
      hnull (he ▸ hpositive)

/-- Fubini and the 12 quartic pairings give the exact unsubtracted
spacetime insertion, with a single switching function. -/
theorem osSpatial_raw_quartic_insertion {ν : Measure Y} [SFinite ν] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : ι → Ω → ℝ} {K : ι → ι → ℝ}
    (hW : OSWickMoments μ F K) (a b : ι) (y : Y → ι) (ζ : Y → ℝ)
    (hnull : K a b = 0)
    (hi : Integrable (fun p : Y × Ω ↦ F a p.2 * F b p.2 *
      (ζ p.1 * F (y p.1) p.2 ^ 4 / 24)) (ν.prod μ)) :
    (∫ ω, F a ω * F b ω * osSpatialPotential ν
        (fun x ω ↦ ζ x * F (y x) ω ^ 4 / 24) ω ∂μ) =
      ∫ x, ζ x * (K (y x) (y x) * (K a (y x) * K b (y x)) / 2) ∂ν := by
  rw [(osSpatialPotential_mixed_integral hi).2]
  apply integral_congr_ae
  refine Eventually.of_forall fun x ↦ ?_
  calc
    _ = ∫ ω, ζ x * (F a ω * F b ω * F (y x) ω ^ 4 / 24) ∂μ := by
      exact integral_congr_ae (Eventually.of_forall fun _ ↦ by ring)
    _ = _ := by rw [integral_const_mul, osWickRawQuartic_pair_mean hW a b (y x) hnull]

/-- Fubini and Wick ordering give the product of four cross covariances
in the centered quadratic boundary witness. -/
theorem osSpatial_wick_quartic_insertion {ν : Measure Y} [SFinite ν] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : ι → Ω → ℝ} {K : ι → ι → ℝ}
    (hW : OSWickMoments μ F K) (a b c d : ι) (y : Y → ι) (ζ : Y → ℝ)
    (hi : Integrable (fun p : Y × Ω ↦ (F a p.2 * F b p.2 - K a b) *
      (F c p.2 * F d p.2 - K c d) *
      (ζ p.1 * osWickQuartic (K (y p.1) (y p.1)) (F (y p.1) p.2))) (ν.prod μ)) :
    (∫ ω, (F a ω * F b ω - K a b) * (F c ω * F d ω - K c d) *
        osSpatialPotential ν (fun x ω ↦ ζ x *
          osWickQuartic (K (y x) (y x)) (F (y x) ω)) ω ∂μ) =
      ∫ x, ζ x * (K a (y x) * K b (y x) * K c (y x) * K d (y x)) ∂ν := by
  rw [(osSpatialPotential_mixed_integral hi).2]
  apply integral_congr_ae
  refine Eventually.of_forall fun x ↦ ?_
  calc
    _ = ∫ ω, ζ x * ((F a ω * F b ω - K a b) * (F c ω * F d ω - K c d) *
        osWickQuartic (K (y x) (y x)) (F (y x) ω)) ∂μ := by
      exact integral_congr_ae (Eventually.of_forall fun _ ↦ by ring)
    _ = _ := by rw [integral_const_mul, osWickQuartic_centeredQuadratic_mean hW a b c d (y x)]

end UV
