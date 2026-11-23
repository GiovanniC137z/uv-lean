import UV.ContinueRelativeSoftDepth
import UV.ContinueRelativeVarianceLimit

/-! The variance obstruction for the explicit radial continuum coefficient. -/

noncomputable section

namespace UV.RelativeSoft

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

/-- The manuscript's positive Gaussian width, with σ² = κ r^α. -/
def softDepthWidth (κ α : ℝ) (r : Depth) : ℝ :=
  Real.sqrt (softDepthWidthSq κ α r)

theorem softDepthWidth_sq {κ α : ℝ} (hκ : 0 < κ) (r : Depth) :
    softDepthWidth κ α r ^ 2 = softDepthWidthSq κ α r :=
  Real.sq_sqrt (softDepthWidthSq_pos hκ r).le

/-- The fixed-depth continuum coefficient with the optional squared positive
normalization. Charge one extracts the pure quadratic charge coefficient. -/
def commonDepthContinuumCoeff (κ α m z : ℝ) (r : Depth) : ℝ :=
  z ^ 2 * relativeSoftResponse 1 m (softDepthWidth κ α r)

/-- At every fixed mass the continuum coefficient has the same negative
small-width amplitude, times the optional squared normalization. -/
theorem commonDepthContinuumCoeff_tip {κ α : ℝ} (hκ : 0 < κ) (hα : 0 < α) (m z : ℝ) :
    Tendsto (fun r => softDepthWidthSq κ α r * commonDepthContinuumCoeff κ α m z r)
      (comap (fun r : Depth => (r : ℝ)) (𝓝[>] (0 : ℝ)))
      (𝓝 ((-3 : ℝ) * z ^ 2 / (16 * Real.pi ^ 2))) := by
  let l := comap (fun r : Depth => (r : ℝ)) (𝓝[>] (0 : ℝ))
  have hσ : Tendsto (softDepthWidth κ α) l (𝓝 0) := by
    simpa [softDepthWidth] using (softDepthWidthSq_tendsto_zero (κ := κ) hα).sqrt
  have hm : Tendsto (fun r => m * softDepthWidth κ α r) l (𝓝 0) := by
    simpa using hσ.const_mul m
  have ht := (relative_soft_shape_continuous.continuousAt (x := 0)).tendsto.comp hm
  rw [relative_soft_shape_zero] at ht
  have h := ht.const_mul (z ^ 2 / (16 * Real.pi ^ 2))
  have hconst :
      z ^ 2 / (16 * Real.pi ^ 2) * (-3) = (-3 : ℝ) * z ^ 2 / (16 * Real.pi ^ 2) := by ring
  rw [hconst] at h
  apply h.congr'
  refine Eventually.of_forall fun r => ?_
  have hσsq := softDepthWidth_sq hκ (α := α) r
  have hs := (softDepthWidthSq_pos hκ (α := α) r).ne'
  change z ^ 2 / (16 * Real.pi ^ 2) * relativeSoftShape (m * softDepthWidth κ α r) =
    softDepthWidthSq κ α r * (z ^ 2 * relativeSoftResponse 1 m (softDepthWidth κ α r))
  rw [relativeSoftResponse, hσsq, one_pow]
  field_simp

section

variable {μ : Measure Depth} [IsProbabilityMeasure μ] (D : SoftVarianceData μ)

/-- The explicit radial continuum response supplies the strict part of the
common-depth obstruction for the given finite-volume coefficients. -/
theorem SoftVarianceData.commonDepthSoftVariance_explicit_positive
    (hμ : ChargesDepthTip μ) {κ α : ℝ} (hκ : 0 < κ) (hα : 0 < α)
    {m z : ℝ} (hz : z ≠ 0) (hk : D.k₀ = commonDepthContinuumCoeff κ α m z) :
    0 < (25 : ℝ) / 48 * variance D.k₀ μ := by
  apply D.commonDepthSoftVariance_positive hμ hκ hα
    (c := (-3 : ℝ) * z ^ 2 / (16 * Real.pi ^ 2))
  · exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) (sq_pos_of_ne_zero hz))
      (by positivity)
  · rw [hk]
    exact commonDepthContinuumCoeff_tip hκ hα m z

/-- The proper fourth-order response has a positive rescaled limit and is
unbounded along arbitrarily soft retained momenta, with or without tuning
the mean of the same continuum SoftVarianceData.coefficient to zero. -/
theorem SoftVarianceData.commonDepthSoftVariance_explicit_limit
    (hμ : ChargesDepthTip μ) {κ α : ℝ} (hκ : 0 < κ) (hα : 0 < α)
    {m z : ℝ} (hz : z ≠ 0) (hk : D.k₀ = commonDepthContinuumCoeff κ α m z) :
    Tendsto (fun R : ℝ => R⁻¹ ^ 2 * ∑ j, softRayWeight j * D.coefficient R j)
        atTop (𝓝 ((25 : ℝ) / 48 * variance D.k₀ μ)) ∧
      0 < (25 : ℝ) / 48 * variance D.k₀ μ ∧
      ∀ R₀ C : ℝ, ∃ R ≥ R₀, 1 ≤ R ∧ ∃ j, C < |D.coefficient R j| := by
  have hpos := D.commonDepthSoftVariance_explicit_positive hμ hκ hα hz hk
  refine ⟨D.commonDepthSoftVariance_limit, hpos, D.commonDepthSoftVariance_unbounded ?_⟩
  exact pos_of_mul_pos_right hpos (by norm_num)

end

end UV.RelativeSoft
