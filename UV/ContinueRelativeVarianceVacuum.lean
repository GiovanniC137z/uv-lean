import UV.ContinueRelativeVariance

/-! Ordinary common-vacuum normalization at fourth order on the transverse ray. -/

noncomputable section

namespace UV.RelativeSoft

open MeasureTheory ProbabilityTheory

/-- With the given conditional Wick contractions, division by the averaged
vacuum weight and inversion of the averaged propagator give the common-depth
fourth coefficient. The vacuum weight has constant term one and charge-square
coefficient v, so its normalization contributes one subtraction. -/
theorem softFourth_from_common_vacuum {μ : Measure Depth} [IsProbabilityMeasure μ]
    {u v k : Depth → ℝ} (hu : Integrable u μ) (hv : MemLp v 2 μ) (hk : MemLp k 2 μ)
    {t : ℝ} (ht : t ≠ 0) :
    let c := (t ^ 2)⁻¹
    let g₂ := ∫ r, c ^ 2 * k r ∂μ
    let g₄ := (∫ r, c ^ 2 * u r + c ^ 3 * k r ^ 2 + v r * (c ^ 2 * k r) ∂μ) -
      (∫ r, v r ∂μ) * g₂
    g₄ / c ^ 2 - g₂ ^ 2 / c ^ 3 = softFourthCoefficient μ u v k t := by
  let c := (t ^ 2)⁻¹
  let g₂ := ∫ r, c ^ 2 * k r ∂μ
  let g₄ := (∫ r, c ^ 2 * u r + c ^ 3 * k r ^ 2 + v r * (c ^ 2 * k r) ∂μ) -
    (∫ r, v r ∂μ) * g₂
  have hg₂ : g₂ = c ^ 2 * (∫ r, k r ∂μ) := integral_const_mul _ _
  have hg₄ : g₄ = c ^ 2 *
      ((∫ r, u r ∂μ) + covariance v k μ + (∫ r, k r ^ 2 ∂μ) / t ^ 2) := by
    have hU := hu.const_mul (c ^ 2)
    have hK := ((memLp_two_iff_integrable_sq hk.aestronglyMeasurable).mp hk).const_mul (c ^ 3)
    have hV (r : Depth) : v r * (c ^ 2 * k r) = c ^ 2 * (v * k) r := by
      simp only [Pi.mul_apply]
      ring
    dsimp only [g₄]
    simp_rw [hV]
    have hi := integral_add (hU.add hK) ((hv.integrable_mul hk).const_mul (c ^ 2))
    simp only [Pi.add_apply] at hi
    rw [hg₂, hi, integral_add hU hK, covariance_eq_sub hv hk]
    simp only [integral_const_mul, div_eq_mul_inv]
    change _ = c ^ 2 * ((_ + _) + _ * c)
    ring
  exact softFourth_from_inverse_coefficients hk ht hg₂ hg₄

end UV.RelativeSoft
