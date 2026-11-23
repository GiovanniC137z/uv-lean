import UV.ContinueNetworkPolynomialNorm
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Transfer through any fixed invertible real momentum chart, as
used for the coordinates selected in an ordered Schwinger sector. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace UV

variable {d : ℕ}

/-- The positive inverse determinant of the fixed chart sending physical
momentum to the selected row coordinates. -/
def directionalGaussianChartJacobian (L : DirectionalMomentum d ≃L[ℝ] DirectionalMomentum d) : ℝ :=
  |(LinearMap.det L.toLinearEquiv.toLinearMap)⁻¹|

theorem directionalGaussianChartJacobian_pos
    (L : DirectionalMomentum d ≃L[ℝ] DirectionalMomentum d) :
    0 < directionalGaussianChartJacobian L :=
  abs_pos.mpr (inv_ne_zero L.toLinearEquiv.isUnit_det'.ne_zero)

theorem directionalGaussianChart_map
    (L : DirectionalMomentum d ≃L[ℝ] DirectionalMomentum d) :
    Measure.map L volume = ENNReal.ofReal (directionalGaussianChartJacobian L) • volume :=
  Measure.map_linearMap_addHaar_eq_smul_addHaar volume L.toLinearEquiv.isUnit_det'.ne_zero

theorem directionalGaussianChart_integral
    (L : DirectionalMomentum d ≃L[ℝ] DirectionalMomentum d)
    {F : DirectionalMomentum d → ℝ} (hF : Measurable F) :
    (∫ k, F (L k)) = directionalGaussianChartJacobian L * ∫ x, F x := by
  rw [← integral_map L.continuous.measurable.aemeasurable hF.aestronglyMeasurable,
    directionalGaussianChart_map, integral_smul_measure,
    ENNReal.toReal_ofReal (directionalGaussianChartJacobian_pos L).le, smul_eq_mul]

theorem directionalGaussianChart_integrable
    (L : DirectionalMomentum d ≃L[ℝ] DirectionalMomentum d)
    {F : DirectionalMomentum d → ℝ} (hF : Measurable F) :
    Integrable (fun k => F (L k)) ↔ Integrable F := by
  change Integrable (F ∘ L) ↔ Integrable F
  rw [← integrable_map_measure hF.aestronglyMeasurable L.continuous.measurable.aemeasurable,
    directionalGaussianChart_map]
  exact integrable_smul_measure ((ENNReal.ofReal_pos.mpr (directionalGaussianChartJacobian_pos L)).ne')
    ENNReal.ofReal_ne_top

/-- The two-sided bound for the physical integral after choosing a fixed
invertible chart. The precision is supplied in the selected coordinates.
Its exponent and the polynomial are composed with the same chart. -/
theorem directionalGaussianIntegral_chart_precision_norm_equivalent {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (P : MvPolynomial (Fin d) ℂ) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) →
      ∀ H : DirectionalMomentum d → ℝ, Measurable H →
      (∀ k, c₁*(∑ i, w i * (k i)^2) ≤ H k) →
      (∀ k, H k ≤ c₂*(∑ i, w i * (k i)^2)) →
      ∀ L : DirectionalMomentum d ≃L[ℝ] DirectionalMomentum d,
        let F (k : DirectionalMomentum d) := ‖directionalNumerator P (L k)‖ * Real.exp (-H (L k))
        Integrable F ∧
          C₁ * (directionalGaussianChartJacobian L * directionalGaussianCoefficientBudget w P) ≤
            (∫ k, F k) ∧
          (∫ k, F k) ≤ C₂ * (directionalGaussianChartJacobian L * directionalGaussianCoefficientBudget w P) := by
  obtain ⟨C₁,C₂,hC₁,hC₂,h⟩ := directionalGaussianIntegral_precision_norm_equivalent hc₁ hc₂ P
  refine ⟨C₁,C₂,hC₁,hC₂,fun w hw H hH h₁ h₂ L => ?_⟩
  let F (k : DirectionalMomentum d) := ‖directionalNumerator P k‖ * Real.exp (-H k)
  have hF : Measurable F :=
    (directionalNumerator_continuous P).norm.measurable.mul
      (Real.continuous_exp.measurable.comp hH.neg)
  obtain ⟨hi,hlo,hhi⟩ := h w hw H hH h₁ h₂
  have hL := (directionalGaussianChartJacobian_pos L).le
  refine ⟨(directionalGaussianChart_integrable L hF).2 hi, ?_⟩
  change _ ≤ (∫ k, F (L k)) ∧ (∫ k, F (L k)) ≤ _
  rw [directionalGaussianChart_integral L hF]
  constructor
  · simpa only [mul_left_comm C₁ (directionalGaussianChartJacobian L)]
      using mul_le_mul_of_nonneg_left hlo hL
  · simpa only [mul_left_comm C₂ (directionalGaussianChartJacobian L)]
      using mul_le_mul_of_nonneg_left hhi hL

end UV
