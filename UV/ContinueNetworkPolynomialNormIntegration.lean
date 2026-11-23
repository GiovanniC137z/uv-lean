import UV.ContinueNetworkPolynomialNormWeights

/-! Integrating the nonnegative Schwinger budget over arbitrary positive
parameter sectors. The finite sum keeps exactly the surviving monomials,
with their fixed absolute complex coefficients and the fixed Jacobian. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace UV

variable {d : ℕ} {E X : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace X]

def directionalGaussianSchwingerMonomial (label : Fin d → Option E) (ν : E → ℝ)
    (β : Fin d →₀ ℕ) (t : E → ℝ) : ℝ≥0∞ :=
  ∏ e, ENNReal.ofReal ((t e)^(ν e-(directionalGaussianEdgeCost label β e : ℝ)/2-1))

private theorem directionalGaussianSchwingerMonomial_measurable
    (label : Fin d → Option E) (ν : E → ℝ) (β : Fin d →₀ ℕ)
    {t : X → E → ℝ} (ht : ∀ e, Measurable (fun z => t z e)) :
    Measurable (fun z => directionalGaussianSchwingerMonomial label ν β (t z)) := by
  unfold directionalGaussianSchwingerMonomial
  exact Finset.measurable_prod _ (fun e _ => ((ht e).pow_const _).ennreal_ofReal)

/-- Exact Tonelli reduction of the complete diagonal comparison budget.
A fixed nonnegative multiplier may include the selected-coordinate
Lebesgue Jacobian and the comparison constants. -/
theorem directionalGaussianCoefficientBudget_schwinger_lintegral
    (μ : Measure X) (label : Fin d → Option E) (ν : E → ℝ)
    (P : MvPolynomial (Fin d) ℂ) {A : ℝ} (hA : 0 ≤ A)
    {t : X → E → ℝ} (ht : ∀ e, Measurable (fun z => t z e))
    (ht₀ : ∀ᵐ z ∂μ, ∀ e, 0 < t z e) :
    (∫⁻ z, (∏ e, ENNReal.ofReal ((t z e)^(ν e-1))) *
        ENNReal.ofReal (A * directionalGaussianCoefficientBudget
          (directionalGaussianRowWeights label (t z)) P) ∂μ) =
      ∑ β ∈ P.support, ENNReal.ofReal (A*‖P.coeff β‖) *
        ∫⁻ z, directionalGaussianSchwingerMonomial label ν β (t z) ∂μ := by
  let H (β : Fin d →₀ ℕ) (z : X) := directionalGaussianSchwingerMonomial label ν β (t z)
  have hH (β : Fin d →₀ ℕ) : Measurable (H β) :=
    directionalGaussianSchwingerMonomial_measurable label ν β ht
  change _ = ∑ β ∈ P.support, ENNReal.ofReal (A*‖P.coeff β‖) * ∫⁻ z, H β z ∂μ
  simp_rw [← lintegral_const_mul _ (hH _)]
  rw [← lintegral_finset_sum _ (fun β _ => measurable_const.mul (hH β))]
  apply lintegral_congr_ae
  filter_upwards [ht₀] with z hz
  have hpow (e : E) : 0 ≤ (t z e)^(ν e-1) := Real.rpow_nonneg (hz e).le _
  rw [← ENNReal.ofReal_prod_of_nonneg (fun e _ => hpow e),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg (fun e _ => hpow e)), mul_left_comm,
    directionalGaussianCoefficientBudget_schwinger label hz, Finset.mul_sum,
    ENNReal.ofReal_sum_of_nonneg (fun β _ => mul_nonneg hA
      (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun e _ => Real.rpow_nonneg (hz e).le _))))]
  apply Finset.sum_congr rfl
  intro β _
  unfold H directionalGaussianSchwingerMonomial
  rw [← ENNReal.ofReal_prod_of_nonneg (fun e _ => Real.rpow_nonneg (hz e).le _),
    ← ENNReal.ofReal_mul (mul_nonneg hA (norm_nonneg _)), mul_assoc]

/-- Finiteness of the integrated budget tests exactly the surviving
monomials, including their full multiscale Schwinger powers. -/
theorem directionalGaussianCoefficientBudget_schwinger_finite_iff
    (μ : Measure X) (label : Fin d → Option E) (ν : E → ℝ)
    (P : MvPolynomial (Fin d) ℂ) {A : ℝ} (hA : 0 < A)
    {t : X → E → ℝ} (ht : ∀ e, Measurable (fun z => t z e))
    (ht₀ : ∀ᵐ z ∂μ, ∀ e, 0 < t z e) :
    (∫⁻ z, (∏ e, ENNReal.ofReal ((t z e)^(ν e-1))) *
        ENNReal.ofReal (A * directionalGaussianCoefficientBudget
          (directionalGaussianRowWeights label (t z)) P) ∂μ) < ∞ ↔
      ∀ β ∈ P.support,
        (∫⁻ z, directionalGaussianSchwingerMonomial label ν β (t z) ∂μ) < ∞ := by
  rw [directionalGaussianCoefficientBudget_schwinger_lintegral μ label ν P hA.le ht ht₀,
    ENNReal.sum_lt_top]
  apply forall₂_congr
  intro β hβ
  have hcoeff := norm_pos_iff.mpr (MvPolynomial.mem_support_iff.mp hβ)
  have hpositive := ENNReal.ofReal_pos.mpr (mul_pos hA hcoeff)
  rw [ENNReal.mul_lt_top_iff]
  simp [ENNReal.ofReal_lt_top, hpositive.ne']
  intro hz
  rw [hz]
  exact ENNReal.zero_lt_top

end UV
