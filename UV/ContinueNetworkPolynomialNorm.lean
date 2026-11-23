import UV.ContinueNetworkPolynomialNormCompact
import UV.ContinueNetworkPolynomialNormScaling

/-! The coefficient factor in the directional theorem. It applies
uniformly as the positive anisotropic weights approach zero in a
Schwinger sector. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace UV

variable {d : ℕ} {ι : Type*} [Fintype ι]

def directionalGaussianCoefficientBudget (w : Fin d → ℝ)
    (P : MvPolynomial (Fin d) ℂ) : ℝ :=
  (∏ i, (w i)^(-(1/2 : ℝ))) *
    ∑ β ∈ P.support, ‖P.coeff β‖ * ∏ i, (w i)^(-(β i : ℝ)/2)

/-- For fixed Gaussian rescaling and fixed distinct monomials, the
constants in the coefficient comparison work for every positive weight
vector and every complex coefficient vector. -/
theorem directionalGaussianIntegral_diagonal_norm_equivalent {c : ℝ} (hc : 0 < c)
    (γ : ι ↪ (Fin d →₀ ℕ)) :
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧ ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) →
      ∀ a : ι → ℂ,
        L * (directionalGaussianJacobian w *
          ∑ j, ‖a j‖ * directionalGaussianCoefficientScale w (γ j)) ≤
          directionalGaussianIntegral c w (directionalPolynomialOfTerms γ a) ∧
        directionalGaussianIntegral c w (directionalPolynomialOfTerms γ a) ≤
          U * (directionalGaussianJacobian w *
            ∑ j, ‖a j‖ * directionalGaussianCoefficientScale w (γ j)) := by
  obtain ⟨L,U,hL,hU,h⟩ := directionalGaussianIntegral_terms_norm_equivalent hc
    (w := fun _ => 1) (fun _ => zero_lt_one) γ
  refine ⟨L,U,hL,hU,fun w hw a => ?_⟩
  let b (j : ι) := a j * (directionalGaussianCoefficientScale w (γ j) : ℂ)
  have hb : directionalCoefficientL1 b =
      ∑ j, ‖a j‖ * directionalGaussianCoefficientScale w (γ j) := by
    unfold directionalCoefficientL1
    apply Finset.sum_congr rfl
    intro j _
    simp only [b, norm_mul, Complex.norm_real, Real.norm_of_nonneg
      (directionalGaussianCoefficientScale_pos hw (γ j)).le]
  have hJ := (directionalGaussianJacobian_pos hw).le
  rw [directionalGaussianIntegral_diagonal_change c hw, ← hb]
  simpa only [mul_left_comm L (directionalGaussianJacobian w), mul_left_comm U (directionalGaussianJacobian w)]
    using And.intro (mul_le_mul_of_nonneg_left (h b).1 hJ) (mul_le_mul_of_nonneg_left (h b).2 hJ)

/-- The manuscript's actual coefficient sum over surviving monomials,
with exponents (-1/2) and (-gamma_i/2) in the positive weights. -/
theorem directionalGaussianIntegral_polynomial_norm_equivalent {c : ℝ} (hc : 0 < c)
    (P : MvPolynomial (Fin d) ℂ) :
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧ ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) →
      L * directionalGaussianCoefficientBudget w P ≤ directionalGaussianIntegral c w P ∧
      directionalGaussianIntegral c w P ≤ U * directionalGaussianCoefficientBudget w P := by
  classical
  let γ : P.support ↪ (Fin d →₀ ℕ) := ⟨Subtype.val, Subtype.val_injective⟩
  obtain ⟨L,U,hL,hU,h⟩ := directionalGaussianIntegral_diagonal_norm_equivalent hc γ
  refine ⟨L,U,hL,hU,fun w hw => ?_⟩
  have hP : directionalPolynomialOfTerms γ (fun j => P.coeff (γ j)) = P :=
    directionalPolynomialOfTerms_support P
  have hB : (∑ j : P.support, ‖P.coeff (γ j)‖ * directionalGaussianCoefficientScale w (γ j)) =
      ∑ β ∈ P.support, ‖P.coeff β‖ * ∏ i, (w i)^(-(β i : ℝ)/2) := by
    simp_rw [directionalGaussianCoefficientScale_rpow hw]
    exact P.support.sum_coe_sort (fun β => ‖P.coeff β‖ * ∏ i, (w i)^(-(β i : ℝ)/2))
  have h' := h w hw (fun j => P.coeff (γ j))
  rw [hP, hB, directionalGaussianJacobian_rpow hw] at h'
  exact h'

theorem directionalGaussianIntegrand_polynomial_integrable {c : ℝ} (hc : 0 < c)
    {w : Fin d → ℝ} (hw : ∀ i, 0 < w i) (P : MvPolynomial (Fin d) ℂ) :
    Integrable (directionalGaussianIntegrand c w P) := by
  classical
  have h := directionalGaussianIntegrand_terms_integrable hc hw
    (fun j : P.support => (j : Fin d →₀ ℕ)) (fun j => P.coeff j)
  rwa [directionalPolynomialOfTerms_support] at h

/-- A measurable precision uniformly sandwiched between two positive
multiples of the diagonal precision has the same coefficient budget.
This passes the exact diagonal norm estimate to the Gaussian selected
by a fixed ordered Schwinger sector. -/
theorem directionalGaussianIntegral_precision_norm_equivalent {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (P : MvPolynomial (Fin d) ℂ) :
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧
      ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) →
      ∀ H : DirectionalMomentum d → ℝ, Measurable H →
      (∀ k, c₁*(∑ i, w i * (k i)^2) ≤ H k) →
      (∀ k, H k ≤ c₂*(∑ i, w i * (k i)^2)) →
      let F (k : DirectionalMomentum d) := ‖directionalNumerator P k‖ * Real.exp (-H k)
      Integrable F ∧
        L * directionalGaussianCoefficientBudget w P ≤ (∫ k, F k) ∧
        (∫ k, F k) ≤ U * directionalGaussianCoefficientBudget w P := by
  obtain ⟨_,U,_,hU,hu⟩ := directionalGaussianIntegral_polynomial_norm_equivalent hc₁ P
  obtain ⟨L,_,hL,_,hl⟩ := directionalGaussianIntegral_polynomial_norm_equivalent hc₂ P
  refine ⟨L,U,hL,hU,fun w hw H hH h₁ h₂ => ?_⟩
  let F (k : DirectionalMomentum d) := ‖directionalNumerator P k‖ * Real.exp (-H k)
  have hF0 (k : DirectionalMomentum d) : 0 ≤ F k :=
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hF₁ (k : DirectionalMomentum d) : F k ≤ directionalGaussianIntegrand c₁ w P k := by
    unfold F directionalGaussianIntegrand directionalGaussianWeight
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [h₁ k])) (norm_nonneg _)
  have hF₂ (k : DirectionalMomentum d) : directionalGaussianIntegrand c₂ w P k ≤ F k := by
    unfold F directionalGaussianIntegrand directionalGaussianWeight
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [h₂ k])) (norm_nonneg _)
  have hi₁ := directionalGaussianIntegrand_polynomial_integrable hc₁ hw P
  have hi₂ := directionalGaussianIntegrand_polynomial_integrable hc₂ hw P
  have hiF : Integrable F := by
    apply hi₁.mono' ((directionalNumerator_continuous P).norm.measurable.mul
      (Real.continuous_exp.measurable.comp hH.neg)).aestronglyMeasurable
    refine ae_of_all _ fun k => ?_
    change ‖F k‖ ≤ directionalGaussianIntegrand c₁ w P k
    rw [Real.norm_of_nonneg (hF0 k)]
    exact hF₁ k
  exact ⟨hiF, (hl w hw).1.trans (integral_mono hi₂ hiF hF₂),
    (integral_mono hiF hi₁ hF₁).trans (hu w hw).2⟩

end UV
