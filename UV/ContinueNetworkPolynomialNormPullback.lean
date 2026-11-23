import UV.ContinueNetworkPolynomialNormChart
import Mathlib.Algebra.MvPolynomial.Monad

/-! The actual numerator in an invertible selected-row chart. Each
coordinate is substituted by its real linear polynomial, keeping the
original complex coefficient ring. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace UV

variable {d : ℕ}

def directionalPolynomialComposeLinear
    (A : DirectionalMomentum d →L[ℝ] DirectionalMomentum d)
    (P : MvPolynomial (Fin d) ℂ) : MvPolynomial (Fin d) ℂ :=
  MvPolynomial.bind₁ (fun i => ∑ j,
    MvPolynomial.C ((A (EuclideanSpace.basisFun (Fin d) ℝ j) i : ℝ) : ℂ) *
      MvPolynomial.X j) P

theorem directionalNumerator_compose_linear
    (A : DirectionalMomentum d →L[ℝ] DirectionalMomentum d) (P : MvPolynomial (Fin d) ℂ)
    (k : DirectionalMomentum d) :
    directionalNumerator (directionalPolynomialComposeLinear A P) k = directionalNumerator P (A k) := by
  let q (i : Fin d) : MvPolynomial (Fin d) ℂ :=
    ∑ j, MvPolynomial.C ((A (EuclideanSpace.basisFun (Fin d) ℝ j) i : ℝ) : ℂ) *
      MvPolynomial.X j
  have he (i : Fin d) :
      MvPolynomial.aeval (fun j => (k j : ℂ)) (q i) = (A k i : ℂ) := by
    dsimp only [q]
    simp only [map_sum, map_mul, MvPolynomial.aeval_C, Algebra.algebraMap_self_apply, MvPolynomial.aeval_X]
    have h := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr k
    simp only [EuclideanSpace.basisFun_repr] at h
    let T : DirectionalMomentum d →ₗ[ℝ] ℝ :=
      (PiLp.projₗ 2 (fun _ : Fin d => ℝ) i).comp A.toLinearMap
    have hT := congrArg T h
    rw [map_sum] at hT
    simp only [map_smul, smul_eq_mul] at hT
    change (∑ j, k j * (A (EuclideanSpace.basisFun (Fin d) ℝ j) i)) = A k i at hT
    exact_mod_cast (by simpa only [mul_comm] using hT :
      (∑ j, (A (EuclideanSpace.basisFun (Fin d) ℝ j) i)*k j) = A k i)
  change MvPolynomial.aeval (fun j => (k j : ℂ)) (MvPolynomial.bind₁ q P) =
    MvPolynomial.aeval (fun j => (A k j : ℂ)) P
  rw [MvPolynomial.aeval_bind₁]
  simp only [he]

theorem directionalPolynomialComposeLinear_ne_zero
    (L : DirectionalMomentum d ≃L[ℝ] DirectionalMomentum d)
    {P : MvPolynomial (Fin d) ℂ} (hP : P ≠ 0) :
    directionalPolynomialComposeLinear L.toContinuousLinearMap P ≠ 0 := by
  obtain ⟨k,hk⟩ := directionalNumerator_exists_ne_zero hP
  intro h
  have he := directionalNumerator_compose_linear L.toContinuousLinearMap P (L.symm k)
  simp only [h, directionalNumerator, map_zero, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] at he
  exact hk he.symm

/-- A fixed physical polynomial and chart determine one fixed collection
of coefficients. Their Gaussian comparison is uniform in all positive
weights with the actual physical precision in the exponent. -/
theorem directionalGaussianIntegral_physical_norm_equivalent {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (L : DirectionalMomentum d ≃L[ℝ] DirectionalMomentum d)
    (P : MvPolynomial (Fin d) ℂ) :
    let Q := directionalPolynomialComposeLinear L.symm.toContinuousLinearMap P
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) →
      ∀ H : DirectionalMomentum d → ℝ, Measurable H →
      (∀ k, c₁*(∑ i, w i * (L k i)^2) ≤ H k) →
      (∀ k, H k ≤ c₂*(∑ i, w i * (L k i)^2)) →
        let F (k : DirectionalMomentum d) := ‖directionalNumerator P k‖ * Real.exp (-H k)
        Integrable F ∧
          C₁ * (directionalGaussianChartJacobian L * directionalGaussianCoefficientBudget w Q) ≤
            (∫ k, F k) ∧
          (∫ k, F k) ≤ C₂ * (directionalGaussianChartJacobian L * directionalGaussianCoefficientBudget w Q) := by
  let Q := directionalPolynomialComposeLinear L.symm.toContinuousLinearMap P
  obtain ⟨C₁,C₂,hC₁,hC₂,h⟩ := directionalGaussianIntegral_chart_precision_norm_equivalent hc₁ hc₂ Q
  refine ⟨C₁,C₂,hC₁,hC₂,fun w hw H hH h₁ h₂ => ?_⟩
  have h₁' (k : DirectionalMomentum d) : c₁*(∑ i, w i*(k i)^2) ≤ (H ∘ L.symm) k := by
    simpa only [L.apply_symm_apply] using h₁ (L.symm k)
  have h₂' (k : DirectionalMomentum d) : (H ∘ L.symm) k ≤ c₂*(∑ i, w i*(k i)^2) := by
    simpa only [L.apply_symm_apply] using h₂ (L.symm k)
  have hQ (k : DirectionalMomentum d) : directionalNumerator Q (L k) = directionalNumerator P k := by
    rw [show Q = directionalPolynomialComposeLinear L.symm.toContinuousLinearMap P from rfl,
      directionalNumerator_compose_linear, ContinuousLinearEquiv.coe_coe, L.symm_apply_apply]
  simpa only [hQ, Function.comp_apply, L.symm_apply_apply] using
    h w hw (H ∘ L.symm) (hH.comp L.symm.continuous.measurable) h₁' h₂' L

/-- The same bounds for the nonnegative momentum integral used by Tonelli. -/
theorem directionalGaussianLIntegral_physical_norm_equivalent {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (L : DirectionalMomentum d ≃L[ℝ] DirectionalMomentum d)
    (P : MvPolynomial (Fin d) ℂ) :
    let Q := directionalPolynomialComposeLinear L.symm.toContinuousLinearMap P
    ∃ A₁ A₂ : ℝ, 0 < A₁ ∧ 0 < A₂ ∧
      ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) →
      ∀ H : DirectionalMomentum d → ℝ, Measurable H →
      (∀ k, c₁*(∑ i, w i * (L k i)^2) ≤ H k) →
      (∀ k, H k ≤ c₂*(∑ i, w i * (L k i)^2)) →
        let F (k : DirectionalMomentum d) := ‖directionalNumerator P k‖ * Real.exp (-H k)
        ENNReal.ofReal (A₁ * directionalGaussianCoefficientBudget w Q) ≤
          (∫⁻ k, ENNReal.ofReal (F k)) ∧
        (∫⁻ k, ENNReal.ofReal (F k)) ≤ ENNReal.ofReal (A₂ * directionalGaussianCoefficientBudget w Q) := by
  obtain ⟨C₁,C₂,hC₁,hC₂,h⟩ := directionalGaussianIntegral_physical_norm_equivalent hc₁ hc₂ L P
  let J := directionalGaussianChartJacobian L
  have hJ := directionalGaussianChartJacobian_pos L
  refine ⟨C₁*J,C₂*J,mul_pos hC₁ hJ,mul_pos hC₂ hJ,fun w hw H hH h₁ h₂ => ?_⟩
  obtain ⟨hi,hlo,hhi⟩ := h w hw H hH h₁ h₂
  dsimp only
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun k =>
    mul_nonneg (norm_nonneg _) (Real.exp_pos (-H k)).le)]
  simpa only [mul_assoc] using And.intro (ENNReal.ofReal_le_ofReal hlo) (ENNReal.ofReal_le_ofReal hhi)

end UV
