import UV.ContinueNetworkPolynomialNormTerms
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Exact positive diagonal rescaling of the absolute Gaussian polynomial
integral, including the Lebesgue determinant. -/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace UV

variable {d : ℕ} {ι : Type*} [Fintype ι]

def directionalGaussianJacobian (w : Fin d → ℝ) : ℝ :=
  ∏ i, (Real.sqrt (w i))⁻¹

def directionalGaussianCoefficientScale (w : Fin d → ℝ) (β : Fin d →₀ ℕ) : ℝ :=
  ∏ i, ((Real.sqrt (w i))⁻¹)^(β i)

theorem directionalGaussianJacobian_pos {w : Fin d → ℝ} (hw : ∀ i, 0 < w i) :
    0 < directionalGaussianJacobian w :=
  Finset.prod_pos fun i _ => inv_pos.mpr (Real.sqrt_pos.mpr (hw i))

theorem directionalGaussianCoefficientScale_pos {w : Fin d → ℝ} (hw : ∀ i, 0 < w i)
    (β : Fin d →₀ ℕ) : 0 < directionalGaussianCoefficientScale w β :=
  Finset.prod_pos fun i _ => pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr (hw i))) _

private def directionalGaussianDilation (w : Fin d → ℝ) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
  Matrix.toLin' (Matrix.diagonal fun i => Real.sqrt (w i))

private theorem directionalGaussianDilation_apply (w : Fin d → ℝ) (x : Fin d → ℝ) (i : Fin d) :
    directionalGaussianDilation w x i = Real.sqrt (w i) * x i := by
  rw [directionalGaussianDilation, Matrix.diagonal_toLin']
  rfl

private theorem directionalGaussianDilation_map {w : Fin d → ℝ} (hw : ∀ i, 0 < w i) :
    Measure.map (directionalGaussianDilation w) volume =
      ENNReal.ofReal (directionalGaussianJacobian w) • volume := by
  have hp : 0 < ∏ i, Real.sqrt (w i) :=
    Finset.prod_pos fun i _ => Real.sqrt_pos.mpr (hw i)
  have hdet : 0 < (Matrix.diagonal fun i => Real.sqrt (w i)).det := by
    rwa [Matrix.det_diagonal]
  rw [directionalGaussianDilation, Real.map_matrix_volume_pi_eq_smul_volume_pi hdet.ne',
    Matrix.det_diagonal, abs_of_pos (inv_pos.mpr hp), directionalGaussianJacobian,
    Finset.prod_inv_distrib]

private theorem directionalGaussianDilation_polynomial {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) (γ : ι → (Fin d →₀ ℕ)) (a : ι → ℂ) (x : Fin d → ℝ) :
    directionalNumerator (directionalPolynomialOfTerms γ
      (fun j => a j * (directionalGaussianCoefficientScale w (γ j) : ℂ)))
      (WithLp.toLp 2 (directionalGaussianDilation w x)) =
    directionalNumerator (directionalPolynomialOfTerms γ a) (WithLp.toLp 2 x) := by
  rw [directionalPolynomialOfTerms_eval, directionalPolynomialOfTerms_eval]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc]
  congr 1
  rw [directionalGaussianCoefficientScale, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  change ((↑((Real.sqrt (w i))⁻¹ ^ (γ j i)) : ℂ) *
    (directionalGaussianDilation w x i : ℂ)^(γ j i)) = (x i : ℂ)^(γ j i)
  rw [directionalGaussianDilation_apply]
  norm_cast
  rw [← mul_pow, ← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.mpr (hw i)).ne', one_mul]

private theorem directionalGaussianDilation_weight {c : ℝ} {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) (x : Fin d → ℝ) :
    directionalGaussianWeight c (fun _ => 1) (WithLp.toLp 2 (directionalGaussianDilation w x)) =
      directionalGaussianWeight c w (WithLp.toLp 2 x) := by
  unfold directionalGaussianWeight
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  change 1 * (directionalGaussianDilation w x i)^2 = w i * (x i)^2
  rw [directionalGaussianDilation_apply, one_mul, mul_pow, Real.sq_sqrt (hw i).le]

/-- The exact identity under (z_i=sqrt{w_i},x_i), with the full
complex polynomial evaluated before taking its absolute value. -/
theorem directionalGaussianIntegral_diagonal_change (c : ℝ) {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) (γ : ι → (Fin d →₀ ℕ)) (a : ι → ℂ) :
    directionalGaussianIntegral c w (directionalPolynomialOfTerms γ a) =
      directionalGaussianJacobian w *
        directionalGaussianIntegral c (fun _ => 1) (directionalPolynomialOfTerms γ
          (fun j => a j * (directionalGaussianCoefficientScale w (γ j) : ℂ))) := by
  let P := directionalPolynomialOfTerms γ a
  let Q := directionalPolynomialOfTerms γ
    (fun j => a j * (directionalGaussianCoefficientScale w (γ j) : ℂ))
  let F (x : Fin d → ℝ) := directionalGaussianIntegrand c (fun _ => 1) Q (WithLp.toLp 2 x)
  have hA : Measurable (directionalGaussianDilation w) :=
    (LinearMap.continuous_on_pi (directionalGaussianDilation w)).measurable
  have hF : Measurable F :=
    (directionalGaussianIntegrand_continuous c (fun _ => 1) Q).measurable.comp
      (EuclideanSpace.measurableEquiv (Fin d)).symm.measurable
  have he := EuclideanSpace.volume_preserving_measurableEquiv (Fin d)
  have h₁ := he.symm.integral_comp (EuclideanSpace.measurableEquiv (Fin d)).symm.measurableEmbedding
    (directionalGaussianIntegrand c w P)
  have h₂ := he.symm.integral_comp (EuclideanSpace.measurableEquiv (Fin d)).symm.measurableEmbedding
    (directionalGaussianIntegrand c (fun _ => 1) Q)
  change (∫ x : Fin d → ℝ, directionalGaussianIntegrand c w P (WithLp.toLp 2 x)) =
    directionalGaussianIntegral c w P at h₁
  change (∫ x : Fin d → ℝ, F x) = directionalGaussianIntegral c (fun _ => 1) Q at h₂
  change directionalGaussianIntegral c w P =
    directionalGaussianJacobian w * directionalGaussianIntegral c (fun _ => 1) Q
  rw [← h₁, ← h₂]
  calc
    _ = ∫ x, F (directionalGaussianDilation w x) := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [F, directionalGaussianIntegrand, P, Q]
      rw [directionalGaussianDilation_polynomial hw, directionalGaussianDilation_weight hw]
    _ = ∫ x, F x ∂Measure.map (directionalGaussianDilation w) volume :=
      (integral_map hA.aemeasurable hF.aestronglyMeasurable).symm
    _ = _ := by
      rw [directionalGaussianDilation_map hw, integral_smul_measure,
        ENNReal.toReal_ofReal (directionalGaussianJacobian_pos hw).le, smul_eq_mul]

theorem directionalGaussianJacobian_rpow {w : Fin d → ℝ} (hw : ∀ i, 0 < w i) :
    directionalGaussianJacobian w = ∏ i, (w i)^(-(1/2 : ℝ)) := by
  unfold directionalGaussianJacobian
  apply Finset.prod_congr rfl
  intro i _
  rw [Real.sqrt_eq_rpow, Real.rpow_neg (hw i).le]

theorem directionalGaussianCoefficientScale_rpow {w : Fin d → ℝ} (hw : ∀ i, 0 < w i)
    (β : Fin d →₀ ℕ) :
    directionalGaussianCoefficientScale w β = ∏ i, (w i)^(-(β i : ℝ)/2) := by
  unfold directionalGaussianCoefficientScale
  apply Finset.prod_congr rfl
  intro i _
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (hw i).le, ← Real.rpow_mul_natCast (hw i).le]
  congr 1
  ring

end UV
