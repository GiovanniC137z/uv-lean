import UV.ContinueNetworkDirectional
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! The finite monomial expansion and its Gaussian majorants in the
directional power-counting proof. The coefficients and the sum remain
complex until taking the norm of the evaluated polynomial. -/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators

namespace UV

variable {d : ℕ} {ι : Type*} [Fintype ι]

def directionalPolynomialOfTerms (γ : ι → (Fin d →₀ ℕ)) (a : ι → ℂ) :
    MvPolynomial (Fin d) ℂ :=
  ∑ j, MvPolynomial.monomial (γ j) (a j)

def directionalGaussianWeight (c : ℝ) (w : Fin d → ℝ) (k : DirectionalMomentum d) : ℝ :=
  Real.exp (-c * ∑ i, w i * (k i)^2)

def directionalGaussianIntegrand (c : ℝ) (w : Fin d → ℝ) (P : MvPolynomial (Fin d) ℂ)
    (k : DirectionalMomentum d) : ℝ :=
  ‖directionalNumerator P k‖ * directionalGaussianWeight c w k

def directionalGaussianIntegral (c : ℝ) (w : Fin d → ℝ)
    (P : MvPolynomial (Fin d) ℂ) : ℝ :=
  ∫ k, directionalGaussianIntegrand c w P k

def directionalGaussianMonomial (c : ℝ) (w : Fin d → ℝ) (β : Fin d →₀ ℕ)
    (k : DirectionalMomentum d) : ℝ :=
  (∏ i, |k i|^(β i)) * directionalGaussianWeight c w k

theorem directionalPolynomialOfTerms_coeff (γ : ι ↪ (Fin d →₀ ℕ)) (a : ι → ℂ) (j : ι) :
    (directionalPolynomialOfTerms γ a).coeff (γ j) = a j := by
  classical
  rw [directionalPolynomialOfTerms, MvPolynomial.coeff_sum, Finset.sum_eq_single j]
  · simp
  · intro j' _ hj
    simp [MvPolynomial.coeff_monomial, γ.injective.ne hj]
  · simp

theorem directionalPolynomialOfTerms_eval (γ : ι → (Fin d →₀ ℕ)) (a : ι → ℂ)
    (k : DirectionalMomentum d) :
    directionalNumerator (directionalPolynomialOfTerms γ a) k =
    ∑ j, a j * ∏ i, (k i : ℂ)^(γ j i) := by
  classical
  rw [directionalNumerator, directionalPolynomialOfTerms, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype]
  simp

theorem directionalGaussianWeight_continuous (c : ℝ) (w : Fin d → ℝ) :
    Continuous (directionalGaussianWeight c w) := by
  unfold directionalGaussianWeight
  exact Real.continuous_exp.comp (continuous_const.mul (continuous_finset_sum _ (fun i _ =>
    continuous_const.mul ((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).pow 2))))

theorem directionalGaussianIntegrand_continuous (c : ℝ) (w : Fin d → ℝ)
    (P : MvPolynomial (Fin d) ℂ) :
    Continuous (directionalGaussianIntegrand c w P) :=
  (directionalNumerator_continuous P).norm.mul (directionalGaussianWeight_continuous c w)

theorem directionalGaussianIntegrand_nonneg (c : ℝ) (w : Fin d → ℝ)
    (P : MvPolynomial (Fin d) ℂ) (k : DirectionalMomentum d) :
    0 ≤ directionalGaussianIntegrand c w P k :=
  mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

theorem directionalGaussianMonomial_nonneg (c : ℝ) (w : Fin d → ℝ)
    (β : Fin d →₀ ℕ) (k : DirectionalMomentum d) :
    0 ≤ directionalGaussianMonomial c w β k := by
  unfold directionalGaussianMonomial directionalGaussianWeight
  positivity

theorem directionalGaussianMonomial_integrable {c : ℝ} (hc : 0 < c)
    {w : Fin d → ℝ} (hw : ∀ i, 0 < w i) (β : Fin d →₀ ℕ) :
    Integrable (directionalGaussianMonomial c w β) := by
  have he := EuclideanSpace.volume_preserving_measurableEquiv (Fin d)
  rw [← he.symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  have h1 (i : Fin d) : Integrable (fun x : ℝ => |x|^(β i) * Real.exp (-(c*w i)*x^2)) := by
    have hi := (integrable_rpow_mul_exp_neg_mul_sq (mul_pos hc (hw i))
      (s := (β i : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) (β i)])).norm
    simpa only [Real.rpow_natCast, norm_mul, Real.norm_eq_abs, abs_pow,
      abs_of_pos (Real.exp_pos _)] using hi
  convert Integrable.fintype_prod h1 using 1
  funext k
  change (∏ i, |k i|^(β i)) * Real.exp (-c * ∑ i, w i * (k i)^2) =
    ∏ i, |k i|^(β i) * Real.exp (-(c*w i)*(k i)^2)
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem directionalGaussianIntegrand_term_bound (c : ℝ) (w : Fin d → ℝ)
    (γ : ι → (Fin d →₀ ℕ)) (a : ι → ℂ) (k : DirectionalMomentum d) :
    directionalGaussianIntegrand c w (directionalPolynomialOfTerms γ a) k ≤
      ∑ j, ‖a j‖ * directionalGaussianMonomial c w (γ j) k := by
  rw [directionalGaussianIntegrand, directionalPolynomialOfTerms_eval]
  refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (Real.exp_pos _).le).trans_eq ?_
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [norm_mul, norm_prod, directionalGaussianMonomial, ← mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro i _
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]

theorem directionalGaussianIntegrand_terms_integrable {c : ℝ} (hc : 0 < c)
    {w : Fin d → ℝ} (hw : ∀ i, 0 < w i) (γ : ι → (Fin d →₀ ℕ)) (a : ι → ℂ) :
    Integrable (directionalGaussianIntegrand c w (directionalPolynomialOfTerms γ a)) := by
  have hi : Integrable (fun k => ∑ j, ‖a j‖ * directionalGaussianMonomial c w (γ j) k) :=
    integrable_finset_sum _ (fun j _ => (directionalGaussianMonomial_integrable hc hw (γ j)).const_mul _)
  apply hi.mono' (directionalGaussianIntegrand_continuous c w _).aestronglyMeasurable
  filter_upwards with k
  rw [Real.norm_of_nonneg (directionalGaussianIntegrand_nonneg c w _ _)]
  exact directionalGaussianIntegrand_term_bound c w γ a k

theorem directionalGaussianIntegral_term_bound {c : ℝ} (hc : 0 < c)
    {w : Fin d → ℝ} (hw : ∀ i, 0 < w i) (γ : ι → (Fin d →₀ ℕ)) (a : ι → ℂ) :
    directionalGaussianIntegral c w (directionalPolynomialOfTerms γ a) ≤
      ∑ j, ‖a j‖ * ∫ k, directionalGaussianMonomial c w (γ j) k := by
  have hj (j : ι) := (directionalGaussianMonomial_integrable hc hw (γ j)).const_mul ‖a j‖
  have hi : Integrable (fun k => ∑ j, ‖a j‖ * directionalGaussianMonomial c w (γ j) k) :=
    integrable_finset_sum _ (fun j _ => hj j)
  calc
    _ ≤ ∫ k, ∑ j, ‖a j‖ * directionalGaussianMonomial c w (γ j) k :=
      integral_mono (directionalGaussianIntegrand_terms_integrable hc hw γ a) hi
        (directionalGaussianIntegrand_term_bound c w γ a)
    _ = _ := by rw [integral_finset_sum _ (fun j _ => hj j)]; simp only [integral_const_mul]

theorem directionalGaussianIntegral_terms_pos {c : ℝ} (hc : 0 < c)
    {w : Fin d → ℝ} (hw : ∀ i, 0 < w i) (γ : ι ↪ (Fin d →₀ ℕ)) {a : ι → ℂ}
    (ha : a ≠ 0) :
    0 < directionalGaussianIntegral c w (directionalPolynomialOfTerms γ a) := by
  obtain ⟨j,hj⟩ : ∃ j, a j ≠ 0 := by
    contrapose! ha
    funext j
    exact ha j
  have hp : directionalPolynomialOfTerms γ a ≠ 0 := by
    intro h
    apply hj
    rw [← directionalPolynomialOfTerms_coeff γ a j, h, MvPolynomial.coeff_zero]
  obtain ⟨k,hk⟩ := directionalNumerator_exists_ne_zero hp
  exact integral_pos_of_integrable_nonneg_nonzero (directionalGaussianIntegrand_continuous c w _)
    (directionalGaussianIntegrand_terms_integrable hc hw γ a)
    (directionalGaussianIntegrand_nonneg c w _)
    (mul_ne_zero (norm_ne_zero_iff.mpr hk) (Real.exp_pos _).ne')

theorem directionalPolynomialOfTerms_support (P : MvPolynomial (Fin d) ℂ) :
    directionalPolynomialOfTerms (fun j : P.support => (j : Fin d →₀ ℕ)) (fun j => P.coeff j) = P := by
  classical
  unfold directionalPolynomialOfTerms
  calc
    _ = ∑ j ∈ P.support, MvPolynomial.monomial j (P.coeff j) :=
      P.support.sum_coe_sort (fun j => MvPolynomial.monomial j (P.coeff j))
    _ = P := P.support_sum_monomial_coeff

end UV
