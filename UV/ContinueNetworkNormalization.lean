import UV.ContinueNetworkFourier

/-! Exact independent-probe normalization of the literal rooted network. -/

noncomputable section
open MeasureTheory Set
open scoped Topology BigOperators InnerProductSpace Matrix ENNReal

namespace UV

theorem networkSPDInverseGaussian_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    Integrable (fun q : EuclideanSpace ℝ ι =>
      Real.exp (-((WithLp.ofLp q) ⬝ᵥ (A⁻¹ *ᵥ WithLp.ofLp q)))) := by
  have hB : ((4 : ℝ) • A⁻¹).PosDef := hA.inv.smul (by norm_num)
  have hi := (networkSPDWave_integrable _ hB 0).re
  apply hi.congr
  filter_upwards with q
  simp only [networkSPDWave, inner_zero_left, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_mul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have he : -(4 * ((WithLp.ofLp q) ⬝ᵥ (A⁻¹ *ᵥ WithLp.ofLp q))) / 4 =
      -((WithLp.ofLp q) ⬝ᵥ (A⁻¹ *ᵥ WithLp.ofLp q)) := by ring
  rw [he]
  rfl

theorem networkSPDInverseGaussian_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    (∫ q : EuclideanSpace ℝ ι,
      Real.exp (-((WithLp.ofLp q) ⬝ᵥ (A⁻¹ *ᵥ WithLp.ofLp q)))) =
      Real.sqrt (Real.pi ^ Fintype.card ι * A.det) := by
  have hB : ((4 : ℝ) • A⁻¹).PosDef := hA.inv.smul (by norm_num)
  have h : (∫ q : EuclideanSpace ℝ ι, (networkSPDWave ((4 : ℝ) • A⁻¹) 0 q).re) =
      Real.sqrt ((4 * Real.pi) ^ Fintype.card ι / ((4 : ℝ) • A⁻¹).det) := by
    calc
      _ = (∫ q : EuclideanSpace ℝ ι, networkSPDWave ((4 : ℝ) • A⁻¹) 0 q).re :=
        integral_re (networkSPDWave_integrable _ hB 0)
      _ = _ := by
        rw [networkSPDWave_integral _ hB 0]
        simp
  have heq : (fun q : EuclideanSpace ℝ ι => (networkSPDWave ((4 : ℝ) • A⁻¹) 0 q).re) =
      fun q => Real.exp (-((WithLp.ofLp q) ⬝ᵥ (A⁻¹ *ᵥ WithLp.ofLp q))) := by
    funext q
    simp only [networkSPDWave, inner_zero_left, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, one_mul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    have he : -(4 * ((WithLp.ofLp q) ⬝ᵥ (A⁻¹ *ᵥ WithLp.ofLp q))) / 4 =
        -((WithLp.ofLp q) ⬝ᵥ (A⁻¹ *ᵥ WithLp.ofLp q)) := by ring
    rw [he]
    rfl
  rw [heq] at h
  rw [h]
  congr 1
  rw [Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, mul_pow]
  field_simp

theorem networkFullPrecision_normalizer {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (s : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) (hs : ∀ e, 0 < s e) :
    Real.sqrt ((4 * Real.pi) ^ Fintype.card (Fin n × Fin 4) /
      (networkFullPrecision src dst s).det) =
        (4 * Real.pi) ^ (2 * n) / (networkPrecision src dst s).det ^ 2 := by
  have hd := networkPrecision_det_pos G src dst s hG hcover hs
  rw [networkFullPrecision_det, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have heq : (4 * Real.pi) ^ (n * 4) / (networkPrecision src dst s).det ^ 4 =
      ((4 * Real.pi) ^ (2 * n) / (networkPrecision src dst s).det ^ 2) ^ 2 := by
    rw [div_pow, ← pow_mul, ← pow_mul]
    congr 2; omega
  rw [heq, Real.sqrt_sq (by positivity)]

theorem networkSharedFourier_exact {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (m z s : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) (hs : ∀ e, 0 < s e)
    (q : NetworkVisitSpace n) :
    networkSharedFourier src dst m z s q =
      ((networkSharedPrefactor m z s * ((4 * Real.pi) ^ (2 * n) /
        (networkPrecision src dst s).det ^ 2)) * Real.exp (-((WithLp.ofLp q) ⬝ᵥ
        (Matrix.kronecker (networkPrecision src dst s)⁻¹ (1 : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ WithLp.ofLp q))) : ℝ) := by
  rw [networkSharedFourier_factor, networkSPDWave_integral _
    (networkFullPrecision_posDef G src dst s hG hcover hs),
    networkFullPrecision_normalizer G src dst s hG hcover hs, networkFullPrecision_inverse]
  push_cast
  ring

theorem networkFullPrecision_inverseGaussian_integral {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (s : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) (hs : ∀ e, 0 < s e) :
    (∫ q : NetworkVisitSpace n,
      Real.exp (-((WithLp.ofLp q) ⬝ᵥ ((networkFullPrecision src dst s)⁻¹ *ᵥ WithLp.ofLp q)))) =
      Real.pi ^ (2 * n) * (networkPrecision src dst s).det ^ 2 := by
  have hd := networkPrecision_det_pos G src dst s hG hcover hs
  rw [networkSPDInverseGaussian_integral _ (networkFullPrecision_posDef G src dst s hG hcover hs),
    networkFullPrecision_det, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have heq : Real.pi ^ (n * 4) * (networkPrecision src dst s).det ^ 4 =
      (Real.pi ^ (2 * n) * (networkPrecision src dst s).det ^ 2) ^ 2 := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
    congr 2; omega
  rw [heq, Real.sqrt_sq (by positivity)]

theorem networkSharedFourier_norm {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (m z s : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) (hs : ∀ e, 0 < s e)
    (q : NetworkVisitSpace n) :
    ‖networkSharedFourier src dst m z s q‖ =
      networkSharedPrefactor m z s *
        Real.sqrt ((4 * Real.pi) ^ Fintype.card (Fin n × Fin 4) / (networkFullPrecision src dst s).det) *
        Real.exp (-((WithLp.ofLp q) ⬝ᵥ ((networkFullPrecision src dst s)⁻¹ *ᵥ WithLp.ofLp q))) := by
  rw [networkSharedFourier_factor, networkSPDWave_integral _
    (networkFullPrecision_posDef G src dst s hG hcover hs), ← Complex.ofReal_mul,
    Complex.norm_real, Real.norm_of_nonneg]
  · ring
  · exact mul_nonneg (networkSharedPrefactor_nonneg m z s hs)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)

theorem networkSharedFourier_momentum_integrable {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (m z s : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) (hs : ∀ e, 0 < s e) :
    Integrable (fun q : NetworkVisitSpace n => ‖networkSharedFourier src dst m z s q‖) := by
  have hi := (networkSPDInverseGaussian_integrable _
    (networkFullPrecision_posDef G src dst s hG hcover hs)).const_mul
      (networkSharedPrefactor m z s *
        Real.sqrt ((4 * Real.pi) ^ Fintype.card (Fin n × Fin 4) / (networkFullPrecision src dst s).det))
  exact hi.congr (Filter.Eventually.of_forall (fun q =>
    (networkSharedFourier_norm G src dst m z s hG hcover hs q).symm))

/-- The actual normalized independent-probe momentum integral cancels both
Gaussian determinant factors, leaving exactly the edge kernels at Δx=0. -/
theorem networkSharedFourier_momentum_integral {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (m z s : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) (hs : ∀ e, 0 < s e) :
    (1 / (2 * Real.pi) ^ (4 * n)) *
      (∫ q : NetworkVisitSpace n, ‖networkSharedFourier src dst m z s q‖) =
        networkSharedPrefactor m z s := by
  simp_rw [networkSharedFourier_norm G src dst m z s hG hcover hs]
  rw [integral_const_mul, networkFullPrecision_inverseGaussian_integral G src dst s hG hcover hs,
    networkFullPrecision_normalizer G src dst s hG hcover hs]
  have hd := networkPrecision_det_pos G src dst s hG hcover hs
  have hpow : (4 * Real.pi) ^ (2 * n) * Real.pi ^ (2 * n) = (2 * Real.pi) ^ (4 * n) := by
    rw [← mul_pow]
    calc
      _ = ((2 * Real.pi) ^ 2) ^ (2 * n) := by congr 1; ring
      _ = _ := by rw [← pow_mul]; congr 1; omega
  field_simp
  linear_combination networkSharedPrefactor m z s * hpow

end UV
