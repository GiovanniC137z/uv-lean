import UV.ContinueNetworkGaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Literal Fourier integration of a positive Gaussian in orthogonal
coordinates. The normalization is an actual Lebesgue integral, not a
postulated characteristic function. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators InnerProductSpace Matrix

namespace UV

def networkDiagonalWave {ι : Type*} [Fintype ι] (a q x : ι → ℝ) : ℂ :=
  Complex.exp (-(∑ i, ((a i / 4 : ℝ) : ℂ) * (x i : ℂ) ^ 2) +
    ∑ i, (Complex.I * (q i : ℂ)) * (x i : ℂ))

def networkDiagonalNormalizer {ι : Type*} [Fintype ι] (a : ι → ℝ) : ℂ :=
  ∏ i, ((Real.pi : ℂ) / ((a i / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)

theorem networkDiagonalWave_integrable {ι : Type*} [Fintype ι]
    (a q : ι → ℝ) (ha : ∀ i, 0 < a i) : Integrable (networkDiagonalWave a q) := by
  exact GaussianFourier.integrable_cexp_neg_sum_mul_add (fun i => by simpa using (div_pos (ha i) (by norm_num) : 0 < a i / 4))
    (fun i => Complex.I * (q i : ℂ))

theorem networkDiagonalWave_integral {ι : Type*} [Fintype ι]
    (a q : ι → ℝ) (ha : ∀ i, 0 < a i) :
    (∫ x : ι → ℝ, networkDiagonalWave a q x) = networkDiagonalNormalizer a *
      (Real.exp (-(∑ i, q i ^ 2 / a i)) : ℂ) := by
  unfold networkDiagonalWave
  rw [GaussianFourier.integral_cexp_neg_sum_mul_add
    (fun i => by simpa using (div_pos (ha i) (by norm_num) : 0 < a i / 4))]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, Complex.ofReal_exp]
  congr 1
  congr 1
  push_cast
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_pow, Complex.I_sq, neg_one_mul]
  ring

theorem networkDiagonalNormalizer_ne_zero {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) : networkDiagonalNormalizer a ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Complex.cpow_ne_zero_iff.mpr
  left
  apply div_ne_zero
  · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (div_pos (ha i) (by norm_num) : 0 < a i / 4))

theorem networkDiagonalWave_zero_integral {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    (∫ x : ι → ℝ, networkDiagonalWave a 0 x) = networkDiagonalNormalizer a := by
  rw [networkDiagonalWave_integral a 0 ha]
  simp

theorem networkDiagonalWave_normalized {ι : Type*} [Fintype ι]
    (a q : ι → ℝ) (ha : ∀ i, 0 < a i) :
    (∫ x : ι → ℝ, networkDiagonalWave a q x) /
      (∫ x : ι → ℝ, networkDiagonalWave a 0 x) =
        (Real.exp (-(∑ i, q i ^ 2 / a i)) : ℂ) := by
  rw [networkDiagonalWave_integral a q ha, networkDiagonalWave_zero_integral a ha]
  exact mul_div_cancel_left₀ _ (networkDiagonalNormalizer_ne_zero a ha)

def networkBasisWave {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (a : ι → ℝ) (q x : V) : ℂ :=
  Complex.exp (Complex.I * (inner ℝ q x : ℂ)) *
    (Real.exp (-(∑ i, (a i / 4) * (b.repr x i) ^ 2)) : ℂ)

theorem networkBasisWave_coordinates {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fintype ι] (b : OrthonormalBasis ι ℝ V) (a : ι → ℝ) (q x : V) :
    networkBasisWave b a q x = networkDiagonalWave a (fun i => b.repr q i) (fun i => b.repr x i) := by
  have hi : inner ℝ q x = ∑ i, (b.repr q i) * (b.repr x i) := by
    have hh := b.repr.inner_map_map q x
    simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm] using hh.symm
  unfold networkBasisWave networkDiagonalWave
  rw [hi, Complex.ofReal_exp, ← Complex.exp_add]
  push_cast
  rw [Finset.mul_sum]
  congr 1
  rw [add_comm]
  apply congrArg₂ (· + ·)
  · rfl
  · apply Finset.sum_congr rfl
    intro i _
    ring

theorem networkBasisWave_integral {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (a : ι → ℝ) (ha : ∀ i, 0 < a i) (q : V) :
    (∫ x : V, networkBasisWave b a q x) = networkDiagonalNormalizer a *
      (Real.exp (-(∑ i, (b.repr q i) ^ 2 / a i)) : ℂ) := by
  let e : V ≃ᵐ (ι → ℝ) := b.measurableEquiv.trans (EuclideanSpace.measurableEquiv ι)
  have he : MeasurePreserving e volume volume :=
    (EuclideanSpace.volume_preserving_measurableEquiv ι).comp b.measurePreserving_measurableEquiv
  have hh := he.integral_comp' (networkDiagonalWave a (fun i => b.repr q i))
  calc
    _ = ∫ x : V, networkDiagonalWave a (fun i => b.repr q i) (e x) := by
      apply integral_congr_ae
      filter_upwards with x
      exact networkBasisWave_coordinates b a q x
    _ = _ := hh.trans (networkDiagonalWave_integral a (fun i => b.repr q i) ha)

theorem networkBasisWave_integrable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (a : ι → ℝ) (ha : ∀ i, 0 < a i) (q : V) :
    Integrable (networkBasisWave b a q) := by
  let e : V ≃ᵐ (ι → ℝ) := b.measurableEquiv.trans (EuclideanSpace.measurableEquiv ι)
  have he : MeasurePreserving e volume volume :=
    (EuclideanSpace.volume_preserving_measurableEquiv ι).comp b.measurePreserving_measurableEquiv
  have hi := (he.integrable_comp_emb e.measurableEmbedding).mpr
    (networkDiagonalWave_integrable a (fun i => b.repr q i) ha)
  apply hi.congr
  filter_upwards with x
  exact (networkBasisWave_coordinates b a q x).symm

theorem networkBasisWave_normalized {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (a : ι → ℝ) (ha : ∀ i, 0 < a i) (q : V) :
    (∫ x : V, networkBasisWave b a q x) / (∫ x : V, networkBasisWave b a 0 x) =
      (Real.exp (-(∑ i, (b.repr q i) ^ 2 / a i)) : ℂ) := by
  rw [networkBasisWave_integral b a ha q, networkBasisWave_integral b a ha 0]
  simp only [map_zero, PiLp.zero_apply, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div,
    Finset.sum_const_zero, neg_zero, Real.exp_zero, Complex.ofReal_one, mul_one]
  exact mul_div_cancel_left₀ _ (networkDiagonalNormalizer_ne_zero a ha)

theorem networkBasis_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) (a : ι → ℝ)
    (heigen : ∀ i, Matrix.toEuclideanLin A (b i) = a i • b i) (x : EuclideanSpace ℝ ι) :
    (WithLp.ofLp x) ⬝ᵥ (A *ᵥ WithLp.ofLp x) = ∑ i, a i * (b.repr x i) ^ 2 := by
  have hT : Matrix.toEuclideanLin A x = ∑ i, (a i * b.repr x i) • b i := by
    nth_rw 1 [← b.sum_repr x]
    rw [map_sum]
    simp_rw [map_smul, heigen, smul_smul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring
  have hdot : inner ℝ x (Matrix.toEuclideanLin A x) =
      (WithLp.ofLp x) ⬝ᵥ (A *ᵥ WithLp.ofLp x) := by
    simp [PiLp.inner_apply, RCLike.inner_apply, Matrix.toEuclideanLin_apply, dotProduct, mul_comm]
  rw [← hdot, hT, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : inner ℝ x (b i) = b.repr x i := by
    rw [b.repr_apply_apply]
    exact real_inner_comm _ _
  rw [inner_smul_right, hi]
  ring

theorem networkSPD_eigenbasis_action {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (i : ι) :
    Matrix.toEuclideanLin A (hA.eigenvectorBasis i) = hA.eigenvalues i • hA.eigenvectorBasis i := by
  apply WithLp.ofLp_injective
  exact hA.mulVec_eigenvectorBasis i

def networkSPDWave {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (q x : EuclideanSpace ℝ ι) : ℂ :=
  Complex.exp (Complex.I * (inner ℝ q x : ℂ)) *
    (Real.exp (-((WithLp.ofLp x) ⬝ᵥ (A *ᵥ WithLp.ofLp x)) / 4) : ℂ)

theorem networkSPDWave_eigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (q x : EuclideanSpace ℝ ι) :
    networkSPDWave A q x = networkBasisWave hA.eigenvectorBasis hA.eigenvalues q x := by
  have he : (∑ i, (hA.eigenvalues i / 4) * (hA.eigenvectorBasis.repr x i) ^ 2) =
      ((WithLp.ofLp x) ⬝ᵥ (A *ᵥ WithLp.ofLp x)) / 4 := by
    rw [networkBasis_quadratic A hA.eigenvectorBasis hA.eigenvalues (networkSPD_eigenbasis_action A hA),
      Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold networkSPDWave networkBasisWave
  rw [he]
  simp only [neg_div]

theorem networkSPDWave_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (q : EuclideanSpace ℝ ι) :
    Integrable (networkSPDWave A q) := by
  have he : networkSPDWave A q = networkBasisWave hA.1.eigenvectorBasis hA.1.eigenvalues q :=
    funext (networkSPDWave_eigenbasis A hA.1 q)
  rw [he]
  exact networkBasisWave_integrable _ _ hA.eigenvalues_pos q

/-- The normalized characteristic is obtained from the actual Lebesgue
integral after an orthogonal eigenbasis change of variables. -/
theorem networkSPDWave_normalized_eigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (q : EuclideanSpace ℝ ι) :
    (∫ x : EuclideanSpace ℝ ι, networkSPDWave A q x) /
      (∫ x : EuclideanSpace ℝ ι, networkSPDWave A 0 x) =
        (Real.exp (-(∑ i, (hA.1.eigenvectorBasis.repr q i) ^ 2 / hA.1.eigenvalues i)) : ℂ) := by
  simp_rw [networkSPDWave_eigenbasis A hA.1]
  exact networkBasisWave_normalized _ _ hA.eigenvalues_pos q

theorem networkSPD_inverse_eigenbasis_action {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (i : ι) :
    Matrix.toEuclideanLin A⁻¹ (hA.1.eigenvectorBasis i) =
      (hA.1.eigenvalues i)⁻¹ • hA.1.eigenvectorBasis i := by
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hi : A⁻¹ *ᵥ (A *ᵥ WithLp.ofLp (hA.1.eigenvectorBasis i)) =
      WithLp.ofLp (hA.1.eigenvectorBasis i) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  rw [hA.1.mulVec_eigenvectorBasis, Matrix.mulVec_smul] at hi
  apply WithLp.ofLp_injective
  change A⁻¹ *ᵥ WithLp.ofLp (hA.1.eigenvectorBasis i) =
    (hA.1.eigenvalues i)⁻¹ • WithLp.ofLp (hA.1.eigenvectorBasis i)
  calc
    _ = (hA.1.eigenvalues i)⁻¹ •
        (hA.1.eigenvalues i • (A⁻¹ *ᵥ WithLp.ofLp (hA.1.eigenvectorBasis i))) := by
      rw [inv_smul_smul₀ (hA.eigenvalues_pos i).ne']
    _ = _ := congrArg (fun y => (hA.1.eigenvalues i)⁻¹ • y) hi

theorem networkSPD_inverse_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (q : EuclideanSpace ℝ ι) :
    (∑ i, (hA.1.eigenvectorBasis.repr q i) ^ 2 / hA.1.eigenvalues i) =
      (WithLp.ofLp q) ⬝ᵥ (A⁻¹ *ᵥ WithLp.ofLp q) := by
  rw [networkBasis_quadratic A⁻¹ hA.1.eigenvectorBasis (fun i => (hA.1.eigenvalues i)⁻¹)
    (networkSPD_inverse_eigenbasis_action A hA)]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem networkSPDWave_normalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (q : EuclideanSpace ℝ ι) :
    (∫ x : EuclideanSpace ℝ ι, networkSPDWave A q x) /
      (∫ x : EuclideanSpace ℝ ι, networkSPDWave A 0 x) =
        (Real.exp (-((WithLp.ofLp q) ⬝ᵥ (A⁻¹ *ᵥ WithLp.ofLp q))) : ℂ) := by
  rw [networkSPDWave_normalized_eigenbasis A hA, networkSPD_inverse_quadratic A hA]

theorem networkSPDWave_integral_spectral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (q : EuclideanSpace ℝ ι) :
    (∫ x : EuclideanSpace ℝ ι, networkSPDWave A q x) =
      networkDiagonalNormalizer hA.1.eigenvalues *
        (Real.exp (-((WithLp.ofLp q) ⬝ᵥ (A⁻¹ *ᵥ WithLp.ofLp q))) : ℂ) := by
  simp_rw [networkSPDWave_eigenbasis A hA.1]
  rw [networkBasisWave_integral _ _ hA.eigenvalues_pos, networkSPD_inverse_quadratic A hA]

theorem networkDiagonalNormalizer_real {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    networkDiagonalNormalizer a = ((∏ i, Real.sqrt (4 * Real.pi / a i) : ℝ) : ℂ) := by
  unfold networkDiagonalNormalizer
  rw [Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  have hpos : 0 ≤ Real.pi / (a i / 4) := (div_pos Real.pi_pos (div_pos (ha i) (by norm_num))).le
  have hpow : (((Real.pi / (a i / 4) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) =
      (Real.sqrt (Real.pi / (a i / 4)) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hpos]
    norm_num
  rw [← Complex.ofReal_div, hpow]
  congr 2
  field_simp

theorem networkSPD_normalizer_determinant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    networkDiagonalNormalizer hA.1.eigenvalues =
      (Real.sqrt ((4 * Real.pi) ^ Fintype.card ι / A.det) : ℂ) := by
  let R : ℝ := ∏ i, Real.sqrt (4 * Real.pi / hA.1.eigenvalues i)
  have hR : 0 ≤ R := Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have hRsq : R ^ 2 = (4 * Real.pi) ^ Fintype.card ι / A.det := by
    dsimp [R]
    rw [← Finset.prod_pow]
    have hsquare (i : ι) : Real.sqrt (4 * Real.pi / hA.1.eigenvalues i) ^ 2 =
        4 * Real.pi / hA.1.eigenvalues i :=
      Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (hA.eigenvalues_pos i).le)
    simp_rw [hsquare]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, hA.1.det_eq_prod_eigenvalues]
    rfl
  have he := congrArg Real.sqrt hRsq
  rw [Real.sqrt_sq hR] at he
  rw [networkDiagonalNormalizer_real _ hA.eigenvalues_pos]
  exact congrArg Complex.ofReal he

/-- Exact SPD Fourier evaluation, with both its covariance and determinant
normalization derived from the actual eigenbasis integration. -/
theorem networkSPDWave_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (q : EuclideanSpace ℝ ι) :
    (∫ x : EuclideanSpace ℝ ι, networkSPDWave A q x) =
      (Real.sqrt ((4 * Real.pi) ^ Fintype.card ι / A.det) *
        Real.exp (-((WithLp.ofLp q) ⬝ᵥ (A⁻¹ *ᵥ WithLp.ofLp q))) : ℝ) := by
  rw [networkSPDWave_integral_spectral A hA q, networkSPD_normalizer_determinant A hA]
  exact (Complex.ofReal_mul _ _).symm

def networkFullPrecision {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (s : E → ℝ) : Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ :=
  Matrix.kronecker (networkPrecision src dst s) (1 : Matrix (Fin 4) (Fin 4) ℝ)

theorem networkFullPrecision_mulVec {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (s : E → ℝ) (x : (Fin n × Fin 4) → ℝ)
    (v : Fin n) (ν : Fin 4) :
    (networkFullPrecision src dst s *ᵥ x) (v, ν) =
      (networkPrecision src dst s *ᵥ (fun w => x (w, ν))) v := by
  classical
  simp [networkFullPrecision, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.one_apply]

theorem networkFullPrecision_quadratic {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (s : E → ℝ) (x : NetworkVisitSpace n) :
    (WithLp.ofLp x) ⬝ᵥ (networkFullPrecision src dst s *ᵥ WithLp.ofLp x) =
      networkSharedEnergy src dst s x := by
  rw [networkSharedEnergy_matrix]
  simp only [dotProduct, Fintype.sum_prod_type, networkFullPrecision_mulVec]
  rw [Finset.sum_comm]
  rfl

theorem networkFullPrecision_posDef {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (s : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) (hs : ∀ e, 0 < s e) :
    (networkFullPrecision src dst s).PosDef := by
  have hH := networkPrecision_posDef G src dst s hG hcover hs
  refine ⟨?_, ?_⟩
  · unfold networkFullPrecision Matrix.kronecker
    rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, hH.isHermitian.eq, Matrix.conjTranspose_one]
  · intro x hx
    have hx' : WithLp.toLp 2 x ≠ (0 : NetworkVisitSpace n) := by
      intro h
      apply hx
      exact congrArg WithLp.ofLp h
    have h := networkSharedEnergy_positive G src dst s hG hcover hs hx'
    rw [← networkFullPrecision_quadratic] at h
    simpa only [WithLp.ofLp_toLp, star_trivial] using h

theorem networkFullPrecision_det {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (s : E → ℝ) :
    (networkFullPrecision src dst s).det = (networkPrecision src dst s).det ^ 4 :=
  four_dimensional_routing_det _

theorem networkFullPrecision_inverse {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (s : E → ℝ) :
    (networkFullPrecision src dst s)⁻¹ =
      Matrix.kronecker (networkPrecision src dst s)⁻¹ (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  unfold networkFullPrecision Matrix.kronecker
  rw [Matrix.inv_kronecker]
  simp

theorem networkSharedFourier_factor {E : Type*} [Fintype E] {n : ℕ}
    (src dst : E → Option (Fin n)) (m z s : E → ℝ) (q : NetworkVisitSpace n) :
    networkSharedFourier src dst m z s q = (networkSharedPrefactor m z s : ℂ) *
      ∫ x : NetworkVisitSpace n, networkSPDWave (networkFullPrecision src dst s) q x := by
  unfold networkSharedFourier
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [networkSharedKernel_gaussian]
  unfold networkSPDWave
  rw [networkFullPrecision_quadratic]
  push_cast
  ring

/-- The literal shared-vertex Fourier coefficient has exactly the normalized
Gaussian characteristic in the manuscript, including the physical H⁻¹⊗I₄. -/
theorem networkSharedFourier_normalized {E : Type*} [Fintype E] {n : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (m z s : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) (hs : ∀ e, 0 < s e)
    (q : NetworkVisitSpace n) :
    networkSharedFourier src dst m z s q / networkSharedFourier src dst m z s 0 =
      (Real.exp (-((WithLp.ofLp q) ⬝ᵥ
        (Matrix.kronecker (networkPrecision src dst s)⁻¹ (1 : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ WithLp.ofLp q))) : ℂ) := by
  have hA := networkFullPrecision_posDef G src dst s hG hcover hs
  rw [networkSharedFourier_factor, networkSharedFourier_factor]
  rw [mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr (networkSharedPrefactor_pos m z s hs).ne')]
  rw [networkSPDWave_normalized _ hA, networkFullPrecision_inverse]

end UV
