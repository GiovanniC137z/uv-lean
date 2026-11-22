import UV.ContinueNetworkNormalization

/-! Exact translated Gaussian in the intrinsic Euclidean loop coordinates.
The induced precision uses the full-column-rank momentum map and the
inverse of the same physical shared-vertex precision. -/

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix InnerProductSpace

namespace UV

variable {ι ν : Type*} [Fintype ι] [Fintype ν]

def networkRoutedPrecision (Q : Matrix ν ν ℝ) (B : Matrix ν ι ℝ) : Matrix ι ι ℝ :=
  B.transpose * Q * B

theorem networkRoutedPrecision_posDef {Q : Matrix ν ν ℝ} {B : Matrix ν ι ℝ}
    (hQ : Q.PosDef) (hB : Function.Injective B.mulVec) :
    (networkRoutedPrecision Q B).PosDef := by
  simpa only [networkRoutedPrecision, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hQ.conjTranspose_mul_mul_same hB

private theorem networkQuadratic_pair_symm {Q : Matrix ν ν ℝ} (hQ : Q.IsHermitian)
    (x y : ν → ℝ) : x ⬝ᵥ (Q *ᵥ y) = y ⬝ᵥ (Q *ᵥ x) := by
  have hT : Q.transpose = Q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ.eq
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]

private theorem networkRoutedPrecision_pair (Q : Matrix ν ν ℝ) (B : Matrix ν ι ℝ)
    (u v : ι → ℝ) :
    (B *ᵥ u) ⬝ᵥ (Q *ᵥ (B *ᵥ v)) = u ⬝ᵥ (networkRoutedPrecision Q B *ᵥ v) := by
  unfold networkRoutedPrecision
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u B.transpose,
    Matrix.vecMul_transpose]

variable [DecidableEq ι]

def networkRoutedCenter (Q : Matrix ν ν ℝ) (B : Matrix ν ι ℝ) (b : ν → ℝ) : ι → ℝ :=
  (networkRoutedPrecision Q B)⁻¹ *ᵥ (B.transpose *ᵥ (Q *ᵥ b))

def networkRoutedResidual (Q : Matrix ν ν ℝ) (B : Matrix ν ι ℝ) (b : ν → ℝ) : ν → ℝ :=
  b - B *ᵥ networkRoutedCenter Q B b

/-- The residual of the shift is orthogonal to the full route in the
shared-vertex precision pairing. -/
theorem networkRoutedResidual_orthogonal {Q : Matrix ν ν ℝ} {B : Matrix ν ι ℝ}
    (hQ : Q.PosDef) (hB : Function.Injective B.mulVec) (b : ν → ℝ) (k : ι → ℝ) :
    (B *ᵥ k) ⬝ᵥ (Q *ᵥ networkRoutedResidual Q B b) = 0 := by
  let P := networkRoutedPrecision Q B
  have hP : P.PosDef := networkRoutedPrecision_posDef hQ hB
  have hsolve : P *ᵥ networkRoutedCenter Q B b = B.transpose *ᵥ (Q *ᵥ b) := by
    change P *ᵥ (P⁻¹ *ᵥ _) = _
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP.det_pos.ne'),
      Matrix.one_mulVec]
  rw [networkRoutedResidual, Matrix.mulVec_sub, dotProduct_sub,
    networkRoutedPrecision_pair, hsolve, Matrix.dotProduct_mulVec k B.transpose,
    Matrix.vecMul_transpose, sub_self]

theorem networkRoutedResidual_nonneg {Q : Matrix ν ν ℝ} {B : Matrix ν ι ℝ}
    (hQ : Q.PosDef) (b : ν → ℝ) :
    0 ≤ networkRoutedResidual Q B b ⬝ᵥ (Q *ᵥ networkRoutedResidual Q B b) := by
  simpa only [star_trivial] using hQ.posSemidef.2 (networkRoutedResidual Q B b)

/-- Completion of the square for the literal routed exponent. The residual
depends only on the component of the shift orthogonal to the route. -/
theorem networkRoutedQuadratic_complete_square {Q : Matrix ν ν ℝ} {B : Matrix ν ι ℝ}
    (hQ : Q.PosDef) (hB : Function.Injective B.mulVec) (b : ν → ℝ) (k : ι → ℝ) :
    (B *ᵥ k + b) ⬝ᵥ (Q *ᵥ (B *ᵥ k + b)) =
      (k + networkRoutedCenter Q B b) ⬝ᵥ
        (networkRoutedPrecision Q B *ᵥ (k + networkRoutedCenter Q B b)) +
      networkRoutedResidual Q B b ⬝ᵥ (Q *ᵥ networkRoutedResidual Q B b) := by
  let c := networkRoutedCenter Q B b
  let r := networkRoutedResidual Q B b
  have hshift : B *ᵥ k + b = B *ᵥ (k + c) + r := by
    change B *ᵥ k + b = B *ᵥ (k + c) + (b - B *ᵥ c)
    rw [Matrix.mulVec_add]
    abel
  have hz : (B *ᵥ (k + c)) ⬝ᵥ (Q *ᵥ r) = 0 :=
    networkRoutedResidual_orthogonal hQ hB b (k + c)
  rw [hshift, Matrix.mulVec_add Q (B *ᵥ (k + c)) r, add_dotProduct,
    dotProduct_add, dotProduct_add,
    hz, ← networkQuadratic_pair_symm hQ.isHermitian (B *ᵥ (k + c)) r, hz,
    networkRoutedPrecision_pair, add_zero, zero_add]

/-- Actual Lebesgue integral on the independent loop variables. -/
theorem networkRoutedGaussian_integral {Q : Matrix ν ν ℝ} {B : Matrix ν ι ℝ}
    (hQ : Q.PosDef) (hB : Function.Injective B.mulVec) (b : ν → ℝ) :
    (∫ k : EuclideanSpace ℝ ι,
      Real.exp (-((B *ᵥ k.ofLp + b) ⬝ᵥ (Q *ᵥ (B *ᵥ k.ofLp + b))))) =
      Real.exp (-(networkRoutedResidual Q B b ⬝ᵥ (Q *ᵥ networkRoutedResidual Q B b))) *
        Real.sqrt (Real.pi ^ Fintype.card ι / (networkRoutedPrecision Q B).det) := by
  let P := networkRoutedPrecision Q B
  let c : EuclideanSpace ℝ ι := WithLp.toLp 2 (networkRoutedCenter Q B b)
  let r := networkRoutedResidual Q B b
  have hP : P.PosDef := networkRoutedPrecision_posDef hQ hB
  have hiP := isUnit_iff_ne_zero.mpr hP.det_pos.ne'
  have hsq (k : EuclideanSpace ℝ ι) :
      Real.exp (-((B *ᵥ k.ofLp + b) ⬝ᵥ (Q *ᵥ (B *ᵥ k.ofLp + b)))) =
        Real.exp (-(r ⬝ᵥ (Q *ᵥ r))) *
          Real.exp (-((k + c).ofLp ⬝ᵥ (P *ᵥ (k + c).ofLp))) := by
    rw [networkRoutedQuadratic_complete_square hQ hB, ← Real.exp_add, WithLp.ofLp_add]
    congr 1
    dsimp only [c, P, r, WithLp.ofLp_toLp]
    ring
  simp_rw [hsq]
  rw [integral_const_mul, integral_add_right_eq_self
    (fun k : EuclideanSpace ℝ ι => Real.exp (-(k.ofLp ⬝ᵥ (P *ᵥ k.ofLp)))) c]
  have hi := networkSPDInverseGaussian_integral P⁻¹ hP.inv
  rw [Matrix.nonsing_inv_nonsing_inv P hiP, Matrix.det_nonsing_inv, Ring.inverse_eq_inv,
    ← div_eq_mul_inv] at hi
  rw [hi]

/-- Coordinates of the same routed momentum map, in the declared orthonormal
Euclidean bases of the intrinsic loop and shared-vertex spaces. -/
def networkRoutingMatrix {L n : ℕ} (B : NetworkVisitSpace L →L[ℝ] NetworkVisitSpace n) :
    Matrix (Fin n × Fin 4) (Fin L × Fin 4) ℝ :=
  (Matrix.toEuclideanLin (𝕜 := ℝ)).symm B.toLinearMap

theorem networkRoutingMatrix_mulVec {L n : ℕ} (B : NetworkVisitSpace L →L[ℝ] NetworkVisitSpace n)
    (k : NetworkVisitSpace L) :
    networkRoutingMatrix B *ᵥ k.ofLp = (B k).ofLp := by
  rw [← Matrix.ofLp_toEuclideanLin_apply, networkRoutingMatrix, LinearEquiv.apply_symm_apply]
  rfl

theorem networkRoutingMatrix_injective {L n : ℕ}
    {B : NetworkVisitSpace L →L[ℝ] NetworkVisitSpace n} (hB : Function.Injective B) :
    Function.Injective (networkRoutingMatrix B).mulVec := by
  intro u v h
  change networkRoutingMatrix B *ᵥ ((WithLp.toLp 2 u : NetworkVisitSpace L).ofLp) =
    networkRoutingMatrix B *ᵥ ((WithLp.toLp 2 v : NetworkVisitSpace L).ofLp) at h
  rw [networkRoutingMatrix_mulVec, networkRoutingMatrix_mulVec] at h
  exact congrArg WithLp.ofLp (hB ((WithLp.equiv _ _).injective h))

/-- The normalized integral of the routed Fourier coefficient retains both
determinants and the exact residual exponential. The normalization is
`(2π)^{-4L}` for L independent loop four-vectors. -/
theorem networkRoutedFourier_momentum_exact {E : Type*} [Fintype E] {n L : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (m z s : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) (hs : ∀ e, 0 < s e)
    {B : NetworkVisitSpace L →L[ℝ] NetworkVisitSpace n} (hB : Function.Injective B)
    (b : NetworkVisitSpace n) :
    let Q := (networkFullPrecision src dst s)⁻¹
    let C := networkRoutingMatrix B
    let r := networkRoutedResidual Q C b.ofLp
    (1 / (2 * Real.pi) ^ (4 * L)) *
      (∫ k, ‖networkRoutedFourier src dst m z s B b k‖) =
      (1 / (2 * Real.pi) ^ (4 * L)) * (networkSharedPrefactor m z s *
        ((4 * Real.pi) ^ (2 * n) / (networkPrecision src dst s).det ^ 2)) *
        (Real.exp (-(r ⬝ᵥ (Q *ᵥ r))) *
          Real.sqrt (Real.pi ^ (4 * L) / (networkRoutedPrecision Q C).det)) := by
  dsimp only
  simp_rw [networkRoutedFourier, networkSharedFourier_norm G src dst m z s hG hcover hs,
    networkFullPrecision_normalizer G src dst s hG hcover hs, WithLp.ofLp_add,
    ← networkRoutingMatrix_mulVec]
  rw [integral_const_mul, networkRoutedGaussian_integral
    (networkFullPrecision_posDef G src dst s hG hcover hs).inv
    (networkRoutingMatrix_injective hB), Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    Nat.mul_comm L 4]
  ring

end UV
