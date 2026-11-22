import UV.VerifyNetworkDisplacements
import UV.AdvanceNetworkRoutedBounds

/-! The polynomial multiplying a coherent Gaussian after finitely many
actual displacement insertions. Each derivative replaces a frequency
pairing by a covariance pairing or differentiates the Gaussian itself. -/

noncomputable section

open scoped BigOperators InnerProductSpace Matrix

namespace UV

inductive NetworkMarkPolynomial (n : ℕ)
  | constant (c : ℝ)
  | linear (u : NetworkVisitSpace n)
  | pairing (u v : NetworkVisitSpace n)
  | add (f g : NetworkMarkPolynomial n)
  | mul (f g : NetworkMarkPolynomial n)

variable {n : ℕ}

def NetworkMarkPolynomial.evaluate (Q : NetworkVisitSpace n →L[ℝ] NetworkVisitSpace n)
    (q : NetworkVisitSpace n) : NetworkMarkPolynomial n → ℝ
  | .constant c => c
  | .linear u => inner ℝ u (Q q)
  | .pairing u v => inner ℝ u (Q v)
  | .add f g => f.evaluate Q q + g.evaluate Q q
  | .mul f g => f.evaluate Q q * g.evaluate Q q

def NetworkMarkPolynomial.derivative (v : NetworkVisitSpace n) :
    NetworkMarkPolynomial n → NetworkMarkPolynomial n
  | .constant _ => .constant 0
  | .linear u => .pairing u v
  | .pairing _ _ => .constant 0
  | .add f g => .add (f.derivative v) (g.derivative v)
  | .mul f g => .add (.mul (f.derivative v) g) (.mul f (g.derivative v))

def NetworkMarkPolynomial.degree : NetworkMarkPolynomial n → ℕ
  | .constant _ => 0
  | .linear _ => 1
  | .pairing _ _ => 1
  | .add f g => max f.degree g.degree
  | .mul f g => f.degree + g.degree

theorem NetworkMarkPolynomial.derivative_degree_le (f : NetworkMarkPolynomial n)
    (v : NetworkVisitSpace n) : (f.derivative v).degree ≤ f.degree := by
  induction f with
  | constant c => simp [NetworkMarkPolynomial.derivative, NetworkMarkPolynomial.degree]
  | linear u => simp [NetworkMarkPolynomial.derivative, NetworkMarkPolynomial.degree]
  | pairing u w => simp [NetworkMarkPolynomial.derivative, NetworkMarkPolynomial.degree]
  | add f g hf hg =>
      simp only [NetworkMarkPolynomial.derivative, NetworkMarkPolynomial.degree]
      exact max_le_max hf hg
  | mul f g hf hg =>
      simp only [NetworkMarkPolynomial.derivative, NetworkMarkPolynomial.degree]
      exact max_le (add_le_add_right hf _) (add_le_add_left hg _)

theorem NetworkMarkPolynomial.evaluate_hasDerivAt (f : NetworkMarkPolynomial n)
    (Q : NetworkVisitSpace n →L[ℝ] NetworkVisitSpace n) (q v : NetworkVisitSpace n) (t : ℝ) :
    HasDerivAt (fun y : ℝ => f.evaluate Q (q + y • v))
      ((f.derivative v).evaluate Q (q + t • v)) t := by
  induction f with
  | constant c => exact hasDerivAt_const t c
  | linear u =>
      simpa only [NetworkMarkPolynomial.evaluate, NetworkMarkPolynomial.derivative, map_add, map_smul,
        inner_add_right, real_inner_smul_right, id, one_mul] using
        ((hasDerivAt_id t).mul_const (inner ℝ u (Q v))).const_add (inner ℝ u (Q q))
  | pairing u w => exact hasDerivAt_const t (inner ℝ u (Q w))
  | add f g hf hg => exact hf.add hg
  | mul f g hf hg => exact hf.mul hg

/-- Polynomial from the complete list of directional Gaussian marks. -/
def networkMarkPolynomial : List (NetworkVisitSpace n) → NetworkMarkPolynomial n
  | [] => .constant 1
  | v :: directions =>
    let f := networkMarkPolynomial directions
    .add (f.derivative v) (.mul (.mul (.constant (-2)) (.linear v)) f)

theorem networkMarkPolynomial_degree (directions : List (NetworkVisitSpace n)) :
    (networkMarkPolynomial directions).degree ≤ directions.length := by
  induction directions with
  | nil => exact le_rfl
  | cons v directions ih =>
      simp only [networkMarkPolynomial, NetworkMarkPolynomial.degree, List.length_cons]
      have hb := (networkMarkPolynomial directions).derivative_degree_le v
      omega

def networkCovariance {E : Type*} [Fintype E] (src dst : E → Option (Fin n)) (s : E → ℝ) :
    NetworkVisitSpace n →L[ℝ] NetworkVisitSpace n :=
  (Matrix.toEuclideanLin ((networkFullPrecision src dst s)⁻¹)).toContinuousLinearMap

theorem networkSharedDamping_eq_inner {E : Type*} [Fintype E]
    (src dst : E → Option (Fin n)) (s : E → ℝ) (q : NetworkVisitSpace n) :
    networkSharedDamping src dst s q = inner ℝ q (networkCovariance src dst s q) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, networkSharedDamping, dotProduct_comm]
  rfl

theorem networkCovariance_pair_symmetric {E : Type*} [Fintype E]
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (s : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) (hs : ∀ e, 0 < s e)
    (u v : NetworkVisitSpace n) :
    inner ℝ u (networkCovariance src dst s v) = inner ℝ v (networkCovariance src dst s u) := by
  have hQ := (networkFullPrecision_posDef G src dst s hG hcover hs).inv.isHermitian
  have hSym := Matrix.isHermitian_iff_isSymmetric.mp hQ
  rw [← real_inner_comm u (networkCovariance src dst s v)]
  exact hSym v u

private theorem networkCovariance_exp_hasDerivAt
    (Q : NetworkVisitSpace n →L[ℝ] NetworkVisitSpace n)
    (hQ : ∀ u v, inner ℝ u (Q v) = inner ℝ v (Q u)) (q v : NetworkVisitSpace n) (t : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-(inner ℝ (q + y • v) (Q (q + y • v)))))
      ((-2 * inner ℝ v (Q (q + t • v))) * Real.exp (-(inner ℝ (q + t • v) (Q (q + t • v))))) t := by
  have he (y : ℝ) : inner ℝ (q + y • v) (Q (q + y • v)) =
      inner ℝ q (Q q) + (2 * inner ℝ v (Q q)) * y + inner ℝ v (Q v) * y ^ 2 := by
    rw [map_add, map_smul, inner_add_left, inner_add_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right, hQ q v]
    ring
  have hderiv : HasDerivAt (fun y => inner ℝ (q + y • v) (Q (q + y • v)))
      (2 * inner ℝ v (Q (q + t • v))) t := by
    have hp := (((hasDerivAt_id t).const_mul (2 * inner ℝ v (Q q))).const_add
      (inner ℝ q (Q q))).add (((hasDerivAt_id t).pow 2).const_mul (inner ℝ v (Q v)))
    convert hp using 1
    · funext y
      exact he y
    · simp only [map_add, map_smul, inner_add_right, real_inner_smul_right, id, Nat.cast_ofNat,
        Nat.reduceSubDiff, pow_one, mul_one]
      ring
  convert hderiv.neg.exp using 1
  simp only [Pi.neg_apply]
  ring

/-- The marked coefficient is the Gaussian characteristic of the same
kernel times its exactly derived covariance polynomial. -/
theorem networkMarkedFourier_eq_polynomial {E : Type*} [Fintype E]
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n)) (m z s : E → ℝ)
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst) (hs : ∀ e, 0 < s e)
    (directions : List (NetworkVisitSpace n)) (q : NetworkVisitSpace n) :
    networkMarkedFourier src dst m z s directions q =
      ((networkMarkPolynomial directions).evaluate (networkCovariance src dst s) q : ℂ) *
        networkSharedFourier src dst m z s q := by
  let Q := networkCovariance src dst s
  let A := networkSharedPrefactor m z s * ((4 * Real.pi) ^ (2 * n) /
    (networkPrecision src dst s).det ^ 2)
  have hQ (u v : NetworkVisitSpace n) : inner ℝ u (Q v) = inner ℝ v (Q u) :=
    networkCovariance_pair_symmetric G src dst s hG hcover hs u v
  have hGaussian (u : NetworkVisitSpace n) : networkSharedFourier src dst m z s u =
      ((A * Real.exp (-(inner ℝ u (Q u)))) : ℝ) := by
    rw [networkSharedFourier_exact G src dst m z s hG hcover hs,
      ← networkFullPrecision_inverse]
    exact congrArg Complex.ofReal (congrArg (fun y => A * Real.exp (-y))
      (networkSharedDamping_eq_inner src dst s u))
  induction directions generalizing q with
  | nil => simp [networkMarkPolynomial, NetworkMarkPolynomial.evaluate]
  | cons v directions ih =>
      let f := networkMarkPolynomial directions
      have hmark := networkMarkedFourier_hasDerivAt G src dst m z s hG hcover hs directions q v 0
      have hP := f.evaluate_hasDerivAt Q q v 0
      have hGau := (networkCovariance_exp_hasDerivAt Q hQ q v 0).const_mul A
      have h := (hP.mul hGau).ofReal_comp
      let P (t : ℝ) : ℝ := f.evaluate Q (q + t • v) *
        (A * Real.exp (-(inner ℝ (q + t • v) (Q (q + t • v)))))
      have hfun : (fun t => (P t : ℂ)) =
          fun t : ℝ => networkMarkedFourier src dst m z s directions (q + t • v) := by
        funext t
        rw [ih, hGaussian]
        exact Complex.ofReal_mul _ _
      change HasDerivAt (fun t => (P t : ℂ)) _ 0 at h
      rw [hfun] at h
      have hvalue := hmark.unique h
      simp only [zero_smul, add_zero] at hvalue
      rw [hvalue, hGaussian]
      simp only [networkMarkPolynomial, NetworkMarkPolynomial.evaluate]
      push_cast
      ring

end UV
