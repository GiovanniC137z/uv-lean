import UV.VerifyCurvatureProductMoments
import Mathlib.MeasureTheory.Integral.Pi

/-! Marking two external slots of one common Gaussian photon source.
The diagonal entries of the Hessian are actual second derivatives of the
shifted test polynomial. Zero-variance Gaussian coordinates are allowed. -/

noncomputable section

namespace UV.MarkedPhoton

open Filter MeasureTheory Real UV.VerifyCurvatureProductMoments
open scoped BigOperators

private instance baseProbability : IsProbabilityMeasure sourceGaussianBase := by
  rw [UV.ContinueCurvatureGaussian.sourceGaussianBase_eq_gaussianReal]
  infer_instance

private instance coordinateProbability (v : ℝ) : IsProbabilityMeasure (sourceGaussian v) :=
  Measure.isProbabilityMeasure_map (by fun_prop : AEMeasurable (fun x : ℝ => sqrt (2*v)*x) sourceGaussianBase)

private def moment (v : ℝ) (k : ℕ) := (Real.sqrt (2*v))^k * scalarPairMoment k

private theorem gaussian_moment (v : ℝ) (k : ℕ) : (∫ x : ℝ, x^k ∂sourceGaussian v) = moment v k := by
  rw [sourceGaussian, integral_map (by fun_prop) (by fun_prop)]
  simp only [mul_pow, integral_const_mul, scalarPairMoment_eq_integral, moment]

private theorem weighted_second_moment (v : ℝ) (hv : 0 ≤ v) (n : ℕ) :
    v * ((n:ℝ) * ((n-1:ℕ):ℝ)) * moment v (n-2) = (n:ℝ) * moment v n := by
  rcases n with _ | _ | k
  · simp
  · simp [moment, scalarPairMoment]
  · simp only [Nat.add_one_sub_one, moment, scalarPairMoment]
    rw [show (sqrt (2*v))^(k+2) = (sqrt (2*v))^k * (2*v) by rw [pow_add, sq_sqrt (by positivity)]]
    push_cast
    ring

variable {ι : Type*} [Fintype ι]

def coordinateLaw (v : ι → ℝ) : Measure (ι → ℝ) := Measure.pi (fun i => sourceGaussian (v i))

def monomial (ν : ι → ℕ) (x : ι → ℝ) : ℝ := ∏ i, x i ^ ν i

theorem monomial_integrable (v : ι → ℝ) (ν : ι → ℕ) : Integrable (monomial ν) (coordinateLaw v) :=
  Integrable.fintype_prod (fun i => sourceGaussian_power_integrable (v i) (ν i))

private theorem monomial_integral (v : ι → ℝ) (ν : ι → ℕ) :
    (∫ x, monomial ν x ∂coordinateLaw v) = ∏ i, moment (v i) (ν i) := by
  unfold coordinateLaw monomial
  rw [integral_fintype_prod_eq_prod (fun i => fun x : ℝ => x^(ν i))]
  simp_rw [gaussian_moment]

variable [DecidableEq ι]

private def otherPowers (ν : ι → ℕ) (x : ι → ℝ) (i : ι) := ∏ j ∈ Finset.univ.erase i, x j ^ ν j

private theorem monomial_slice (ν : ι → ℕ) (x : ι → ℝ) (i : ι) (t : ℝ) :
    monomial ν (Function.update x i t) = t^(ν i) * otherPowers ν x i := by
  unfold monomial otherPowers
  rw [← Finset.mul_prod_erase Finset.univ (fun j => Function.update x i t j ^ ν j) (Finset.mem_univ i), Function.update_self]
  congr 1
  exact Finset.prod_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.mem_erase.mp hj).1])

def diagonalHessian (V : (ι → ℝ) → ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  deriv (deriv (fun t => V (Function.update x i t))) (x i)

private theorem d_monomial_slice (ν : ι → ℕ) (x : ι → ℝ) (i : ι) (t : ℝ) :
    HasDerivAt (fun y => monomial ν (Function.update x i y))
      (((ν i : ℝ) * t^(ν i-1)) * otherPowers ν x i) t := by
  simp_rw [monomial_slice]
  exact (hasDerivAt_pow (ν i) t).mul_const _

private theorem dd_monomial_slice (ν : ι → ℕ) (x : ι → ℝ) (i : ι) (t : ℝ) :
    HasDerivAt (deriv (fun y => monomial ν (Function.update x i y)))
      (((ν i : ℝ)*((ν i-1:ℕ):ℝ))*t^(ν i-2)*otherPowers ν x i) t := by
  rw [show deriv (fun y => monomial ν (Function.update x i y)) = _ from funext fun y => (d_monomial_slice ν x i y).deriv]
  convert ((hasDerivAt_pow (ν i-1) t).const_mul (ν i : ℝ)).mul_const (otherPowers ν x i) using 1
  simp only [Nat.sub_sub]
  ring

private theorem diagonalHessian_monomial (ν : ι → ℕ) (x : ι → ℝ) (i : ι) :
    diagonalHessian (monomial ν) x i = ((ν i:ℝ)*((ν i-1:ℕ):ℝ)) * monomial (Function.update ν i (ν i-2)) x := by
  rw [diagonalHessian, (dd_monomial_slice ν x i (x i)).deriv]
  let η := Function.update ν i (ν i-2)
  have he : monomial η x = (x i)^(ν i-2) * otherPowers ν x i := by
    unfold monomial
    rw [← Finset.mul_prod_erase Finset.univ (fun j => x j ^ η j) (Finset.mem_univ i)]
    simp only [η, Function.update_self, otherPowers]
    congr 1
    exact Finset.prod_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.mem_erase.mp hj).1])
  change _ = _ * monomial η x
  rw [he]; ring

private theorem hessian_integrable (v : ι → ℝ) (ν : ι → ℕ) (i : ι) :
    Integrable (fun x => diagonalHessian (monomial ν) x i) (coordinateLaw v) := by
  simp_rw [diagonalHessian_monomial]
  exact (monomial_integrable v _).const_mul _

private theorem marked_coordinate (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) (ν : ι → ℕ) (i : ι) :
    v i * (∫ x, diagonalHessian (monomial ν) x i ∂coordinateLaw v) =
      (ν i : ℝ) * ∫ x, monomial ν x ∂coordinateLaw v := by
  simp_rw [diagonalHessian_monomial, integral_const_mul, monomial_integral]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => moment (v j) (Function.update ν i (ν i-2) j)) (Finset.mem_univ i),
      ← Finset.mul_prod_erase Finset.univ (fun j => moment (v j) (ν j)) (Finset.mem_univ i), Function.update_self]
  have hr : (∏ j ∈ Finset.univ.erase i, moment (v j) (Function.update ν i (ν i-2) j)) =
      ∏ j ∈ Finset.univ.erase i, moment (v j) (ν j) :=
    Finset.prod_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.mem_erase.mp hj).1])
  rw [hr]
  linear_combination (∏ j ∈ Finset.univ.erase i, moment (v j) (ν j)) * weighted_second_moment (v i) (hv i) (ν i)

/-- Each complete monomial contributes once for every possible first end of
the marked pair. The two derivatives act on the same polynomial. -/
theorem marked_monomial_trace (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) (ν : ι → ℕ) :
    (∑ i, v i * ∫ x, diagonalHessian (monomial ν) x i ∂coordinateLaw v) =
      (∑ i, ν i : ℕ) * (∫ x, monomial ν x ∂coordinateLaw v) := by
  simp_rw [marked_coordinate v hv ν]
  simp [Finset.sum_mul]

variable {J : Type*}

/-- A finite coordinate expansion allows signed kernels and repeated photon slots. -/
def photonPolynomial (s : Finset J) (c : J → ℝ) (ν : J → ι → ℕ) (x : ι → ℝ) : ℝ :=
  ∑ j ∈ s, c j * monomial (ν j) x

private theorem polynomial_hessian (s : Finset J) (c : J → ℝ) (ν : J → ι → ℕ) (x : ι → ℝ) (i : ι) :
    diagonalHessian (photonPolynomial s c ν) x i = ∑ j ∈ s, c j * diagonalHessian (monomial (ν j)) x i := by
  have hD : deriv (fun t => photonPolynomial s c ν (Function.update x i t)) = fun t =>
      ∑ j ∈ s, c j * deriv (fun y => monomial (ν j) (Function.update x i y)) t := by
    funext t
    apply HasDerivAt.deriv
    apply HasDerivAt.fun_sum
    exact fun j _ => ((d_monomial_slice (ν j) x i t).differentiableAt.hasDerivAt.const_mul (c j))
  rw [diagonalHessian, hD]
  apply HasDerivAt.deriv
  apply HasDerivAt.fun_sum
  exact fun j _ => (dd_monomial_slice (ν j) x i (x i)).differentiableAt.hasDerivAt.const_mul (c j)

/-- This is the ordinary two-entry Hessian in the Gaussian coordinates, with the
external source varying the same polynomial in each differentiation. -/
def measuredHessian (v : ι → ℝ) (V : (ι → ℝ) → ℝ) : Matrix ι ι ℝ := fun i j =>
  ∫ x, deriv (fun t => deriv (fun u => V (Function.update (Function.update x i t) j u))
    ((Function.update x i t) j)) (x i) ∂coordinateLaw v

private theorem measuredHessian_diag (v : ι → ℝ) (V : (ι → ℝ) → ℝ) (i : ι) :
    measuredHessian v V i i = ∫ x, diagonalHessian V x i ∂coordinateLaw v := by
  simp [measuredHessian, diagonalHessian, Function.update_idem]

/-- In Gaussian covariance coordinates this is an equality of the actual matrix
trace and the Gaussian expectation for every fixed homogeneous degree, including odd degrees. -/
theorem marked_polynomial_trace (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) (s : Finset J) (c : J → ℝ)
    (ν : J → ι → ℕ) (r : ℕ) (hν : ∀ j ∈ s, ∑ i, ν j i = r) :
    Matrix.trace (Matrix.diagonal v * measuredHessian v (photonPolynomial s c ν)) =
      (r : ℝ) * ∫ x, photonPolynomial s c ν x ∂coordinateLaw v := by
  unfold Matrix.trace
  simp only [Matrix.diag, Matrix.diagonal_mul, measuredHessian_diag, polynomial_hessian]
  have hi (j : J) (i : ι) := (hessian_integrable v (ν j) i).const_mul (c j)
  simp_rw [integral_finset_sum s (fun j _ => hi j _), integral_const_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold photonPolynomial
  rw [integral_finset_sum s (fun j _ => (monomial_integrable v (ν j)).const_mul (c j)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp_rw [mul_left_comm _ (c j), ← Finset.mul_sum, marked_monomial_trace v hv, integral_const_mul, hν j hj]
  ring

end UV.MarkedPhoton
