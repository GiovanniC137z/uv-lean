import UV.MarkedPhotonMonomial
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Gaussian integration by parts on finite coordinate polynomials,
including singular diagonal Gaussians. -/

noncomputable section
open MeasureTheory MvPolynomial Real
open UV.VerifyCurvatureProductMoments

namespace UV.MarkedPhoton

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def osGaussMoment (v : ℝ) (k : ℕ) := (sqrt (2*v))^k * scalarPairMoment k

private theorem osGaussMoment_eq (v : ℝ) (k : ℕ) :
    (∫ x : ℝ, x^k ∂sourceGaussian v) = osGaussMoment v k := by
  rw [sourceGaussian,integral_map (by fun_prop) (by fun_prop)]
  simp only [mul_pow,integral_const_mul,scalarPairMoment_eq_integral,osGaussMoment]

private theorem osGaussMoment_step {v : ℝ} (hv : 0 ≤ v) (n : ℕ) :
    osGaussMoment v (1+n) = v*(n:ℝ)*osGaussMoment v (n-1) := by
  cases n with
  | zero => simp [osGaussMoment,scalarPairMoment]
  | succ k =>
    rw [show 1+k.succ = k+2 by omega]
    simp only [osGaussMoment,scalarPairMoment,Nat.succ_sub_one,Nat.cast_succ]
    rw [pow_add,sq_sqrt (by positivity)]
    ring

omit [DecidableEq ι] in
private theorem osPolynomial_monomial_eval (q : ι →₀ ℕ) (a : ℝ) (z : ι → ℝ) :
    eval z (MvPolynomial.monomial q a) = a * monomial q z := by
  rw [eval_monomial,q.prod_fintype _ (fun _ => pow_zero _)]
  rfl

omit [DecidableEq ι] in
theorem osPolynomial_integrable (v : ι → ℝ) (p : MvPolynomial ι ℝ) :
    Integrable (fun z => eval z p) (coordinateLaw v) := by
  induction p using MvPolynomial.induction_on' with
  | monomial q a =>
    simp_rw [osPolynomial_monomial_eval]
    exact (monomial_integrable v q).const_mul _
  | add p q hp hq =>
    simpa only [map_add] using hp.add hq

omit [DecidableEq ι] in
private theorem osPolynomial_monomial_mean (v : ι → ℝ) (q : ι →₀ ℕ) (a : ℝ) :
    (∫ z, eval z (MvPolynomial.monomial q a) ∂coordinateLaw v) = a * ∏ j, osGaussMoment (v j) (q j) := by
  simp_rw [osPolynomial_monomial_eval,monomial,integral_const_mul,coordinateLaw,
    integral_fintype_prod_eq_prod (fun j => fun x : ℝ => x^(q j)),osGaussMoment_eq]

/-- The Stein identity for each coordinate of an arbitrary finite
real polynomial. A zero eigenvalue makes both sides vanish. -/
theorem osPolynomial_stein (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) (i : ι) (p : MvPolynomial ι ℝ) :
    (∫ z, eval z (X i * p) ∂coordinateLaw v) = v i * ∫ z, eval z (pderiv i p) ∂coordinateLaw v := by
  induction p using MvPolynomial.induction_on' with
  | monomial q a =>
    rw [X,MvPolynomial.monomial_mul,one_mul,MvPolynomial.pderiv_monomial,
      osPolynomial_monomial_mean,osPolynomial_monomial_mean]
    rw [←Finset.mul_prod_erase Finset.univ (fun j => osGaussMoment (v j) ((Finsupp.single i 1+q : ι →₀ ℕ) j)) (Finset.mem_univ i),
      ←Finset.mul_prod_erase Finset.univ (fun j => osGaussMoment (v j) ((q-Finsupp.single i 1 : ι →₀ ℕ) j)) (Finset.mem_univ i)]
    simp only [Finsupp.add_apply,Finsupp.tsub_apply,Finsupp.single_eq_same,osGaussMoment_step (hv i)]
    have he : (∏ j ∈ Finset.univ.erase i, osGaussMoment (v j) (Finsupp.single i 1 j + q j)) =
        ∏ j ∈ Finset.univ.erase i, osGaussMoment (v j) (q j - Finsupp.single i 1 j) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hj)]
      simp
    rw [he]
    ring
  | add p q hp hq =>
    simp only [mul_add,map_add]
    rw [integral_add (osPolynomial_integrable v (X i*p)) (osPolynomial_integrable v (X i*q)),
      integral_add (osPolynomial_integrable v (pderiv i p)) (osPolynomial_integrable v (pderiv i q)),hp,hq,mul_add]

end UV.MarkedPhoton
