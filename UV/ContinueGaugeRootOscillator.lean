import UV.ContinueGaugeRootLandau
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Exact Hermite oscillator modes of the scalar magnetic fibre, in the
physical wave-number coordinate of the constant Cartan field. -/

noncomputable section
open Polynomial Real MeasureTheory

namespace UV.RootMagnetic

def rootHermite (n : ℕ) : Polynomial ℝ := (hermite n).map (Int.castRingHom ℝ)

@[simp] theorem rootHermite_zero : rootHermite 0 = 1 := by simp [rootHermite]

theorem rootHermite_succ (n : ℕ) : rootHermite (n+1) = X * rootHermite n - (rootHermite n).derivative := by
  simp [rootHermite,hermite_succ,derivative_map]

theorem rootHermite_derivative (n : ℕ) : (rootHermite (n+1)).derivative = C ((n:ℝ)+1)*rootHermite n := by
  induction n with
  | zero => simp [rootHermite_succ]
  | succ n ih =>
    rw [rootHermite_succ (n+1),derivative_sub,derivative_mul,derivative_X,one_mul,ih,
      derivative_mul,derivative_C,zero_mul,zero_add,rootHermite_succ n]
    push_cast
    simp only [map_add,map_one]
    ring

theorem rootHermite_eqn (n : ℕ) : (rootHermite n).derivative.derivative - X*(rootHermite n).derivative =
    -C (n:ℝ)*rootHermite n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [rootHermite_derivative,derivative_mul,derivative_C,zero_mul,zero_add,rootHermite_succ]
    push_cast
    ring

private def rootFiberGauss (b x : ℝ) := Real.exp (-b*x^2/2)
private def rootFiberArgument (b x : ℝ) := Real.sqrt (2*b)*x
def rootFiberMode (b : ℝ) (n : ℕ) (x : ℝ) :=
  (rootHermite n).eval (rootFiberArgument b x) * rootFiberGauss b x

private theorem rootFiber_poly_deriv (p : Polynomial ℝ) (b x : ℝ) :
    HasDerivAt (fun y => p.eval (rootFiberArgument b y))
      (p.derivative.eval (rootFiberArgument b x)*Real.sqrt (2*b)) x := by
  apply (p.hasDerivAt _).comp x
  change HasDerivAt (fun y : ℝ => Real.sqrt (2*b)*y) _ x
  simpa only [mul_one,id_eq] using (hasDerivAt_id x).const_mul (Real.sqrt (2*b))

private theorem rootFiber_gauss_deriv (b x : ℝ) :
    HasDerivAt (rootFiberGauss b) ((-b*x)*rootFiberGauss b x) x := by
  have h := ((((hasDerivAt_pow 2 x).const_mul (-b)).div_const 2).exp)
  convert h using 1
  dsimp [rootFiberGauss]
  ring

private theorem rootFiber_deriv (b : ℝ) (n : ℕ) (x : ℝ) :
    deriv (rootFiberMode b n) x = (rootHermite n).derivative.eval (rootFiberArgument b x) *
      Real.sqrt (2*b)*rootFiberGauss b x +
      (rootHermite n).eval (rootFiberArgument b x)*((-b*x)*rootFiberGauss b x) :=
  ((rootFiber_poly_deriv (rootHermite n) b x).mul (rootFiber_gauss_deriv b x)).deriv

/-- The actual Schrödinger differential expression yields the Landau
level (2n+1)b at every point, for every positive absolute field b. -/
theorem rootFiberMode_eigen (b : ℝ) (hb : 0 < b) (n : ℕ) (x : ℝ) :
    -(deriv (deriv (rootFiberMode b n)) x) + (b*x)^2 * rootFiberMode b n x =
      ((2*(n:ℝ)+1)*b)*rootFiberMode b n x := by
  let p := rootHermite n
  let z := rootFiberArgument b x
  let c := Real.sqrt (2*b)
  let g := rootFiberGauss b x
  have h1 := (((rootFiber_poly_deriv p.derivative b x).mul_const c).mul (rootFiber_gauss_deriv b x))
  have h2 := (rootFiber_poly_deriv p b x).mul (((hasDerivAt_id x).const_mul (-b)).mul (rootFiber_gauss_deriv b x))
  have hdd : deriv (deriv (rootFiberMode b n)) x =
      p.derivative.derivative.eval z*c*c*g + (p.derivative.eval z*c)*(-b*x*g) +
        (p.derivative.eval z*c*((-b*x)*g) + p.eval z*(((-b)*1)*g+((-b)*x)*((-b*x)*g))) := by
    rw [funext (rootFiber_deriv b n)]
    exact (h1.add h2).deriv
  rw [hdd]
  have hpoly := congrArg (fun q : Polynomial ℝ => q.eval z) (rootHermite_eqn n)
  simp only [eval_sub,eval_mul,eval_neg,eval_X,eval_C] at hpoly
  change p.derivative.derivative.eval z-z*p.derivative.eval z = _ at hpoly
  have hc2 : c^2 = 2*b := Real.sq_sqrt (by positivity)
  change -(p.derivative.derivative.eval z*c*c*g + (p.derivative.eval z*c)*(-b*x*g) +
    (p.derivative.eval z*c*((-b*x)*g) + p.eval z*(((-b)*1)*g+((-b)*x)*((-b*x)*g)))) +
      (b*x)^2*(p.eval z*g) = _*(p.eval z*g)
  change p.derivative.derivative.eval z-c*x*p.derivative.eval z = -(n:ℝ)*p.eval z at hpoly
  rw [show p.derivative.derivative.eval z*c*c*g = p.derivative.derivative.eval z*(2*b)*g by rw [←hc2]; ring]
  linear_combination -2*b*g*hpoly

end UV.RootMagnetic
