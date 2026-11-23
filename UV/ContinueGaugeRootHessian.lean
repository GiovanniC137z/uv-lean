import UV.RootMagneticResponse
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Second variation of the five-component curvature and background
Feynman gauge term. The covariant integration-by-parts and adjoint
curvature identities are exposed separately. -/

noncomputable section
open Filter
open scoped InnerProductSpace BigOperators ContDiff

namespace UV.RootMagnetic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def rootCurvaturePoly (F L Q : E) : Polynomial ℝ := Polynomial.C (‖F‖^2) + Polynomial.C (2*⟪F,L⟫_ℝ)*Polynomial.X +
    Polynomial.C (‖L‖^2+2*⟪F,Q⟫_ℝ)*Polynomial.X^2 + Polynomial.C (2*⟪L,Q⟫_ℝ)*Polynomial.X^3 +
    Polynomial.C (‖Q‖^2)*Polynomial.X^4

private theorem rootCurvaturePoly_eval (F L Q : E) (t : ℝ) :
    ‖F+t • L+t^2 • Q‖^2 = (rootCurvaturePoly F L Q).eval t := by
  have hp (t : ℝ) : ‖F + t • L + t^2 • Q‖^2 =
      ‖F‖^2 + 2*⟪F,L⟫_ℝ*t + (‖L‖^2+2*⟪F,Q⟫_ℝ)*t^2 + 2*⟪L,Q⟫_ℝ*t^3 + ‖Q‖^2*t^4 := by
    rw [←real_inner_self_eq_norm_sq]
    simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq]
    rw [real_inner_comm L F,real_inner_comm Q F,real_inner_comm Q L]
    simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    ring
  simp only [hp,rootCurvaturePoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_X]

private theorem rootCurvaturePoly_second (F L Q : E) :
    (rootCurvaturePoly F L Q).derivative.derivative.eval 0 = 2*‖L‖^2+4*⟪F,Q⟫_ℝ := by
  simp [rootCurvaturePoly,Polynomial.derivative_mul,Polynomial.derivative_pow]
  ring

/-- The map in the linear curvature variation, with the normal component
included in the five-dimensional one-form. -/
def rootLinearCurvature (D : Fin 5 → E →ₗ[ℝ] E) (a : Fin 5 → E) (i j : Fin 5) : E :=
  D i (a j)-D j (a i)

/-- The gauge-fixed second variation before integration by parts. The last
sum is the contribution of the nonlinear commutator in the curvature. -/
def rootFeynmanForm (D : Fin 5 → E →ₗ[ℝ] E) (a : Fin 5 → E) (curv : Fin 5 → Fin 5 → E → E) : ℝ :=
  (∑ i, ∑ j, ‖rootLinearCurvature D a i j‖^2)/2 +
    ‖∑ i, D i (a i)‖^2 + ∑ i, ∑ j, ⟪curv i j (a i),a j⟫_ℝ

/-- Local root-vector Hessian on the common covariant test core. -/
def rootVectorHessian (D : Fin 5 → E →ₗ[ℝ] E) (curv : Fin 5 → Fin 5 → E → E)
    (a : Fin 5 → E) (j : Fin 5) : E :=
  ∑ i, (-(D i (D i (a j))) - (2:ℝ) • curv j i (a i))

theorem root_feynman_hessian (D : Fin 5 → E →ₗ[ℝ] E) (curv : Fin 5 → Fin 5 → E → E)
    (hD : ∀ i x y, ⟪D i x,y⟫_ℝ = -⟪x,D i y⟫_ℝ)
    (hF : ∀ i j x, D i (D j x) - D j (D i x) = curv i j x) (a : Fin 5 → E) :
    rootFeynmanForm D a curv = ∑ j, ⟪a j,rootVectorHessian D curv a j⟫_ℝ := by
  let A (i j : Fin 5) := ‖D i (a j)‖^2
  let B (i j : Fin 5) := ⟪D i (a j),D j (a i)⟫_ℝ
  let G (i j : Fin 5) := ⟪D j (a j),D i (a i)⟫_ℝ
  let R (i j : Fin 5) := ⟪curv i j (a i),a j⟫_ℝ
  have hL (i j : Fin 5) : ‖rootLinearCurvature D a i j‖^2 = A i j + A j i - 2*B i j := by
    simp only [rootLinearCurvature,norm_sub_sq_real,A,B]
    ring
  have hswap : (∑ i, ∑ j, A j i) = ∑ i, ∑ j, A i j := Finset.sum_comm
  have hG : ‖∑ i, D i (a i)‖^2 = ∑ i,∑ j, G i j := by
    rw [←real_inner_self_eq_norm_sq]
    simp only [inner_sum,sum_inner,G]
  have hcurv (i j : Fin 5) : curv j i (a i) = -(curv i j (a i)) := by
    rw [←hF,←hF,neg_sub]
  have hone (i j : Fin 5) :
      A i j - B i j + G i j + R i j =
        ⟪a j, -(D i (D i (a j))) - (2:ℝ) • curv j i (a i)⟫_ℝ := by
    have hA : A i j = -⟪a j,D i (D i (a j))⟫_ℝ := by
      change ‖D i (a j)‖^2 = _
      rw [←real_inner_self_eq_norm_sq,hD]
    have hR : R i j = ⟪a j,curv i j (a i)⟫_ℝ := real_inner_comm _ _
    dsimp only [B,G]
    rw [hA,hD i,hD j,hR,hcurv,inner_sub_right,inner_neg_right,real_inner_smul_right,inner_neg_right,←hF,inner_sub_right]
    ring
  unfold rootFeynmanForm rootVectorHessian
  conv_lhs => simp only [hL,Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,hswap,hG]
  simp only [inner_sum]
  rw [Finset.sum_comm (f := fun j i => ⟪a j, -(D i (D i (a j))) - (2:ℝ) • curv j i (a i)⟫_ℝ)]
  simp_rw [←hone,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  change _ + ∑ i,∑ j, R i j = _
  ring

/-- Bare curvature action along a straight potential variation, including
the background-covariant Feynman gauge-fixing term. -/
def rootGaugeAction (F : Fin 5 → Fin 5 → E) (bracket : E → E → E)
    (D : Fin 5 → E →ₗ[ℝ] E) (a : Fin 5 → E) (t : ℝ) : ℝ :=
  (1/4 : ℝ)*(∑ i,∑ j, ‖F i j + t • rootLinearCurvature D a i j + t^2 • bracket (a i) (a j)‖^2) +
    (‖∑ i, D i (a i)‖^2/2)*t^2

/-- Actual second derivative of the action is the quadratic form of
the covariant vector Hessian. Curvature of the background covariant
derivative and invariance of the adjoint pairing are distinct inputs. -/
theorem root_action_hessian (F : Fin 5 → Fin 5 → E) (bracket : E → E → E)
    (D : Fin 5 → E →ₗ[ℝ] E) (a : Fin 5 → E) (curv : Fin 5 → Fin 5 → E → E)
    (hD : ∀ i x y, ⟪D i x,y⟫_ℝ = -⟪x,D i y⟫_ℝ)
    (hF : ∀ i j x, D i (D j x)-D j (D i x) = curv i j x)
    (hpair : ∀ i j x y, ⟪F i j,bracket x y⟫_ℝ = ⟪curv i j x,y⟫_ℝ) :
    deriv (deriv (rootGaugeAction F bracket D a)) 0 = ∑ j, ⟪a j,rootVectorHessian D curv a j⟫_ℝ := by
  let p (i j : Fin 5) := rootCurvaturePoly (F i j) (rootLinearCurvature D a i j) (bracket (a i) (a j))
  let k := ‖∑ i, D i (a i)‖^2/2
  let P : Polynomial ℝ := Polynomial.C (1/4:ℝ)*(∑ i,∑ j, p i j) + Polynomial.C k * Polynomial.X^2
  have he (t : ℝ) : rootGaugeAction F bracket D a t = P.eval t := by
    simp only [rootGaugeAction,P,p,k,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_finset_sum,rootCurvaturePoly_eval]
  rw [funext he, show deriv (fun t => P.eval t) = _ from funext (fun t => P.deriv (x := t)),P.derivative.deriv]
  rw [←root_feynman_hessian D curv hD hF a]
  simp [P,Polynomial.derivative_mul,Polynomial.derivative_pow,
    Polynomial.eval_finset_sum,p,rootCurvaturePoly_second,hpair,rootFeynmanForm,k,
    Finset.sum_add_distrib,←Finset.mul_sum]
  ring

end UV.RootMagnetic
