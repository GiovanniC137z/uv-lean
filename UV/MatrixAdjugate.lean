import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Holomorphy of the actual determinant and adjugate of a finite matrix
family, derived from their finite entry formulas. -/

noncomputable section
open scoped Matrix.Norms.Elementwise

namespace UV

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem matrix_det_analyticWithinAt {K : ℂ → Matrix n n ℂ} {s : Set ℂ} {p : ℂ}
    (hK : AnalyticWithinAt ℂ K s p) :
    AnalyticWithinAt ℂ (fun z => (K z).det) s p := by
  have he (i j : n) : AnalyticWithinAt ℂ (fun z => K z i j) s p :=
    analyticWithinAt_pi_iff.mp (analyticWithinAt_pi_iff.mp hK i) j
  simp_rw [Matrix.det_apply']
  apply Finset.analyticWithinAt_fun_sum
  intro σ _
  apply AnalyticWithinAt.mul analyticWithinAt_const
  exact Finset.analyticWithinAt_fun_prod _ (fun i _ => he (σ i) i)

theorem matrix_adjugate_analyticWithinAt {K : ℂ → Matrix n n ℂ} {s : Set ℂ} {p : ℂ}
    (hK : AnalyticWithinAt ℂ K s p) :
    AnalyticWithinAt ℂ (fun z => (K z).adjugate) s p := by
  apply AnalyticWithinAt.pi
  intro i
  apply AnalyticWithinAt.pi
  intro j
  change AnalyticWithinAt ℂ (fun z => (K z).adjugate i j) s p
  simp_rw [Matrix.adjugate_apply]
  apply matrix_det_analyticWithinAt
  apply AnalyticWithinAt.pi
  intro a
  apply AnalyticWithinAt.pi
  intro b
  by_cases hab : a = j
  · subst a
    simp only [Matrix.updateRow_self]
    exact analyticWithinAt_const
  · simpa only [Matrix.updateRow_apply, if_neg hab] using
      analyticWithinAt_pi_iff.mp (analyticWithinAt_pi_iff.mp hK a) b

theorem matrix_det_analyticAt {K : ℂ → Matrix n n ℂ} {p : ℂ}
    (hK : AnalyticAt ℂ K p) : AnalyticAt ℂ (fun z => (K z).det) p := by
  rw [← analyticWithinAt_univ] at hK ⊢
  exact matrix_det_analyticWithinAt hK

theorem matrix_adjugate_analyticAt {K : ℂ → Matrix n n ℂ} {p : ℂ}
    (hK : AnalyticAt ℂ K p) : AnalyticAt ℂ (fun z => (K z).adjugate) p := by
  rw [← analyticWithinAt_univ] at hK ⊢
  exact matrix_adjugate_analyticWithinAt hK

theorem matrix_det_analyticOnNhd {K : ℂ → Matrix n n ℂ} {s : Set ℂ}
    (hK : AnalyticOnNhd ℂ K s) : AnalyticOnNhd ℂ (fun z => (K z).det) s :=
  fun _ hz => matrix_det_analyticAt (hK _ hz)

theorem matrix_adjugate_analyticOnNhd {K : ℂ → Matrix n n ℂ} {s : Set ℂ}
    (hK : AnalyticOnNhd ℂ K s) : AnalyticOnNhd ℂ (fun z => (K z).adjugate) s :=
  fun _ hz => matrix_adjugate_analyticAt (hK _ hz)

theorem matrix_det_differentiableOn {K : ℂ → Matrix n n ℂ} {s : Set ℂ}
    (hK : AnalyticOnNhd ℂ K s) : DifferentiableOn ℂ (fun z => (K z).det) s :=
  fun _ hz => (matrix_det_analyticAt (hK _ hz)).differentiableAt.differentiableWithinAt

theorem matrix_adjugate_differentiableOn {K : ℂ → Matrix n n ℂ} {s : Set ℂ}
    (hK : AnalyticOnNhd ℂ K s) : DifferentiableOn ℂ (fun z => (K z).adjugate) s :=
  fun _ hz => (matrix_adjugate_analyticAt (hK _ hz)).differentiableAt.differentiableWithinAt

omit [DecidableEq n] in
/-- Matrix multiplication is analytic for rectangular finite matrix families,
proved entrywise from its actual finite sums. -/
theorem matrix_mul_analyticWithinAt {m l : Type*} [Fintype m] [Fintype l]
    {A : ℂ → Matrix m n ℂ} {B : ℂ → Matrix n l ℂ} {s : Set ℂ} {p : ℂ}
    (hA : AnalyticWithinAt ℂ A s p) (hB : AnalyticWithinAt ℂ B s p) :
    AnalyticWithinAt ℂ (fun z => A z * B z) s p := by
  apply AnalyticWithinAt.pi
  intro i
  apply AnalyticWithinAt.pi
  intro j
  change AnalyticWithinAt ℂ (fun z => (A z * B z) i j) s p
  simp_rw [Matrix.mul_apply]
  apply Finset.analyticWithinAt_fun_sum
  intro k _
  exact (analyticWithinAt_pi_iff.mp (analyticWithinAt_pi_iff.mp hA i) k).mul
    (analyticWithinAt_pi_iff.mp (analyticWithinAt_pi_iff.mp hB k) j)

omit [DecidableEq n] in
theorem matrix_mul_analyticAt {m l : Type*} [Fintype m] [Fintype l]
    {A : ℂ → Matrix m n ℂ} {B : ℂ → Matrix n l ℂ} {p : ℂ}
    (hA : AnalyticAt ℂ A p) (hB : AnalyticAt ℂ B p) :
    AnalyticAt ℂ (fun z => A z * B z) p := by
  rw [← analyticWithinAt_univ] at hA hB ⊢
  exact matrix_mul_analyticWithinAt hA hB

omit [DecidableEq n] in
theorem matrix_mul_analyticOnNhd {m l : Type*} [Fintype m] [Fintype l]
    {A : ℂ → Matrix m n ℂ} {B : ℂ → Matrix n l ℂ} {s : Set ℂ}
    (hA : AnalyticOnNhd ℂ A s) (hB : AnalyticOnNhd ℂ B s) :
    AnalyticOnNhd ℂ (fun z => A z * B z) s :=
  fun z hz => matrix_mul_analyticAt (hA z hz) (hB z hz)

end UV
