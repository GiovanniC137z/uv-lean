import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic

/-! Forward marks of a two-sided analytic pole assignment. The argument
uses continuity for the on-shell identity and exact determinant algebra
for the finite-probe test. -/

open Filter Matrix
open scoped Topology Matrix ComplexOrder

noncomputable section

namespace UV

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Two eigenblocks of the free Dirac inverse on the rest chart. -/
def diracRestPencil (m t : ℂ) (P : Matrix n n ℂ) : Matrix n n ℂ :=
  t • P + (2 * m - t) • (1 - P)

/-- The free inverse multiplied by the pole coordinate, extended at zero. -/
def diracRestRegularizer (m t : ℂ) (P : Matrix n n ℂ) : Matrix n n ℂ :=
  P + (t / (2 * m - t)) • (1 - P)

theorem dirac_rest_regularizer_mul (m t : ℂ) (P : Matrix n n ℂ)
    (hP : P * P = P) (ht : 2 * m - t ≠ 0) :
    diracRestRegularizer m t P * diracRestPencil m t P = t • 1 := by
  have hPQ : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  have hQP : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by rw [sub_mul, one_mul, hPQ, sub_zero]
  unfold diracRestRegularizer diracRestPencil
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, hP, hPQ,
    hQP, hQQ, smul_zero, zero_add, add_zero]
  rw [mul_comm (2 * m - t), div_mul_cancel₀ _ ht]
  rw [← smul_add]
  congr 1
  abel

/-- Analytic outer maps are continuous at the shell. Exact factorization on
its punctured neighborhood forces the residue of the core inverse to vanish. -/
theorem two_sided_pole_residue_zero (m : ℂ) (hm : m ≠ 0) (P : Matrix n n ℂ)
    (hP : P * P = P) (L K R : ℂ → Matrix n n ℂ)
    (hL : ContinuousAt L 0) (hK : ContinuousAt K 0) (hR : ContinuousAt R 0)
    (hK₀ : IsUnit (K 0).det)
    (hRunit : ∀ᶠ t in 𝓝[≠] (0 : ℂ), IsUnit (R t).det)
    (hbase : ∀ᶠ t in 𝓝[≠] (0 : ℂ), L t * K t * R t = diracRestPencil m t P) :
    R 0 * P * L 0 = 0 := by
  let B := fun t => diracRestRegularizer m t P
  have hd : 2 * m - 0 ≠ 0 := by simp [hm]
  have hden : ContinuousAt (fun t : ℂ => 2 * m - t) 0 :=
    continuousAt_const.sub continuousAt_id
  have hB : ContinuousAt B 0 := continuousAt_const.add
    ((continuousAt_id.div hden hd).smul continuousAt_const)
  have hB₀ : B 0 = P := by simp [B, diracRestRegularizer]
  let f := fun t => R t * B t * L t * K t
  have hf : ContinuousAt f 0 := ((hR.mul hB).mul hL).mul hK
  have hpunc : ∀ᶠ t in 𝓝[≠] (0 : ℂ), 2 * m - t ≠ 0 :=
    mem_nhdsWithin_of_mem_nhds (hden.eventually_ne hd)
  have heq : f =ᶠ[𝓝[≠] (0 : ℂ)] (fun t => t • (1 : Matrix n n ℂ)) := by
    filter_upwards [hbase, hRunit, hpunc] with t ht hr hd'
    have he : f t * R t = (t • (1 : Matrix n n ℂ)) * R t := by
      calc
        f t * R t = R t * (B t * (L t * K t * R t)) := by simp [f, mul_assoc]
        _ = R t * (t • (1 : Matrix n n ℂ)) := by rw [ht, dirac_rest_regularizer_mul m t P hP hd']
        _ = (t • (1 : Matrix n n ℂ)) * R t := by simp
    simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ hr] using
      congrArg (fun A : Matrix n n ℂ => A * (R t)⁻¹) he
  have hc₀ : ContinuousAt (fun t : ℂ => t • (1 : Matrix n n ℂ)) 0 :=
    continuousAt_id.smul continuousAt_const
  have hz := tendsto_nhds_unique hf.continuousWithinAt
    (hc₀.continuousWithinAt.congr' heq.symm)
  have hres : R 0 * P * L 0 * K 0 = 0 := by simpa [f, hB₀] using hz
  simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ hK₀, zero_mul] using
    congrArg (fun A : Matrix n n ℂ => A * (K 0)⁻¹) hres

omit [DecidableEq n] in
/-- The amputation products vanish for arbitrary core marks, hence for
any derivatives with respect to the external probe. -/
theorem on_shell_core_marks_mul_zero (P L R V V' : Matrix n n ℂ)
    (hP : P * P = P) (h : R * P * L = 0) :
    (P * L * V * R * P) * (P * L * V' * R * P) = 0 := by
  calc
    _ = (P * L * V) * (R * (P * P) * L) * (V' * R * P) := by simp only [mul_assoc]
    _ = 0 := by rw [hP, h, mul_zero, zero_mul]

omit [DecidableEq n] in
/-- A Hermitian forward core mark on the positive spin space is zero. -/
theorem hermitian_on_shell_core_mark_eq_zero (P L R V : Matrix n n ℂ)
    (hP : P * P = P) (h : R * P * L = 0)
    (hHerm : (P * L * V * R * P)ᴴ = (P * L * V * R * P)) :
    P * L * V * R * P = 0 := by
  apply Matrix.conjTranspose_mul_self_eq_zero.mp
  rw [hHerm, on_shell_core_marks_mul_zero P L R V V hP h]

omit [DecidableEq n] in
/-- In particular, the zero Hermitian core mark cannot be a nonzero charge
on a nontrivial pole projection. -/
theorem hermitian_on_shell_core_mark_ne_charge (P L R V : Matrix n n ℂ)
    (hP : P * P = P) (h : R * P * L = 0)
    (hHerm : (P * L * V * R * P)ᴴ = (P * L * V * R * P))
    {q : ℂ} (hq : q ≠ 0) (hp : P ≠ 0) : P * L * V * R * P ≠ q • P := by
  rw [hermitian_on_shell_core_mark_eq_zero P L R V hP h hHerm]
  exact Ne.symm (smul_ne_zero hq hp)

/-- The determinant at finite probe has the same zeros as the free
pencil when the core remains nonsingular. -/
theorem two_sided_pole_det_eq (D L K₀ K R : Matrix n n ℂ)
    (hD : D = L * K₀ * R) (hK : K₀.det ≠ 0) :
    (L * K * R).det = D.det * (K.det / K₀.det) := by
  rw [hD]
  simp only [Matrix.det_mul]
  field_simp

/-- A holomorphic finite probe with nonsingular core leaves the order of the
determinant zero unchanged on the same rest chart. -/
theorem two_sided_pole_order_eq (D L K₀ K R : ℂ → Matrix n n ℂ)
    (hD : ∀ᶠ t in 𝓝 (0 : ℂ), D t = L t * K₀ t * R t)
    (hK₀ : (K₀ 0).det ≠ 0) (hK : (K 0).det ≠ 0)
    (haD : AnalyticAt ℂ (fun t => (D t).det) 0)
    (haK₀ : AnalyticAt ℂ (fun t => (K₀ t).det) 0)
    (haK : AnalyticAt ℂ (fun t => (K t).det) 0) :
    analyticOrderAt (fun t => (L t * K t * R t).det) 0 =
      analyticOrderAt (fun t => (D t).det) 0 := by
  let d := fun t => (D t).det
  let u := fun t => (K t).det / (K₀ t).det
  have hu : AnalyticAt ℂ u 0 := haK.div haK₀ hK₀
  have horder : analyticOrderAt u 0 = 0 :=
    hu.analyticOrderAt_eq_zero.mpr (div_ne_zero hK hK₀)
  have hK₀near : ∀ᶠ t in 𝓝 (0 : ℂ), (K₀ t).det ≠ 0 :=
    haK₀.continuousAt.eventually_ne hK₀
  have heq : (fun t => (L t * K t * R t).det) =ᶠ[𝓝 (0 : ℂ)] d * u := by
    filter_upwards [hD, hK₀near] with t hDt hK₀t
    exact two_sided_pole_det_eq (D t) (L t) (K₀ t) (K t) (R t) hDt hK₀t
  rw [analyticOrderAt_congr heq, analyticOrderAt_mul haD hu, horder, add_zero]

end UV
