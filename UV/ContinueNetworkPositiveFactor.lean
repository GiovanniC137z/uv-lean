import UV.ContinueNetworkDirectional
import Mathlib.Analysis.InnerProductSpace.Positive

/-! The actual positive-semidefinite quadratic form in the directional
theorem factors as (A^*A) in real Euclidean coordinates. Zero
eigenvalues are kept, so the factor has exactly the original kernel. -/

noncomputable section
open scoped BigOperators InnerProductSpace

namespace UV

variable {d : ℕ}

/-- The PSD form factors through a continuous Euclidean row map with
the same kernel. The equality is bilinear before specialization to
the quadratic form. -/
theorem directionalQuadratic_positive_factor
    (Q : DirectionalMomentum d →L[ℝ] DirectionalMomentum d)
    (hSym : ∀ x y, inner ℝ x (Q y) = inner ℝ y (Q x))
    (hPSD : ∀ x, 0 ≤ inner ℝ x (Q x)) :
    ∃ A : DirectionalMomentum d →L[ℝ] DirectionalMomentum d,
      Q = A.adjoint.comp A ∧
      (∀ x y, inner ℝ x (Q y) = inner ℝ (A x) (A y)) ∧
      (∀ x, ‖A x‖^2 = inner ℝ x (Q x)) ∧
      (∀ x, A x = 0 ↔ Q x = 0) := by
  have hp : Q.toLinearMap.IsPositive := by
    constructor
    · intro x y
      change inner ℝ (Q x) y = inner ℝ x (Q y)
      rw [real_inner_comm y (Q x)]
      exact (hSym x y).symm
    · intro x
      change 0 ≤ inner ℝ (Q x) x
      simpa only [real_inner_comm x (Q x)] using hPSD x
  have hn : Module.finrank ℝ (DirectionalMomentum d) = d := by
    simp [DirectionalMomentum, finrank_euclideanSpace]
  let B := hp.isSymmetric.eigenvectorBasis hn
  let ev := hp.isSymmetric.eigenvalues hn
  have hev (i : Fin d) : 0 ≤ ev i := hp.nonneg_eigenvalues hn i
  let A₀ : DirectionalMomentum d →ₗ[ℝ] DirectionalMomentum d :=
    { toFun := fun x => WithLp.toLp 2 (fun i => Real.sqrt (ev i) * B.repr x i)
      map_add' := by
        intro x y
        ext i
        simp only [map_add, PiLp.toLp_apply, PiLp.add_apply, mul_add]
      map_smul' := by
        intro r x
        ext i
        simp only [map_smul, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  let A := A₀.toContinuousLinearMap
  have hA (x : DirectionalMomentum d) (i : Fin d) :
      A x i = Real.sqrt (ev i) * B.repr x i := rfl
  have hQ (x : DirectionalMomentum d) (i : Fin d) :
      B.repr (Q x) i = ev i * B.repr x i :=
    hp.isSymmetric.eigenvectorBasis_apply_self_apply hn x i
  have hB (x y : DirectionalMomentum d) : inner ℝ x (Q y) = inner ℝ (A x) (A y) := by
    rw [← B.repr.inner_map_map x (Q y)]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, hA, hQ]
    apply Finset.sum_congr rfl
    intro i _
    have hs := Real.sq_sqrt (hev i)
    calc
      _ = (Real.sqrt (ev i))^2 * (B.repr y i) * (B.repr x i) := by rw [hs]
      _ = _ := by ring
  have hOp : Q = A.adjoint.comp A := by
    apply ContinuousLinearMap.ext
    intro y
    apply ext_inner_left ℝ
    intro x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
    exact hB x y
  have hsq (x : DirectionalMomentum d) : ‖A x‖^2 = inner ℝ x (Q x) := by
    rw [← real_inner_self_eq_norm_sq, hB]
  refine ⟨A,hOp,hB,hsq,fun x => ?_⟩
  constructor
  · intro h
    rw [hOp, ContinuousLinearMap.comp_apply, h, map_zero]
  · intro h
    exact norm_eq_zero.mp (by simpa [h] using hsq x)

def directionalFactorRow (A : DirectionalMomentum d →L[ℝ] DirectionalMomentum d)
    (i : Fin d) : DirectionalMomentum d →L[ℝ] ℝ :=
  (PiLp.proj 2 (fun _ : Fin d => ℝ) i).comp A

/-- The precision contribution is the exact sum of squares of the
individual scalar rows, with no further comparison constant. -/
theorem directionalFactorRow_norm_sq (A : DirectionalMomentum d →L[ℝ] DirectionalMomentum d)
    (x : DirectionalMomentum d) :
    ‖A x‖^2 = ∑ i, (directionalFactorRow A i x)^2 := by
  simp only [EuclideanSpace.norm_sq_eq, directionalFactorRow, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply, Real.norm_eq_abs, sq_abs]

theorem directionalFactorRow_common_kernel
    (A : DirectionalMomentum d →L[ℝ] DirectionalMomentum d) (x : DirectionalMomentum d) :
    (∀ i, directionalFactorRow A i x = 0) ↔ A x = 0 := by
  constructor
  · intro h
    ext i
    exact h i
  · intro h i
    simp [directionalFactorRow, h]

end UV
