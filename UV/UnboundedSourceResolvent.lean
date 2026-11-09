import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

/-! A maximality criterion for densely defined symmetric operators. The
surjectivity of both imaginary resolvents forces the actual adjoint domain,
rather than assuming a self-adjoint domain identity. -/

noncomputable section
open scoped InnerProductSpace ComplexConjugate

namespace UV

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- One onto imaginary resolvent already forces a symmetric operator's
domain to be dense. Density is a consequence of the operator data. -/
theorem unbounded_dense_of_imaginary_resolvent
    (T : H →ₗ.[ℂ] H) (hSym : T.IsFormalAdjoint T)
    (hPlus : Function.Surjective (fun x : T.domain => T x + Complex.I • (x : H))) :
    Dense (T.domain : Set H) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply eq_bot_iff.mpr
  intro y hy
  have horth := (Submodule.mem_orthogonal T.domain y).mp hy
  obtain ⟨x, hx⟩ := hPlus y
  change T x + Complex.I • (x : H) = y at hx
  have hconj : starRingEnd ℂ ⟪(x : H), T x⟫_ℂ = ⟪(x : H), T x⟫_ℂ := by
    rw [inner_conj_symm]
    exact hSym x x
  have him : (⟪(x : H), T x⟫_ℂ).im = 0 := by
    have he := congrArg Complex.im hconj
    simp only [Complex.conj_im] at he
    linarith
  have hxy := horth (x : H) x.property
  rw [← hx, inner_add_right, inner_smul_right] at hxy
  have hnorm : ‖(x : H)‖ ^ 2 = 0 := by
    have he := congrArg Complex.im hxy
    simp only [Complex.add_im, him, Complex.I_mul_im, zero_add, Complex.zero_im] at he
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) (x : H)).trans he
  have hxzero : (x : H) = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  have hxzero' : x = 0 := Subtype.ext hxzero
  change y = 0
  simpa only [hxzero', LinearPMap.map_zero, Submodule.coe_zero, smul_zero, add_zero]
    using hx.symm

/-- A dense symmetric operator with both imaginary resolvents onto is
self-adjoint as a partially defined operator, including domain equality. -/
theorem unbounded_selfAdjoint_of_imaginary_resolvents
    (T : H →ₗ.[ℂ] H) (hDense : Dense (T.domain : Set H))
    (hSym : T.IsFormalAdjoint T)
    (hPlus : Function.Surjective (fun x : T.domain => T x + Complex.I • (x : H)))
    (hMinus : Function.Surjective (fun x : T.domain => T x - Complex.I • (x : H))) :
    IsSelfAdjoint T := by
  have hle : T ≤ T.adjoint := hSym.le_adjoint hDense
  have hAdj : T.adjoint ≤ T := by
    refine ⟨?_, ?_⟩
    · intro y hy
      let y' : T.adjoint.domain := ⟨y, hy⟩
      obtain ⟨x, hx⟩ := hPlus (T.adjoint y' + Complex.I • y)
      have hrel : T.adjoint y' - T x = Complex.I • ((x : H)-y) := by
        have hz : T.adjoint y' = T x + Complex.I • (x : H) - Complex.I • y :=
          eq_sub_of_add_eq hx.symm
        rw [hz, smul_sub]
        abel
      have horth : ∀ v : T.domain, ⟪y-(x : H), T v-Complex.I • (v : H)⟫_ℂ = 0 := by
        intro v
        have hfirst : ⟪y-(x : H), T v⟫_ℂ = Complex.I * ⟪y-(x : H), (v : H)⟫_ℂ := by
          calc
            _ = ⟪T.adjoint y' - T x, (v : H)⟫_ℂ := by
              rw [inner_sub_left, inner_sub_left,
                LinearPMap.adjoint_isFormalAdjoint hDense y' v, hSym x v]
            _ = _ := by
              rw [hrel, inner_smul_left]
              simp only [Complex.conj_I, inner_sub_left]
              ring
        rw [inner_sub_right, inner_smul_right, hfirst, sub_self]
      obtain ⟨v, hv⟩ := hMinus (y-(x : H))
      have hzero : y-(x : H) = 0 := by
        have hself : ⟪y-(x : H), y-(x : H)⟫_ℂ = 0 := by
          simpa only [hv] using horth v
        exact (inner_self_eq_zero (𝕜 := ℂ)).mp hself
      have hyx : y = (x : H) := sub_eq_zero.mp hzero
      exact hyx ▸ x.property
    · intro y z hyz
      exact (hle.2 hyz.symm).symm
  exact LinearPMap.isSelfAdjoint_def.mpr (le_antisymm hAdj hle)

/-- Both onto imaginary resolvents and symmetry imply full self-adjointness
without an independently assumed density statement. -/
theorem unbounded_selfAdjoint_of_imaginary_resolvents'
    (T : H →ₗ.[ℂ] H) (hSym : T.IsFormalAdjoint T)
    (hPlus : Function.Surjective (fun x : T.domain => T x + Complex.I • (x : H)))
    (hMinus : Function.Surjective (fun x : T.domain => T x - Complex.I • (x : H))) :
    IsSelfAdjoint T :=
  unbounded_selfAdjoint_of_imaginary_resolvents T
    (unbounded_dense_of_imaginary_resolvent T hSym hPlus) hSym hPlus hMinus

end UV
