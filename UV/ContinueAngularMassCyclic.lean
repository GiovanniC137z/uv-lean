import UV.ContinueAngularMassEigen

/-! Algebraic cyclicity of the constant zonal mode. Every coordinate mode is
a finite polynomial in the tridiagonal action applied to the zeroth mode. -/

noncomputable section
open Set
namespace UV

def angularJacobiMap : (ℕ → ℝ) →ₗ[ℝ] (ℕ → ℝ) where
  toFun := angularJacobiRow
  map_add' f g := by ext j; cases j <;> simp [angularJacobiRow] <;> ring
  map_smul' c f := by ext j; cases j <;> simp [angularJacobiRow] <;> ring

def angularZonalMode (j k : ℕ) : ℝ := if k=j then 1 else 0

def angularCyclicSpan := Submodule.span ℝ (range (fun k : ℕ => (angularJacobiMap^k) (angularZonalMode 0)))

private theorem angular_mode_step_zero :
    angularJacobiMap (angularZonalMode 0) = angularJacobiEdge 0 • angularZonalMode 1 := by
  funext k
  cases k with
  | zero => simp [angularJacobiMap,angularJacobiRow,angularZonalMode]
  | succ k =>
    simp [angularJacobiMap,angularJacobiRow,angularZonalMode,eq_comm]
    split_ifs <;> simp_all

private theorem angular_mode_step (j : ℕ) :
    angularJacobiMap (angularZonalMode (j+1)) =
      angularJacobiEdge j • angularZonalMode j + angularJacobiEdge (j+1) • angularZonalMode (j+2) := by
  funext k
  cases k with
  | zero => by_cases h : j=0 <;> simp [angularJacobiMap,angularJacobiRow,angularZonalMode,h,eq_comm]
  | succ k =>
    change angularJacobiEdge k*angularZonalMode (j+1) k + angularJacobiEdge (k+1)*angularZonalMode (j+1) (k+2) = _
    simp only [angularZonalMode,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    have h₁ : k+2=j+1 ↔ k+1=j := by omega
    have h₂ : k+1=j+2 ↔ k=j+1 := by omega
    simp only [h₁,h₂]
    by_cases ha : k+1=j
    · subst j; simp [show k ≠ k+1+1 by omega]
    · by_cases hb : k=j+1
      · subst k; simp [ha]
      · simp [ha,hb]

private theorem angular_cyclic_stable {v : ℕ → ℝ} (hv : v ∈ angularCyclicSpan) :
    angularJacobiMap v ∈ angularCyclicSpan := by
  induction hv using Submodule.span_induction with
  | mem v h =>
    obtain ⟨k,rfl⟩ := h
    apply Submodule.subset_span
    exact ⟨k+1, by dsimp; rw [pow_succ']; rfl⟩
  | zero => rw [map_zero]; exact angularCyclicSpan.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact angularCyclicSpan.add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact angularCyclicSpan.smul_mem c hx

theorem angular_constant_mode_cyclic (j : ℕ) : angularZonalMode j ∈ angularCyclicSpan := by
  have h0 : angularZonalMode 0 ∈ angularCyclicSpan :=
    Submodule.subset_span ⟨0,by simp⟩
  have hdiv (k : ℕ) {v : ℕ → ℝ} (hv : angularJacobiEdge k • v ∈ angularCyclicSpan) : v ∈ angularCyclicSpan := by
    have hd : angularJacobiEdge k ≠ 0 := by unfold angularJacobiEdge; positivity
    simpa [smul_smul,hd] using angularCyclicSpan.smul_mem (angularJacobiEdge k)⁻¹ hv
  induction j using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact hdiv 0 (angular_mode_step_zero ▸ angular_cyclic_stable h0)
  | more j hj hj' =>
    apply hdiv (j+1)
    have hs := angular_cyclic_stable hj'
    rw [angular_mode_step] at hs
    simpa using angularCyclicSpan.sub_mem hs (angularCyclicSpan.smul_mem (angularJacobiEdge j) hj)

end UV
