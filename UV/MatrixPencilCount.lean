import UV.FinitePole

/-! Actual zero count one throughout the complex Neumann parameter disk.
The real path t ↦ tλ preserves the boundary divisor count. -/

noncomputable section
open Set Metric
open scoped Topology Matrix.Norms.L2Operator

namespace UV

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem matrix_pencil_parameter_margin {θ : ℝ} (hθ : 0 < θ) {lam : ℂ}
    (hlam : lam ∈ ball (0 : ℂ) θ⁻¹) : ‖lam‖ * θ < 1 := by
  have hn : ‖lam‖ < θ⁻¹ := by simpa only [mem_ball, dist_zero_right] using hlam
  calc
    _ < θ⁻¹ * θ := mul_lt_mul_of_pos_right hn hθ
    _ = 1 := inv_mul_cancel₀ hθ.ne'

theorem matrix_pencil_parameter_boundary_nonzero
    {K D : ℂ → Matrix n n ℂ} {c : ℂ} {r θ : ℝ} (hθ : 0 < θ)
    (hb : ∀ z ∈ sphere c r, (K z).det ≠ 0)
    (hmargin : ∀ z ∈ sphere c r, ‖Ring.inverse (K z) * D z‖ ≤ θ)
    {lam : ℂ} (hlam : lam ∈ ball (0 : ℂ) θ⁻¹) :
    ∀ z ∈ sphere c r, matrixPencilDet K D lam z ≠ 0 :=
  finite_pencil_boundary_nonzero hb hmargin (matrix_pencil_parameter_margin hθ hlam)

/-- The initial unique simple zero and the actual complex-parameter Neumann
margin force divisor count one at every admitted parameter. No perturbed
root, perturbed simplicity, or perturbed zero count is assumed. -/
theorem matrix_pencil_diskZeroCount_eq_one
    {K D : ℂ → Matrix n n ℂ} {c : ℂ} {r θ : ℝ} (hr : 0 < r) (hθ : 0 < θ)
    (hK : ∀ i j, AnalyticOnNhd ℂ (fun z => K z i j) (closedBall c r))
    (hD : ∀ i j, AnalyticOnNhd ℂ (fun z => D z i j) (closedBall c r))
    (hb : ∀ z ∈ sphere c r, (K z).det ≠ 0)
    (hzero : (K c).det = 0) (hsimple : deriv (fun z => (K z).det) c ≠ 0)
    (honly : ∀ z ∈ ball c r, (K z).det = 0 → z = c)
    (hmargin : ∀ z ∈ sphere c r, ‖Ring.inverse (K z) * D z‖ ≤ θ) :
    ∀ lam ∈ ball (0 : ℂ) θ⁻¹, diskZeroCount (matrixPencilDet K D lam) c r = 1 := by
  intro lam hlam
  let F : ℝ → ℂ → ℂ := fun t z => (K z + (t : ℂ) • (lam • D z)).det
  have hscaled : ∀ i j, AnalyticOnNhd ℂ (fun z => (lam • D z) i j) (closedBall c r) := by
    intro i j
    simpa only [Matrix.smul_apply, smul_eq_mul] using analyticOnNhd_const.mul (hD i j)
  obtain ⟨hA, hC, hderiv⟩ := matrix_pencil_closedDisk_boundary_data hK hscaled
  have hF0 : F 0 = fun z => (K z).det := by funext z; simp [F]
  have hF1 : F 1 = matrixPencilDet K D lam := by funext z; simp [F, matrixPencilDet]
  have hlamMargin := matrix_pencil_parameter_margin hθ hlam
  have hbF : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ sphere c r, F t z ≠ 0 := by
    intro t ht
    have htNorm : ‖(t : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg ht.1]
      exact ht.2
    have hpath : ‖(t : ℂ) * lam‖ * θ < 1 := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left (norm_nonneg lam) htNorm) hθ.le).trans_lt hlamMargin
    simpa only [F, smul_smul] using finite_pencil_boundary_nonzero hb hmargin hpath
  have hzeroCount : diskZeroCount (F 0) c r = 1 := by
    rw [hF0]
    apply disk_zeroCount_eq_one_of_unique_simple _ hr hb (mem_ball_self hr) hzero hsimple honly
    simpa only [← hF0] using hA (0 : ℝ)
  have hcount := disk_zeroCount_homotopy (F := F) hr (fun t _ => hA t) hbF hC hderiv
  have hresult := (hcount 1 ⟨zero_le_one, le_rfl⟩).trans hzeroCount
  simpa only [hF1] using hresult

end UV
