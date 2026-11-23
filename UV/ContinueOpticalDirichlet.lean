import UV.ContinueConstitutiveMagnetic

/-! The independent normal fluctuation at fixed boundary value has the
half-line Green function of -d²/dy² + k², with Dirichlet boundary trace. -/

noncomputable section

open Real Set Filter

namespace UV

def opticalDirichletGreen (k y z : ℝ) : ℝ :=
  (exp (-k * |y-z|) - exp (-k*(y+z))) / (2*k)

theorem opticalDirichletGreen_symmetric (k y z : ℝ) :
    opticalDirichletGreen k y z = opticalDirichletGreen k z y := by
  simp only [opticalDirichletGreen, abs_sub_comm y z, add_comm y z]

theorem opticalDirichletGreen_boundary (k : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    opticalDirichletGreen k 0 z = 0 := by simp [opticalDirichletGreen, abs_of_nonneg hz]

theorem opticalDirichletGreen_continuous (k z : ℝ) :
    Continuous (fun y => opticalDirichletGreen k y z) := by unfold opticalDirichletGreen; fun_prop

private def opticalLeft (k z y : ℝ) : ℝ := (exp (k*(y-z)) - exp (-k*(y+z)))/(2*k)
private def opticalRight (k z y : ℝ) : ℝ := (exp (-k*(y-z)) - exp (-k*(y+z)))/(2*k)
private def opticalLeftSlope (k z y : ℝ) : ℝ := (exp (k*(y-z)) + exp (-k*(y+z)))/2
private def opticalRightSlope (k z y : ℝ) : ℝ := (-exp (-k*(y-z)) + exp (-k*(y+z)))/2

private theorem opticalDirichletGreen_left {k z y : ℝ} (hy : y ≤ z) :
    opticalDirichletGreen k y z = opticalLeft k z y := by
  unfold opticalDirichletGreen opticalLeft
  rw [abs_of_nonpos (sub_nonpos.mpr hy), neg_mul_neg]

private theorem opticalDirichletGreen_right {k z y : ℝ} (hy : z ≤ y) :
    opticalDirichletGreen k y z = opticalRight k z y := by
  simp [opticalDirichletGreen, opticalRight, abs_of_nonneg (sub_nonneg.mpr hy)]

private theorem opticalExpAffine (k z y : ℝ) :
    HasDerivAt (fun x : ℝ => exp (k*(x+z))) (k * exp (k*(y+z))) y := by
  convert (((hasDerivAt_id y).add_const z).const_mul k).exp using 1
  simp [mul_comm]

private theorem opticalLeft_deriv {k : ℝ} (hk : 0 < k) (z y : ℝ) :
    HasDerivAt (opticalLeft k z) (opticalLeftSlope k z y) y := by
  have h := ((opticalExpAffine k (-z) y).sub (opticalExpAffine (-k) z y)).div_const (2*k)
  simp only [← sub_eq_add_neg] at h
  convert h using 1
  unfold opticalLeftSlope
  field_simp
  ring

private theorem opticalRight_deriv {k : ℝ} (hk : 0 < k) (z y : ℝ) :
    HasDerivAt (opticalRight k z) (opticalRightSlope k z y) y := by
  have h := ((opticalExpAffine (-k) (-z) y).sub (opticalExpAffine (-k) z y)).div_const (2*k)
  simp only [← sub_eq_add_neg] at h
  convert h using 1
  unfold opticalRightSlope
  field_simp
  ring

private theorem opticalLeft_second {k : ℝ} (hk : 0 < k) (z y : ℝ) :
    HasDerivAt (opticalLeftSlope k z) (k^2 * opticalLeft k z y) y := by
  have h := ((opticalExpAffine k (-z) y).add (opticalExpAffine (-k) z y)).div_const 2
  simp only [← sub_eq_add_neg] at h
  convert h using 1
  unfold opticalLeft
  field_simp
  ring

private theorem opticalRight_second {k : ℝ} (hk : 0 < k) (z y : ℝ) :
    HasDerivAt (opticalRightSlope k z) (k^2 * opticalRight k z y) y := by
  have h := ((opticalExpAffine (-k) (-z) y).neg.add (opticalExpAffine (-k) z y)).div_const 2
  simp only [← sub_eq_add_neg] at h
  convert h using 1
  unfold opticalRight
  field_simp
  ring

/-- The two actual derivatives of the continuous kernel on the diagonal
differ by minus one, the delta-source normalization for -d²/dy². -/
theorem opticalDirichletGreen_jump {k : ℝ} (hk : 0 < k) (z : ℝ) :
    ∃ l u : ℝ, HasDerivWithinAt (fun y => opticalDirichletGreen k y z) l (Iic z) z ∧
      HasDerivWithinAt (fun y => opticalDirichletGreen k y z) u (Ici z) z ∧ u-l = -1 := by
  refine ⟨_, _, (opticalLeft_deriv hk z z).hasDerivWithinAt.congr
    (fun _ hy => opticalDirichletGreen_left hy) (opticalDirichletGreen_left le_rfl),
    (opticalRight_deriv hk z z).hasDerivWithinAt.congr
    (fun _ hy => opticalDirichletGreen_right hy) (opticalDirichletGreen_right le_rfl), ?_⟩
  simp [opticalLeftSlope, opticalRightSlope]
  ring

theorem opticalDirichletGreen_ode {k : ℝ} (hk : 0 < k) {y z : ℝ} (hy : y ≠ z) :
    deriv (deriv (fun t => opticalDirichletGreen k t z)) y = k^2 * opticalDirichletGreen k y z := by
  rcases lt_or_gt_of_ne hy with hl | hr
  · have H (x : ℝ) (hx : x < z) : deriv (fun t => opticalDirichletGreen k t z) x =
        opticalLeftSlope k z x := by
      have he : (fun t => opticalDirichletGreen k t z) =ᶠ[nhds x] opticalLeft k z :=
        (gt_mem_nhds hx).mono (fun t ht => opticalDirichletGreen_left (k := k) ht.le)
      exact he.deriv_eq.trans (opticalLeft_deriv hk z x).deriv
    have he : deriv (fun t => opticalDirichletGreen k t z) =ᶠ[nhds y] opticalLeftSlope k z :=
      (gt_mem_nhds hl).mono H
    exact he.deriv_eq.trans ((opticalLeft_second hk z y).deriv.trans
      (by rw [opticalDirichletGreen_left hl.le]))
  · have H (x : ℝ) (hx : z < x) : deriv (fun t => opticalDirichletGreen k t z) x =
        opticalRightSlope k z x := by
      have he : (fun t => opticalDirichletGreen k t z) =ᶠ[nhds x] opticalRight k z :=
        (lt_mem_nhds hx).mono (fun t ht => opticalDirichletGreen_right (k := k) ht.le)
      exact he.deriv_eq.trans (opticalRight_deriv hk z x).deriv
    have he : deriv (fun t => opticalDirichletGreen k t z) =ᶠ[nhds y] opticalRightSlope k z :=
      (lt_mem_nhds hr).mono H
    exact he.deriv_eq.trans ((opticalRight_second hk z y).deriv.trans
      (by rw [opticalDirichletGreen_right hr.le]))

theorem opticalDirichletGreen_diag (k y : ℝ) :
    opticalDirichletGreen k y y = (1-exp (-(2*k*y)))/(2*k) := by
  unfold opticalDirichletGreen
  simp only [sub_self, abs_zero, mul_zero, exp_zero]
  ring_nf

theorem opticalDirichletGreen_diag_lower {k k₀ y : ℝ} (h₀ : 0 < k₀) (hk : k₀ ≤ k) (hy : 0 < y) :
    0 < 1-exp (-(2*k₀*y)) ∧ (1-exp (-(2*k₀*y)))/(2*k) ≤ opticalDirichletGreen k y y := by
  rw [opticalDirichletGreen_diag]
  constructor
  · exact sub_pos.mpr (exp_lt_one_iff.mpr (by nlinarith [mul_pos h₀ hy]))
  · apply div_le_div_of_nonneg_right _ (by linarith)
    apply sub_le_sub_left
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hk hy.le]

end UV
