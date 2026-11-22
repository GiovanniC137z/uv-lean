import UV.Kernel
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Data.Matrix.Mul

/-! The one-sided covariance criterion for an injective bounded transfer,
and the spectral projection criterion in a finite eigenbasis. -/

namespace UV

section Operator

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem transferred_covariance_remainder (P C : E →L[𝕜] E) :
    P * C * P - P ^ 2 * C = P * (C * P - P * C) := by
  rw [pow_two, mul_sub]
  simp only [mul_assoc]

/-- Injectivity suffices for cancellation. A bounded inverse is unnecessary. -/
theorem transferred_covariance_eq_iff_of_injective (P C : E →L[𝕜] E)
    (hP : Function.Injective P) : P * C * P = P ^ 2 * C ↔ Commute C P := by
  constructor
  · intro h
    show C * P = P * C
    ext x
    apply hP
    have hx := congrArg (fun A : E →L[𝕜] E => A x) h
    simpa only [pow_two, ContinuousLinearMap.mul_apply] using hx
  · intro h
    rw [pow_two, mul_assoc, h.eq, ← mul_assoc]

end Operator

section FiniteSpectrum

open Matrix

/-- The scalar transfer separates any two distinct nonnegative eigenvalues. -/
theorem kernel_inj_on_nonnegative {r M x y : ℝ} (hr : 0 < r) (hx : 0 ≤ x)
    (hy : 0 ≤ y) : kernel r M x = kernel r M y ↔ x = y := by
  constructor
  · intro h
    have h₁ := Real.exp_injective h
    have h₂ : depthProfile M x = depthProfile M y :=
      mul_left_cancel₀ (neg_ne_zero.mpr (ne_of_gt hr)) h₁
    have h₃ : Real.sqrt (x + M ^ 2) = Real.sqrt (y + M ^ 2) := by
      unfold depthProfile at h₂
      linarith
    have h₄ := congrArg (fun s : ℝ => s ^ 2) h₃
    dsimp at h₄
    rw [Real.sq_sqrt (by positivity : 0 ≤ x + M ^ 2),
      Real.sq_sqrt (by positivity : 0 ≤ y + M ^ 2)] at h₄
    linarith
  · rintro rfl
    rfl

/-- Spectral projection onto the coordinates with eigenvalues in `s`. -/
noncomputable def finiteSpectralProjection {n : Type*} [DecidableEq n]
    (eigenvalue : n → ℝ) (s : Set ℝ) : Matrix n n ℝ := by
  classical
  exact diagonal fun i => if eigenvalue i ∈ s then 1 else 0

/-- On a finite eigenbasis, commutation with the square-root transfer is
precisely commutation with every spectral projection of the normal generator. -/
theorem kernel_transfer_commute_iff_spectral_projections {n : Type*}
    [Fintype n] [DecidableEq n] (eigenvalue : n → ℝ) (hL : ∀ i, 0 ≤ eigenvalue i)
    (C : Matrix n n ℝ) {r M : ℝ} (hr : 0 < r) :
    Commute C (diagonal fun i => kernel r M (eigenvalue i)) ↔
      ∀ s : Set ℝ, Commute C (finiteSpectralProjection eigenvalue s) := by
  classical
  constructor
  · intro h s
    change C * finiteSpectralProjection eigenvalue s = finiteSpectralProjection eigenvalue s * C
    unfold finiteSpectralProjection
    ext i j
    simp only [mul_diagonal, diagonal_mul]
    by_cases hij : eigenvalue i = eigenvalue j
    · rw [hij, mul_comm]
    · have hij' := mt (kernel_inj_on_nonnegative (M := M) hr (hL i) (hL j)).mp hij
      have hc := congrArg (fun A : Matrix n n ℝ => A i j) h.eq
      simp only [mul_diagonal, diagonal_mul] at hc
      have hz : C i j = 0 := by
        have hprod : C i j * (kernel r M (eigenvalue i) - kernel r M (eigenvalue j)) = 0 := by
          linear_combination -hc
        exact (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hij')
      simp [hz]
  · intro h
    show C * diagonal _ = diagonal _ * C
    ext i j
    simp only [mul_diagonal, diagonal_mul]
    by_cases hij : eigenvalue i = eigenvalue j
    · rw [hij, mul_comm]
    · have hc := congrArg (fun A : Matrix n n ℝ => A i j) (h {eigenvalue i}).eq
      simp [finiteSpectralProjection, mul_diagonal, diagonal_mul, Ne.symm hij] at hc
      simp [← hc]

/-- The lower covariance block in the flat commuting reduction. -/
theorem flat_transferred_covariance (r M u m : ℝ) :
    kernel r M u * (u + m ^ 2)⁻¹ * kernel r M u =
      kernel (2 * r) M u / (u + m ^ 2) := by
  unfold kernel
  rw [div_eq_mul_inv]
  have hh : -(2 * r) * depthProfile M u =
      -r * depthProfile M u + -r * depthProfile M u := by ring
  rw [hh, Real.exp_add]
  ring

end FiniteSpectrum

end UV
