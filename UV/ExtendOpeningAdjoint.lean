import UV.NextOpeningPositionCore

/-! The actual adjoint coordinates of the symmetric oscillator position.
Testing the adjoint on each oscillator number state fixes all its Jacobi
coefficients at the boundary and in the interior. -/

noncomputable section

namespace UV

open scoped Nat ComplexInnerProductSpace ComplexConjugate ENNReal

/-- Frequency coefficient of the position field on the number basis. -/
def openingPositionScale (ω : ℝ) : ℂ := (Real.sqrt (2 * ω) : ℂ)⁻¹

@[simp] theorem openingPositionScale_star (ω : ℝ) :
    star (openingPositionScale ω) = openingPositionScale ω := by
  simp [openingPositionScale]

@[simp] theorem openingNumberState_coordinate (n k : ℕ) :
    openingNumberState n k = if n = k then 1 else 0 := by
  by_cases h : n = k
  · subst k
    simp [openingNumberState]
  · exact (lp.single_apply_ne (E := fun _ : ℕ => ℂ) 2 n 1 (Ne.symm h)).trans (if_neg h).symm

@[simp] theorem opening_inner_number (n : ℕ) (v : OpeningFock) :
    inner ℂ (openingNumberState n) v = v n := by
  rw [openingNumberState, lp.inner_single_left]
  simp

private theorem opening.jacobi_number (n k : ℕ) :
    openingJacobi (openingNumberState n) k =
      (Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ) * openingNumberState (n + 1) k +
        (Real.sqrt (n : ℝ) : ℂ) * openingNumberState (n - 1) k := by
  simp only [openingJacobi, openingNumberState_coordinate]
  cases k with
  | zero =>
    by_cases h : n = 1
    · subst n
      simp
    · simp [h, show n - 1 = 0 ↔ n = 0 by omega]
      intro hn
      simp [hn]
  | succ k =>
    by_cases hl : n = k + 2
    · subst n
      simp
      ring_nf
    · by_cases hr : n = k
      · subst n
        simp [show ¬k = k + 1 + 1 by omega, show ¬ k - 1 = k + 1 by omega]
      · simp [hl, hr, show ¬ n - 1 = k + 1 by omega]

def openingPositionNumberState (ω : ℝ) (n : ℕ) : (openingPositionOnCore ω).domain :=
  ⟨openingNumberState n, ⟨n, fun k hk => by simp [show n ≠ k by omega]⟩⟩

private theorem opening.position_number (ω : ℝ) (n : ℕ) :
    openingPositionOnCore ω (openingPositionNumberState ω n) =
      openingPositionScale ω •
        ((Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ) • openingNumberState (n + 1) +
          (Real.sqrt (n : ℝ) : ℂ) • openingNumberState (n - 1)) := by
  ext k
  rw [openingPositionOnCore_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, lp.coeFn_add, Pi.add_apply, smul_eq_mul]
  exact congrArg (openingPositionScale ω * ·) (opening.jacobi_number n k)

theorem openingPositionOnCore_dense (ω : ℝ) :
    Dense ((openingPositionOnCore ω).domain : Set OpeningFock) :=
  openingNumberCore_dense

/-- The adjoint is given by the same Jacobi expression at every number
coordinate of its actual maximal domain. -/
theorem openingPositionOnCore_adjoint_coordinate (ω : ℝ)
    (v : (openingPositionOnCore ω).adjoint.domain) (n : ℕ) :
    ((openingPositionOnCore ω).adjoint v) n = openingPositionScale ω *
      openingJacobi (v : OpeningFock) n := by
  have h := (LinearPMap.adjoint_isFormalAdjoint (openingPositionOnCore_dense ω)).symm
    (openingPositionNumberState ω n) v
  rw [opening.position_number] at h
  change inner ℂ _ (v : OpeningFock) =
    inner ℂ (openingNumberState n) ((openingPositionOnCore ω).adjoint v) at h
  have hs : starRingEnd ℂ (openingPositionScale ω) = openingPositionScale ω :=
    openingPositionScale_star ω
  simpa only [inner_smul_left, inner_add_left, Complex.conj_ofReal,
    hs, opening_inner_number, openingJacobi] using h.symm

end UV
