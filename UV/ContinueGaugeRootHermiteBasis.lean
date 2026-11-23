import UV.ContinueGaugeRootOscillator
import UV.ContinueOpeningGaussianPosition

/-! The ordinary Hermite polynomials realize the complete oscillator
number basis in the normalized Gaussian Hilbert space. -/

noncomputable section
open MeasureTheory Polynomial Filter
open scoped InnerProductSpace BigOperators
namespace UV.RootMagnetic

def factorialRoot (n : ℕ) : ℝ := Real.sqrt (n.factorial : ℝ)

theorem factorialRoot_pos (n : ℕ) : 0 < factorialRoot n :=
  Real.sqrt_pos.2 (by exact_mod_cast Nat.factorial_pos n)

private theorem factorialRoot_step (n : ℕ) :
    factorialRoot n * Real.sqrt ((n : ℝ) + 1) = factorialRoot (n + 1) := by
  rw [factorialRoot, factorialRoot, ← Real.sqrt_mul (Nat.cast_nonneg _), Nat.factorial_succ]
  push_cast
  ring_nf

private theorem factorialRoot_lower (n : ℕ) :
    factorialRoot (n+1) * Real.sqrt ((n : ℝ) + 1) = ((n : ℝ) + 1) * factorialRoot n := by
  rw [← factorialRoot_step n, mul_assoc, ← pow_two, Real.sq_sqrt (by positivity)]
  ring

private theorem opening_fock_wave_at_zero : openingFockWave 0 = openingNumberState 0 := by
  ext n
  change openingCoherentCoefficient ((0 : ℂ) * Complex.I) n = openingNumberState 0 n
  cases n <;> simp [openingCoherentCoefficient, openingNumberState, lp.single_apply]

private theorem gaussian_number_recurrence
    (U : OpeningFock ≃ₗᵢ[ℂ] OpeningGaussianCarrier)
    (hU : ∀ t, U (openingFockWave t) = openingGaussianWave t) (n : ℕ) :
    ∀ᵐ x : ℝ ∂openingGaussianLaw,
      (x : ℂ) * U (openingNumberState n) x =
        (Real.sqrt ((n+1 : ℕ) : ℝ) : ℂ) * U (openingNumberState (n+1)) x +
        (Real.sqrt (n : ℝ) : ℂ) * U (openingNumberState (n-1)) x := by
  let a := (Real.sqrt ((n+1 : ℕ) : ℝ) : ℂ)
  let b := (Real.sqrt (n : ℝ) : ℂ)
  let J := a • openingNumberState (n+1) + b • openingNumberState (n-1)
  have h := opening_gaussian_position_of_test_derivative (U (openingNumberState n)) (U J) (by
    intro t
    simp_rw [← hU, U.inner_map_map]
    exact opening_wave_number_derivative n t)
  rw [show U J = a • U (openingNumberState (n+1)) + b • U (openingNumberState (n-1)) by simp [J]] at h
  filter_upwards [h, Lp.coeFn_add (a • U (openingNumberState (n+1))) (b • U (openingNumberState (n-1))),
    Lp.coeFn_smul a (U (openingNumberState (n+1))), Lp.coeFn_smul b (U (openingNumberState (n-1)))] with x hx h₁ h₂ h₃
  change (x : ℂ) * U (openingNumberState n) x = _ at hx
  rw [hx, h₁, Pi.add_apply, h₂, h₃]
  rfl

/-- The Gaussian unitary takes each number vector to the specified
probabilists' Hermite polynomial divided by the square root of n!. -/
theorem root_gaussian_number_polynomial
    (U : OpeningFock ≃ₗᵢ[ℂ] OpeningGaussianCarrier)
    (hU : ∀ t, U (openingFockWave t) = openingGaussianWave t) (n : ℕ) :
    ∀ᵐ x : ℝ ∂openingGaussianLaw,
      (factorialRoot n : ℂ) * U (openingNumberState n) x = (((rootHermite n).eval x : ℝ) : ℂ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          have h := hU 0
          rw [opening_fock_wave_at_zero] at h
          filter_upwards [opening_gaussian_wave_ae 0] with x hx
          simp [h, hx, openingFourierWave, factorialRoot]
      | succ n =>
          have ih₀ := ih n (Nat.lt_succ_self n)
          have ih₁ := ih (n-1) (by omega)
          filter_upwards [ih₀, ih₁, gaussian_number_recurrence U hU n] with x h₀ h₁ h
          rw [rootHermite_succ]
          simp only [eval_sub, eval_mul, eval_X, Complex.ofReal_sub, Complex.ofReal_mul]
          cases n with
          | zero =>
              have hz : U (openingNumberState 0) x = 1 := by simpa [factorialRoot] using h₀
              have hnext : (x : ℂ) = U (openingNumberState 1) x := by simpa [hz] using h
              simpa [rootHermite_zero, factorialRoot] using hnext.symm
          | succ k =>
              change _ = (x : ℂ) * (((rootHermite (k+1)).eval x : ℝ) : ℂ) -
                ((((rootHermite (k+1)).derivative.eval x) : ℝ) : ℂ)
              rw [rootHermite_derivative, eval_mul, eval_C, Complex.ofReal_mul]
              change _ = (x : ℂ) * (((rootHermite (k+1)).eval x : ℝ) : ℂ) -
                  (((k:ℝ)+1 : ℝ):ℂ) * (((rootHermite k).eval x : ℝ) : ℂ)
              have hprev : (factorialRoot k : ℂ) * U (openingNumberState k) x = (((rootHermite k).eval x : ℝ) : ℂ) := by
                simpa only [Nat.add_sub_cancel] using h₁
              rw [← h₀, ← hprev]
              change (x:ℂ) * U (openingNumberState (k+1)) x =
                (Real.sqrt ((k+1+1:ℕ):ℝ):ℂ) * U (openingNumberState (k+1+1)) x +
                (Real.sqrt ((k+1:ℕ):ℝ):ℂ) * U (openingNumberState k) x at h
              have hstep : (factorialRoot (k+1) : ℂ) * (Real.sqrt ((k+1+1 : ℕ) : ℝ) : ℂ) =
                  (factorialRoot (k+1+1) : ℂ) := by exact_mod_cast (factorialRoot_step (k+1))
              have hlower : (factorialRoot (k+1) : ℂ) * (Real.sqrt ((k+1:ℕ) : ℝ) : ℂ) =
                  ((k : ℂ)+1) * (factorialRoot k : ℂ) := by exact_mod_cast (factorialRoot_lower k)
              have hh := congrArg ((factorialRoot (k+1) : ℂ) * ·) h
              simp only [mul_add, ← mul_assoc] at hh
              rw [hstep, hlower] at hh
              push_cast
              linear_combination -hh

theorem root_gaussian_basis_exists :
    ∃ b : HilbertBasis ℕ ℂ OpeningGaussianCarrier, ∀ n,
      (fun x => (factorialRoot n : ℂ) * b n x) =ᵐ[openingGaussianLaw]
        (fun x : ℝ => (((rootHermite n).eval x : ℝ) : ℂ)) := by
  obtain ⟨U, hU⟩ := opening_position_unitary_exists
  let b : HilbertBasis ℕ ℂ OpeningGaussianCarrier := HilbertBasis.ofRepr U.symm
  refine ⟨b, ?_⟩
  intro n
  have he : b n = U (openingNumberState n) := (b.repr_symm_single n).symm
  rw [he]
  exact root_gaussian_number_polynomial U hU n

end UV.RootMagnetic
