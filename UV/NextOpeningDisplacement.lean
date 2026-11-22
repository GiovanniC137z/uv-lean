import UV.NextOpeningJacobi
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Vacuum coefficients of the actual oscillator position series. The entire
coefficient function satisfies exactly the neighboring-number recurrence of
the Jacobi operator. Its Taylor derivatives recover the core iterates. -/

noncomputable section

namespace UV

open Filter Complex
open scoped Topology Nat ComplexInnerProductSpace ENNReal

private def opening.normalizedMonomial (n : ℕ) (z : ℂ) : ℂ :=
  z ^ n / (Real.sqrt (n ! : ℝ) : ℂ)

private theorem opening.sqrt_factorial_succ (n : ℕ) :
    (Real.sqrt ((n + 1) ! : ℝ) : ℂ) =
      (Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ) * (Real.sqrt (n ! : ℝ) : ℂ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]

private theorem opening.sqrt_factorial_ne (n : ℕ) :
    (Real.sqrt (n ! : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by exact_mod_cast Nat.factorial_pos n)).ne'

private theorem opening.sqrt_succ_ne (n : ℕ) :
    (Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'

private theorem opening.normalizedMonomial_mul (n : ℕ) (z : ℂ) :
    z * opening.normalizedMonomial n z =
      (Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ) * opening.normalizedMonomial (n + 1) z := by
  rw [opening.normalizedMonomial, opening.normalizedMonomial, opening.sqrt_factorial_succ,
    pow_succ']
  field_simp [opening.sqrt_succ_ne, opening.sqrt_factorial_ne]

private theorem opening.normalizedMonomial_hasDerivAt (n : ℕ) (z : ℂ) :
    HasDerivAt (opening.normalizedMonomial n)
      ((Real.sqrt (n : ℝ) : ℂ) * opening.normalizedMonomial (n - 1) z) z := by
  cases n with
  | zero =>
    have hf : opening.normalizedMonomial 0 = (fun _ : ℂ => 1) :=
      funext fun _ => by simp [opening.normalizedMonomial]
    rw [hf]
    simpa using (hasDerivAt_const z (1 : ℂ))
  | succ n =>
    convert (hasDerivAt_pow (n + 1) z).div_const (Real.sqrt ((n + 1) ! : ℝ) : ℂ) using 1
    unfold opening.normalizedMonomial
    rw [opening.sqrt_factorial_succ, Nat.add_sub_cancel]
    have hsq : (Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ) ^ 2 = ((n + 1 : ℕ) : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      norm_cast
    rw [← hsq]
    field_simp [opening.sqrt_succ_ne, opening.sqrt_factorial_ne]

private def opening.entireCoefficient (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (z ^ 2 / 2) * opening.normalizedMonomial n z

private theorem opening.entireCoefficient_analytic (n : ℕ) (z : ℂ) :
    AnalyticAt ℂ (opening.entireCoefficient n) z := by
  unfold opening.entireCoefficient opening.normalizedMonomial
  have h : AnalyticAt ℂ (fun z : ℂ => z ^ 2 / 2) z := by
    fun_prop (disch := norm_num)
  have h' : AnalyticAt ℂ (fun z : ℂ => z ^ n / (Real.sqrt (n ! : ℝ) : ℂ)) z := by
    fun_prop (disch := exact opening.sqrt_factorial_ne n)
  exact h.cexp.mul h'

private theorem opening.entireCoefficient_deriv (n : ℕ) :
    deriv (opening.entireCoefficient n) =
      (Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ) • opening.entireCoefficient (n + 1) +
        (Real.sqrt (n : ℝ) : ℂ) • opening.entireCoefficient (n - 1) := by
  funext z
  have h₁ : HasDerivAt (fun z : ℂ => z ^ 2 / 2) z z := by
    convert (hasDerivAt_pow 2 z).div_const 2 using 1
    ring
  have h₂ := (Complex.hasDerivAt_exp (z ^ 2 / 2)).comp z h₁
  change HasDerivAt (fun t : ℂ => Complex.exp (t ^ 2 / 2)) (Complex.exp (z ^ 2 / 2) * z) z at h₂
  have hd := (h₂.mul (opening.normalizedMonomial_hasDerivAt n z)).deriv
  change deriv (opening.entireCoefficient n) z = _ at hd
  rw [hd]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, opening.entireCoefficient]
  rw [mul_assoc, opening.normalizedMonomial_mul n z]
  ring

private theorem opening.entireCoefficient_iterated (k n : ℕ) :
    iteratedDeriv k (opening.entireCoefficient n) 0 = openingVacuumPower k n := by
  induction k generalizing n with
  | zero =>
    rw [iteratedDeriv_zero, openingVacuumPower_zero]
    cases n with
    | zero => simp [opening.entireCoefficient, opening.normalizedMonomial, openingNumberState]
    | succ n => simp [opening.entireCoefficient, opening.normalizedMonomial, openingNumberState]
  | succ k ih =>
    rw [iteratedDeriv_succ', opening.entireCoefficient_deriv, iteratedDeriv_add,
      iteratedDeriv_const_smul, iteratedDeriv_const_smul, ih, ih]
    · rfl
    all_goals
      first | exact (opening.entireCoefficient_analytic _ _).contDiffAt
            | exact ((opening.entireCoefficient_analytic _ _).const_smul).contDiffAt

private def opening.coordinate (n : ℕ) : OpeningFock →L[ℂ] ℂ := innerSL ℂ (openingNumberState n)

@[simp] private theorem opening.coordinate_apply (n : ℕ) (v : OpeningFock) :
    opening.coordinate n v = v n := by
  change inner ℂ (openingNumberState n) v = v n
  rw [openingNumberState, lp.inner_single_left]
  simp

private def opening.coefficientSeries (n : ℕ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun k : ℕ => openingVacuumPower k n / k !)

private theorem opening.coefficientSeries_radius (n : ℕ) :
    (opening.coefficientSeries n).radius = ⊤ := by
  refine (opening.coefficientSeries n).radius_eq_top_of_summable_norm (fun r => ?_)
  exact (openingVacuumTaylorTerm_norm_summable (((r : NNReal) : ℝ) : ℂ)).of_nonneg_of_le
    (fun _ => by positivity) (fun k => by
      simp only [opening.coefficientSeries, FormalMultilinearSeries.ofScalars_norm, norm_div,
        Complex.norm_natCast, norm_smul, norm_pow, Complex.norm_real]
      rw [Real.norm_of_nonneg (show 0 ≤ (r : ℝ) from r.2)]
      calc
        _ = (r : ℝ) ^ k / (k ! : ℝ) * ‖openingVacuumPower k n‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (lp.norm_apply_le_norm (by norm_num) _ _) (by positivity))

private theorem opening.coefficientSeries_sum (n : ℕ) (z : ℂ) :
    (opening.coefficientSeries n).sum z = openingVacuumTaylor z n := by
  have hs := (opening.coordinate n).hasSum (openingVacuumTaylor_hasSum z)
  unfold FormalMultilinearSeries.sum opening.coefficientSeries
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  calc
    _ = ∑' k, opening.coordinate n ((z ^ k / (k ! : ℂ)) • openingVacuumPower k) :=
      tsum_congr fun k => by
        rw [map_smul, opening.coordinate_apply, smul_eq_mul]
        ring
    _ = _ := by simpa only [opening.coordinate_apply] using hs.tsum_eq

private theorem opening.entireCoefficient_taylor (n : ℕ) :
    (opening.coefficientSeries n).sum = opening.entireCoefficient n := by
  have hr := opening.coefficientSeries_radius n
  have hs := (opening.coefficientSeries n).hasFPowerSeriesOnBall (by simp [hr])
  have h₁ : AnalyticOnNhd ℂ (opening.coefficientSeries n).sum Set.univ := by
    intro z _
    apply hs.analyticOnNhd z
    simp [hr]
  have h₂ : AnalyticOnNhd ℂ (opening.entireCoefficient n) Set.univ :=
    fun z _ => opening.entireCoefficient_analytic n z
  apply h₁.eq_of_eventuallyEq h₂ (z₀ := 0)
  obtain ⟨r, he⟩ := (opening.entireCoefficient_analytic n 0).hasFPowerSeriesAt
  simp only [opening.entireCoefficient_iterated] at he
  filter_upwards [EMetric.ball_mem_nhds (0 : ℂ) he.r_pos] with z hz
  simpa only [zero_add, opening.coefficientSeries] using (he.sum hz).symm

/-- This is the actual norm-convergent Taylor series of the position rule on
the oscillator vacuum, with its exact complex phase in each number slot. -/
theorem openingVacuumTaylor_coefficient (z : ℂ) (n : ℕ) :
    openingVacuumTaylor z n =
      Complex.exp (z ^ 2 / 2) * z ^ n / (Real.sqrt (n ! : ℝ) : ℂ) := by
  rw [← opening.coefficientSeries_sum, opening.entireCoefficient_taylor]
  unfold opening.entireCoefficient opening.normalizedMonomial
  ring

/-- Exponentiating (i \xi(a+a^†)/\sqrt{2\omega}) on the analytic vacuum
gives the already normalized coherent vector, including every phase. -/
theorem openingVacuumTaylor_on_cut (u : ℝ) :
    openingVacuumTaylor ((u : ℂ) * Complex.I) =
      openingCoherentVector ((u : ℂ) * Complex.I) := by
  ext n
  rw [openingVacuumTaylor_coefficient]
  change _ = openingCoherentCoefficient _ _
  unfold openingCoherentCoefficient
  have hz : ((u : ℂ) * Complex.I) ^ 2 / 2 = ((-u ^ 2 / 2 : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq]
    push_cast
    ring
  rw [hz, Complex.ofReal_exp, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- Norm-square channels for the actual position series on the prescribed
real phase of one physical invariant. -/
theorem openingPositionVacuum_on_cut_poisson {ω ξ b S : ℝ} (hω : 0 < ω)
    (hphase : ξ ^ 2 / (2 * ω) = b * S) (n : ℕ) :
    ‖inner ℂ (openingNumberState n)
      (openingVacuumTaylor (((ξ / Real.sqrt (2 * ω) : ℝ) : ℂ) * Complex.I))‖ ^ 2 =
      ProbabilityTheory.poissonPMFReal (b * S).toNNReal n := by
  rw [openingVacuumTaylor_on_cut, openingNumberState_on_cut_poisson hω hphase]

end UV
