import UV.ContinueOpeningFockWaves

/-! The Fourier transform of each Gaussian-side number state obeys
the same raising/lowering recurrence as the number representation. -/

noncomputable section
namespace UV
open scoped ComplexConjugate
private def openingHermiteFactor (n : ℕ) : ℂ := (-Complex.I)^n/(Real.sqrt (n.factorial:ℝ):ℂ)

private theorem opening_hermite_factor_succ (n : ℕ) :
    (Real.sqrt ((n+1:ℕ):ℝ):ℂ)*openingHermiteFactor (n+1) = -Complex.I*openingHermiteFactor n := by
  have ha : (0:ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hb : (0:ℝ) < n+1 := by positivity
  have hne : (Real.sqrt ((n:ℝ)+1):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hb)
  simp only [openingHermiteFactor,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ,Real.sqrt_mul hb.le,Complex.ofReal_mul,pow_succ]
  field_simp

private theorem opening_hermite_factor_prev (n : ℕ) :
    -Complex.I*(Real.sqrt (n:ℝ):ℂ)*openingHermiteFactor (n-1) = (n:ℂ)*openingHermiteFactor n := by
  cases n with
  | zero => simp
  | succ n =>
    have h := opening_hermite_factor_succ n
    have hs : (Real.sqrt ((n+1:ℕ):ℝ):ℂ)^2 = (n+1:ℕ) := by exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (n+1))
    simp only [Nat.add_sub_cancel] at *
    calc
      _ = (Real.sqrt ((n+1:ℕ):ℝ):ℂ)*(-Complex.I*openingHermiteFactor n) := by ring
      _ = _ := by rw [←h,←mul_assoc,←pow_two,hs]

theorem opening_wave_number_fourier (n : ℕ) (t : ℝ) :
    inner ℂ (openingFockWave t) (openingNumberState n) =
      (Real.exp (-t^2/2):ℂ)*openingHermiteFactor n*(t:ℂ)^n := by
  rw [←inner_conj_symm,openingFockWave,openingNumberState_overlap]
  change (starRingEnd ℂ) (openingCoherentCoefficient _ _) = _
  have hN : ‖(t:ℂ)*Complex.I‖^2=t^2 := by simp [Real.norm_eq_abs,sq_abs]
  simp only [openingCoherentCoefficient,hN,map_div₀,map_mul,map_pow,Complex.conj_ofReal,Complex.conj_I,openingHermiteFactor,mul_pow]
  ring

/-- Differentiation uses the actual two adjacent matrix elements of
the oscillator position on the finite-number core. -/
theorem opening_wave_number_derivative (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s => inner ℂ (openingFockWave s) (openingNumberState n))
      (-Complex.I*inner ℂ (openingFockWave t)
        ((Real.sqrt ((n+1:ℕ):ℝ):ℂ) • openingNumberState (n+1) +
         (Real.sqrt (n:ℝ):ℂ) • openingNumberState (n-1))) t := by
  have hg : HasDerivAt (fun s : ℝ => Real.exp (-s^2/2)) (-t*Real.exp (-t^2/2)) t := by
    convert ((((hasDerivAt_id t).pow 2).neg.div_const 2).exp) using 1; simp; ring
  have ht : HasDerivAt (fun s : ℝ => (s:ℂ)) 1 t := by simpa using (hasDerivAt_id t).ofReal_comp
  simp_rw [opening_wave_number_fourier]
  have h := (hg.ofReal_comp.mul_const (openingHermiteFactor n)).mul (ht.pow n)
  convert h using 1
  let e : ℂ := Real.exp (-t^2/2)
  simp only [inner_add_right,inner_smul_right,opening_wave_number_fourier,Pi.pow_apply,mul_one,Complex.ofReal_mul,Complex.ofReal_neg]
  change -Complex.I * ((Real.sqrt ((n+1:ℕ):ℝ):ℂ)*(e*openingHermiteFactor (n+1)*(t:ℂ)^(n+1))+
    (Real.sqrt (n:ℝ):ℂ)*(e*openingHermiteFactor (n-1)*(t:ℂ)^(n-1))) =
    -(t:ℂ)*e*openingHermiteFactor n*(t:ℂ)^n+e*openingHermiteFactor n*((n:ℂ)*(t:ℂ)^(n-1))
  have he : -Complex.I*((Real.sqrt ((n+1:ℕ):ℝ):ℂ)*openingHermiteFactor (n+1))= -openingHermiteFactor n := by
    rw [opening_hermite_factor_succ]; linear_combination (openingHermiteFactor n) * Complex.I_sq
  calc
    _ = e*(t:ℂ)^(n+1)*(-Complex.I*((Real.sqrt ((n+1:ℕ):ℝ):ℂ)*openingHermiteFactor (n+1))) +
      e*(t:ℂ)^(n-1)*(-Complex.I*(Real.sqrt (n:ℝ):ℂ)*openingHermiteFactor (n-1)) := by ring
    _ = _ := by rw [he,opening_hermite_factor_prev,pow_succ]; ring

end UV
