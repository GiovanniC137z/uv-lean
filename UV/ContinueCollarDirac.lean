import UV.FurtherBoundaryCollar

/-! The normal Pauli operator in radial coordinates on the fixed quartic chart. -/

noncomputable section

namespace UV.ContinueCollarDirac

/-- First component of `−i σ₁ ∂ᵣ + σ₂ W` on a two-component normal spinor. -/
def diracUpper (W : ℝ → ℝ) (v : ℝ → ℂ) (r : ℝ) : ℂ :=
  -Complex.I * (deriv v r + (W r : ℂ) * v r)

/-- Second component of `−i σ₁ ∂ᵣ + σ₂ W` on a two-component normal spinor. -/
def diracLower (W : ℝ → ℝ) (u : ℝ → ℂ) (r : ℝ) : ℂ :=
  -Complex.I * (deriv u r - (W r : ℂ) * u r)

/-- On twice differentiable mode components the Pauli square has the two chiral potentials. -/
theorem normal_mode_dirac_square {W : ℝ → ℝ} {u v : ℝ → ℂ} {r w' : ℝ} {u₂ v₂ : ℂ}
    (hW : HasDerivAt W w' r) (hu : DifferentiableAt ℝ u r) (hv : DifferentiableAt ℝ v r)
    (hu₂ : HasDerivAt (deriv u) u₂ r) (hv₂ : HasDerivAt (deriv v) v₂ r) :
    diracUpper W (diracLower W u) r = -u₂ + ((W r : ℂ) ^ (2 : ℕ) + (w' : ℂ)) * u r ∧
      diracLower W (diracUpper W v) r = -v₂ + ((W r : ℂ) ^ (2 : ℕ) - (w' : ℂ)) * v r := by
  have h₁ : HasDerivAt (diracLower W u)
      (-Complex.I * (u₂ - ((w' : ℂ) * u r + (W r : ℂ) * deriv u r))) r :=
    (hu₂.sub (hW.ofReal_comp.mul hu.hasDerivAt)).const_mul (-Complex.I)
  have h₂ : HasDerivAt (diracUpper W v)
      (-Complex.I * (v₂ + ((w' : ℂ) * v r + (W r : ℂ) * deriv v r))) r :=
    (hv₂.add (hW.ofReal_comp.mul hv.hasDerivAt)).const_mul (-Complex.I)
  constructor
  · simp only [diracUpper, h₁.deriv, diracLower]
    calc
      _ = Complex.I ^ (2 : ℕ) * (u₂ - (w' : ℂ) * u r - (W r : ℂ) ^ (2 : ℕ) * u r) := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  · simp only [diracLower, h₂.deriv, diracUpper]
    calc
      _ = Complex.I ^ (2 : ℕ) * (v₂ + (w' : ℂ) * v r - (W r : ℂ) ^ (2 : ℕ) * v r) := by ring
      _ = _ := by rw [Complex.I_sq]; ring

/-- The fixed quartic profile gives the stated (W_n^2 pm W_n') expressions. -/
theorem quartic_normal_mode_dirac_square (ν b : ℝ) {u v : ℝ → ℂ} {r : ℝ} {u₂ v₂ : ℂ}
    (hr : r ≠ 0) (hu : DifferentiableAt ℝ u r) (hv : DifferentiableAt ℝ v r)
    (hu₂ : HasDerivAt (deriv u) u₂ r) (hv₂ : HasDerivAt (deriv v) v₂ r) :
    let W := UV.FurtherBoundaryCollar.spinMultiplier ν b
    let W' := -4 * ν / r ^ (5 : ℕ) - b
    diracUpper W (diracLower W u) r = -u₂ + ((W r : ℂ) ^ (2 : ℕ) + (W' : ℂ)) * u r ∧
      diracLower W (diracUpper W v) r = -v₂ + ((W r : ℂ) ^ (2 : ℕ) - (W' : ℂ)) * v r :=
  normal_mode_dirac_square (UV.FurtherBoundaryCollar.spinMultiplier_hasDerivAt ν b hr) hu hv hu₂ hv₂

/-- Multiplication by the quartic radial half-density removes the (2/r) term. -/
theorem quartic_radial_half_density_conjugation {u : ℝ → ℂ} {r : ℝ} (hr : r ≠ 0)
    (hu : DifferentiableAt ℝ u r) :
    ((r : ℂ) ^ (2 : ℕ)) *
      (deriv (fun x : ℝ => (((x ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * u x) r +
        ((2 / r : ℝ) : ℂ) * (((r ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * u r) = deriv u r := by
  have hpow : HasDerivAt (fun x : ℝ => x ^ (2 : ℕ)) (2 * r) r := by
    convert (hasDerivAt_id r).pow 2 using 1
    simp
  have hinv : HasDerivAt (fun x : ℝ => (x ^ (2 : ℕ))⁻¹) (-2 / r ^ (3 : ℕ)) r := by
    convert hpow.inv (pow_ne_zero 2 hr) using 1
    field_simp
  have hprod := hinv.ofReal_comp.mul hu.hasDerivAt
  change HasDerivAt (fun x : ℝ => (((x ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * u x) _ r at hprod
  rw [hprod.deriv]
  have hz : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  push_cast
  field_simp
  ring

/-- At an exact angular resonance both normal chiral scalar potentials are bounded at the tip. -/
theorem zero_normal_mode_potential_bound (b s r : ℝ) (hs : |s| ≤ 1)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    |(UV.FurtherBoundaryCollar.spinMultiplier 0 b r) ^ (2 : ℕ) + s * (-b)| ≤
      b ^ (2 : ℕ) + |b| := by
  unfold UV.FurtherBoundaryCollar.spinMultiplier
  rw [zero_div, zero_sub, neg_sq]
  calc
    _ ≤ |(b * r) ^ (2 : ℕ)| + |s * (-b)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_of_nonneg (sq_nonneg _), mul_pow, abs_mul, abs_neg]
      have hrp : r ^ (2 : ℕ) ≤ 1 := pow_le_one₀ hr.1 hr.2
      exact add_le_add (by simpa using mul_le_mul_of_nonneg_left hrp (sq_nonneg b))
        (by simpa using mul_le_mul_of_nonneg_right hs (abs_nonneg b))

end UV.ContinueCollarDirac
