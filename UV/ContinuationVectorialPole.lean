import UV.ContinuationSectorPlane
import UV.CarrierStructure

/-! Finite-height vectorial pole prescription on a fixed diamond.
The actual real axial covector is unchanged. The geometric pole unit is
represented by the literal root of the scalar carrier quotient.
This file treats finite heights only. Distributional boundary limits require
an independent test-domain and convergence theorem. -/

noncomputable section

namespace UV.SectorPlane

open UV.Carrier

abbrev Height := {ε : ℝ // 0 < ε}

variable {E : Type*} [NormedAddCommGroup E]

section Geometry

variable [NormedSpace ℝ E]

/-- The height is positive. The sector/evolution sign is kept outside
the displaced vector. -/
def Plane.epsilonVector (diamond : Plane E) (height : Height) : E :=
  (height : ℝ) • (diamond.poleUnit : E)

theorem Plane.epsilonVector_norm (diamond : Plane E) (height : Height) :
    ‖diamond.epsilonVector height‖ = (height : ℝ) := by
  simp [Plane.epsilonVector, Plane.poleUnit, norm_smul, Real.norm_eq_abs,
    abs_of_pos height.property, diamond.Ghat.property]

theorem Plane.epsilonVector_direction (diamond : Plane E) (height : Height) :
    ‖diamond.epsilonVector height‖⁻¹ • diamond.epsilonVector height =
      (diamond.poleUnit : E) := by
  rw [diamond.epsilonVector_norm, Plane.epsilonVector, smul_smul,
    inv_mul_cancel₀ height.property.ne', one_smul]

end Geometry

def axialSign (kParallel : ℝ) : ℝ :=
  if 0 < kParallel then 1 else if kParallel < 0 then -1 else 0

theorem axialSign_abs {kParallel : ℝ} (hk : kParallel ≠ 0) : |axialSign kParallel| = 1 := by
  rcases lt_or_gt_of_ne hk with h | h
  · simp [axialSign, h, h.not_gt]
  · simp [axialSign, h]

theorem axialSign_eq_normalized {kParallel : ℝ} (hk : kParallel ≠ 0) :
    axialSign kParallel = kParallel / |kParallel| := by
  rcases lt_or_gt_of_ne hk with h | h
  · rw [axialSign, if_neg h.not_gt, if_pos h, abs_of_neg h]
    field_simp
  · rw [axialSign, if_pos h, abs_of_pos h, div_self hk]

section Running

variable [NormedSpace ℝ E]

/-- The running normalized unit is only defined at a nonzero aligned
carrier coefficient. Positive and negative rays share the same fixed pole unit. -/
def Plane.runningUnit (diamond : Plane E) (kParallel : ℝ) (hk : kParallel ≠ 0) :
    UnitVector E :=
  ⟨axialSign kParallel • (diamond.poleUnit : E), by
    simp [norm_smul, Real.norm_eq_abs, Plane.poleUnit, diamond.Ghat.property, axialSign_abs hk]⟩

theorem Plane.running_unit_from_aligned (diamond : Plane E) {kParallel : ℝ}
    (hk : kParallel ≠ 0) :
    (diamond.runningUnit kParallel hk : E) =
      ‖kParallel • (diamond.poleUnit : E)‖⁻¹ • (kParallel • (diamond.poleUnit : E)) := by
  simp [Plane.runningUnit, norm_smul, Real.norm_eq_abs, Plane.poleUnit, diamond.Ghat.property,
    smul_smul, axialSign_eq_normalized hk, div_eq_mul_inv, mul_comm]

end Running

/-- Real-algebra embedding of the directed complex line, valued in the
literal scalar quotient C[e]/(e²−1). -/
def directed (z : ℂ) : QuotientCarrier := quotientCharacterEquiv.symm (z, star z)

def poleRoot : QuotientCarrier := AdjoinRoot.root relation

def directedUnit : QuotientCarrier := algebraMap ℂ QuotientCarrier Complex.I * poleRoot

theorem directed_mul (z w : ℂ) : directed (z * w) = directed z * directed w := by
  apply quotientCharacterEquiv.injective
  simp [directed]

theorem directed_one : directed 1 = 1 := by
  apply quotientCharacterEquiv.injective
  simp [directed]

theorem directed_as_real_plus_root (z : ℂ) :
    directed z = algebraMap ℂ QuotientCarrier z.re +
      algebraMap ℂ QuotientCarrier (Complex.I * z.im) * poleRoot := by
  apply quotientCharacterEquiv.injective
  simp only [directed, AlgEquiv.apply_symm_apply, map_add, map_mul, AlgEquiv.commutes,
    poleRoot, quotientCharacterEquiv_root]
  ext <;> simp [generator, Complex.ext_iff, Complex.mul_re, Complex.mul_im]

def Plane.poleDenominator (diamond : Plane E) (ε : Evolution) (height : Height)
    (D : ℝ) : QuotientCarrier :=
  directed ((D : ℂ) + Complex.I * ((diamond.eta ε * (height : ℝ) : ℝ) : ℂ))

theorem Plane.pole_denominator_literal (diamond : Plane E) (ε : Evolution)
    (height : Height) (D : ℝ) :
    diamond.poleDenominator ε height D = algebraMap ℂ QuotientCarrier D +
      algebraMap ℂ QuotientCarrier (Complex.I * ((diamond.eta ε * (height : ℝ) : ℝ) : ℂ)) *
        poleRoot := by
  rw [Plane.poleDenominator, directed_as_real_plus_root]
  simp

theorem Plane.shifted_denominator_ne_zero (diamond : Plane E) (ε : Evolution)
    (height : Height) (D : ℝ) :
    (D : ℂ) + Complex.I * ((diamond.eta ε * (height : ℝ) : ℝ) : ℂ) ≠ 0 := by
  intro he
  have him := congrArg Complex.im he
  simp at him
  rcases him with h | h
  · have hs := diamond.eta_sq ε
    simp [h] at hs
  · exact height.property.ne' h

/-- Exact finite-height inverse of the directed boundary factor. -/
def Plane.poleInverse (diamond : Plane E) (ε : Evolution) (height : Height)
    (D : ℝ) : QuotientCarrier :=
  directed (((D : ℂ) - Complex.I * ((diamond.eta ε * (height : ℝ) : ℝ) : ℂ)) /
    ((D ^ 2 + (height : ℝ) ^ 2 : ℝ) : ℂ))

theorem Plane.pole_inverse_complex (diamond : Plane E) (ε : Evolution)
    (height : Height) (D : ℝ) :
    diamond.poleInverse ε height D =
      directed (((D : ℂ) + Complex.I * ((diamond.eta ε * (height : ℝ) : ℝ) : ℂ))⁻¹) := by
  unfold Plane.poleInverse
  congr 1
  let d : ℂ := D
  let b : ℂ := (height : ℝ)
  let η : ℂ := diamond.eta ε
  have hs : η ^ 2 = 1 := by
    dsimp [η]
    exact_mod_cast diamond.eta_sq ε
  have hsum : d ^ 2 + b ^ 2 ≠ 0 := by
    have hreal : 0 < D ^ 2 + (height : ℝ) ^ 2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos height.property)
    dsimp [d, b]
    exact_mod_cast hreal.ne'
  have hz : d + Complex.I * (η * b) ≠ 0 := by
    simpa [d, b, η] using diamond.shifted_denominator_ne_zero ε height D
  push_cast
  change (d - Complex.I * (η * b)) / (d ^ 2 + b ^ 2) =
    (d + Complex.I * (η * b))⁻¹
  rw [div_eq_iff hsum]
  apply (mul_left_cancel₀ hz)
  have hprod : (d + Complex.I * (η * b)) * (d - Complex.I * (η * b)) =
      d ^ 2 + b ^ 2 := by
    calc
      _ = d ^ 2 - Complex.I ^ 2 * η ^ 2 * b ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq, hs]; ring
  rw [hprod, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]

theorem Plane.pole_inverse_law (diamond : Plane E) (ε : Evolution)
    (height : Height) (D : ℝ) :
    diamond.poleDenominator ε height D * diamond.poleInverse ε height D = 1 := by
  rw [diamond.pole_inverse_complex, Plane.poleDenominator, ← directed_mul,
    mul_inv_cancel₀ (diamond.shifted_denominator_ne_zero ε height D), directed_one]

/-- The real shell input in the Lorentzian formula retains its signed
axial component. Euclidean squared momenta use a different expression. -/
def shellSquare (kParallel : ℝ) (k : Spatial) : ℝ := kParallel ^ 2 - ‖k‖ ^ 2

/-- The literal finite-height line in the directed algebra. The branch
function acts on the directed line through its extracted complex coordinate. -/
def Plane.scalarLine (diamond : Plane E) (ε : Evolution) (height : Height)
    (φ : ℂ → ℂ) (a m kParallel : ℝ) (k : Spatial) (_hk : kParallel ≠ 0) :
    QuotientCarrier :=
  directed (Complex.I * ((diamond.eta ε * axialSign kParallel : ℝ) : ℂ)) *
    directed (φ (-(a : ℂ) ^ 2 * ((shellSquare kParallel k : ℂ) +
      Complex.I * ((diamond.eta ε * (height : ℝ) : ℝ) : ℂ)))) *
    diamond.poleInverse ε height (shellSquare kParallel k - m ^ 2)

theorem Plane.scalar_line_plus (diamond : Plane E) (ε : Evolution) (height : Height)
    (φ : ℂ → ℂ) (a m kParallel : ℝ) (k : Spatial) (hk : kParallel ≠ 0) :
    (quotientCharacterEquiv (diamond.scalarLine ε height φ a m kParallel k hk)).1 =
      Complex.I * ((diamond.eta ε * axialSign kParallel : ℝ) : ℂ) *
        φ (-(a : ℂ) ^ 2 * ((shellSquare kParallel k : ℂ) +
          Complex.I * ((diamond.eta ε * (height : ℝ) : ℝ) : ℂ))) /
        (((shellSquare kParallel k - m ^ 2 : ℝ) : ℂ) +
          Complex.I * ((diamond.eta ε * (height : ℝ) : ℝ) : ℂ)) := by
  simp [Plane.scalarLine, diamond.pole_inverse_complex, directed, div_eq_mul_inv]

theorem Plane.scalar_line_minus (diamond : Plane E) (ε : Evolution) (height : Height)
    (φ : ℂ → ℂ) (hφ : ∀ z, star (φ z) = φ (star z))
    (a m kParallel : ℝ) (k : Spatial) (hk : kParallel ≠ 0) :
    (quotientCharacterEquiv (diamond.scalarLine ε height φ a m kParallel k hk)).2 =
      -Complex.I * ((diamond.eta ε * axialSign kParallel : ℝ) : ℂ) *
        φ (-(a : ℂ) ^ 2 * ((shellSquare kParallel k : ℂ) -
          Complex.I * ((diamond.eta ε * (height : ℝ) : ℝ) : ℂ))) /
        (((shellSquare kParallel k - m ^ 2 : ℝ) : ℂ) -
          Complex.I * ((diamond.eta ε * (height : ℝ) : ℝ) : ℂ)) := by
  simp [Plane.scalarLine, diamond.pole_inverse_complex, directed, div_eq_mul_inv, hφ, sub_eq_add_neg]


theorem directed_neg (z : ℂ) : directed (-z) = -directed z := by
  apply quotientCharacterEquiv.injective
  simp [directed]

theorem axialSign_neg {kParallel : ℝ} (hk : kParallel ≠ 0) :
    axialSign (-kParallel) = -axialSign kParallel := by
  rw [axialSign_eq_normalized (neg_ne_zero.mpr hk), axialSign_eq_normalized hk, abs_neg,
    neg_div]

@[simp] theorem shellSquare_reverse (kParallel : ℝ) (k : Spatial) :
    shellSquare (-kParallel) (-k) = shellSquare kParallel k := by
  simp [shellSquare]

/-- The running-unit line is odd at finite positive height. The pole
displacement and support are held fixed under momentum reversal. -/
theorem Plane.scalar_line_running_odd (diamond : Plane E) (ε : Evolution)
    (height : Height) (φ : ℂ → ℂ) (a m kParallel : ℝ) (k : Spatial)
    (hk : kParallel ≠ 0) :
    diamond.scalarLine ε height φ a m (-kParallel) (-k) (neg_ne_zero.mpr hk) =
      -diamond.scalarLine ε height φ a m kParallel k hk := by
  unfold Plane.scalarLine
  simp only [shellSquare_reverse, axialSign_neg hk, mul_neg, Complex.ofReal_neg,
    directed_neg, neg_mul]

/-- An identical commuting scalar would have an even covariance from
source exchange. A nonzero running-unit line violates that test before a limit. -/
theorem Plane.running_line_fails_identical_scalar_exchange (diamond : Plane E)
    (ε : Evolution) (height : Height) (φ : ℂ → ℂ) (a m kParallel : ℝ)
    (k : Spatial) (hk : kParallel ≠ 0)
    (h : diamond.scalarLine ε height φ a m kParallel k hk ≠ 0) :
    diamond.scalarLine ε height φ a m (-kParallel) (-k) (neg_ne_zero.mpr hk) ≠
      diamond.scalarLine ε height φ a m kParallel k hk := by
  intro he
  have he' := (diamond.scalar_line_running_odd ε height φ a m kParallel k hk).symm.trans he
  have hc := congrArg quotientCharacterEquiv he'
  rw [map_neg] at hc
  apply h
  apply quotientCharacterEquiv.injective
  rw [map_zero]
  exact Prod.ext (CharZero.neg_eq_self_iff.mp (congrArg Prod.fst hc))
    (CharZero.neg_eq_self_iff.mp (congrArg Prod.snd hc))

/-- The declared fixed virtual-carrier benchmark uses the sector unit
for every line. This is a separate expression from the running-unit line. -/
def Plane.fixedScalarLine (diamond : Plane E) (ε : Evolution) (height : Height)
    (φ : ℂ → ℂ) (a m kParallel : ℝ) (k : Spatial) : QuotientCarrier :=
  directed (Complex.I * (evolutionSign ε : ℂ)) *
    directed (φ (-(a : ℂ) ^ 2 * ((shellSquare kParallel k : ℂ) +
      Complex.I * ((diamond.eta ε * (height : ℝ) : ℝ) : ℂ)))) *
    diamond.poleInverse ε height (shellSquare kParallel k - m ^ 2)

theorem Plane.scalar_line_on_sector_ray (diamond : Plane E) (ε : Evolution)
    (height : Height) (φ : ℂ → ℂ) (a m kParallel : ℝ) (k : Spatial)
    (hk : kParallel ≠ 0) (hRay : axialSign kParallel = sectorSign diamond.s) :
    diamond.scalarLine ε height φ a m kParallel k hk =
      diamond.fixedScalarLine ε height φ a m kParallel k := by
  have hs : diamond.eta ε * sectorSign diamond.s = evolutionSign ε := by
    unfold Plane.eta
    calc
      _ = sectorSign diamond.s ^ 2 * evolutionSign ε := by ring
      _ = _ := by simp
  simp only [Plane.scalarLine, Plane.fixedScalarLine, hRay, hs]

theorem Plane.fixed_scalar_line_even (diamond : Plane E) (ε : Evolution)
    (height : Height) (φ : ℂ → ℂ) (a m kParallel : ℝ) (k : Spatial) :
    diamond.fixedScalarLine ε height φ a m (-kParallel) (-k) =
      diamond.fixedScalarLine ε height φ a m kParallel k := by
  simp only [Plane.fixedScalarLine, shellSquare_reverse]

/-- The exact real and directed-imaginary parts of the undamped fixed
line give its Poisson and principal-value regularizers. -/
theorem Plane.fixed_pole_components (diamond : Plane E) (ε : Evolution)
    (height : Height) (D : ℝ) :
    directed (Complex.I * (evolutionSign ε : ℂ)) * diamond.poleInverse ε height D =
      directed (((sectorSign diamond.s * (height : ℝ) : ℝ) : ℂ) /
          ((D ^ 2 + (height : ℝ) ^ 2 : ℝ) : ℂ) +
        Complex.I * ((evolutionSign ε * D : ℝ) : ℂ) /
          ((D ^ 2 + (height : ℝ) ^ 2 : ℝ) : ℂ)) := by
  rw [Plane.poleInverse, ← directed_mul]
  congr 1
  have hs : evolutionSign ε * diamond.eta ε = sectorSign diamond.s := by
    unfold Plane.eta
    calc
      _ = evolutionSign ε ^ 2 * sectorSign diamond.s := by ring
      _ = _ := by simp
  have hsc : (evolutionSign ε : ℂ) * (diamond.eta ε : ℂ) =
      (sectorSign diamond.s : ℂ) := by exact_mod_cast hs
  push_cast
  have he : Complex.I * (evolutionSign ε : ℂ) *
      ((D : ℂ) - Complex.I * ((diamond.eta ε : ℂ) * (height : ℝ))) =
      (sectorSign diamond.s : ℂ) * (height : ℝ) +
        Complex.I * ((evolutionSign ε : ℂ) * (D : ℂ)) := by
    calc
      _ = Complex.I * (evolutionSign ε : ℂ) * (D : ℂ) -
          Complex.I ^ 2 * ((evolutionSign ε : ℂ) * (diamond.eta ε : ℂ)) *
            (height : ℝ) := by ring
      _ = _ := by rw [Complex.I_sq, hsc]; ring
  rw [← mul_div_assoc, he]
  ring

end UV.SectorPlane
