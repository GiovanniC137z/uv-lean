import UV.ContinuationVectorialPole
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Finite-height response on one fixed sector plane. A transported
imaginary carrier unit and the real shell function can both vary in one
common algebra. Inversion is differentiated before the height limit. -/

noncomputable section

namespace UV.SectorPlane

open UV.Carrier

variable {E R : Type*} [NormedAddCommGroup E] [NormedRing R]
  [NormedAlgebra ℝ R]

/-- The shifted denominator in the transported common algebra. -/
def Plane.transportedPole (diamond : Plane E) (ε : Evolution) (height : Height)
    (D : ℝ) (j : UnitVector R) : R :=
  algebraMap ℝ R D + (diamond.eta ε * (height : ℝ)) • (j : R)

private def Plane.transportedPoleUnits (diamond : Plane E) (ε : Evolution)
    (height : Height) (D : ℝ) (j : UnitVector R) (hj : (j : R) ^ 2 = -1) : Rˣ := by
  let h : ℝ := height
  let η := diamond.eta ε
  let a := algebraMap ℝ R D
  let b : R := (η * h) • (j : R)
  have hb : b ^ 2 = -(algebraMap ℝ R (h ^ 2)) := by
    have hs : (η * h) ^ 2 = h ^ 2 := by
      rw [mul_pow, diamond.eta_sq ε, one_mul]
    dsimp [b]
    rw [smul_pow, hs, hj, smul_neg, Algebra.algebraMap_eq_smul_one]
  have ha : a ^ 2 = algebraMap ℝ R (D ^ 2) := (map_pow _ _ _).symm
  have hab : a * b = b * a := Algebra.commutes D b
  have hp : (a + b) * (a - b) = algebraMap ℝ R (D ^ 2 + h ^ 2) := by
    rw [add_mul, mul_sub, mul_sub, hab, ← pow_two, ← pow_two, ha, hb, map_add]
    abel
  have hq : (a - b) * (a + b) = algebraMap ℝ R (D ^ 2 + h ^ 2) := by
    rw [sub_mul, mul_add, mul_add, hab, ← pow_two, ← pow_two, ha, hb, map_add]
    abel
  have hn : D ^ 2 + h ^ 2 ≠ 0 :=
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos height.property)).ne'
  let v : R := (D ^ 2 + h ^ 2)⁻¹ • (a - b)
  have huv : (a + b) * v = 1 := by
    dsimp only [v]
    rw [mul_smul_comm, hp, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hn, map_one]
  have hvu : v * (a + b) = 1 := by
    dsimp only [v]
    rw [smul_mul_assoc, hq, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hn, map_one]
  exact ⟨a + b, v, huv, hvu⟩

theorem Plane.transported_pole_isUnit (diamond : Plane E) (ε : Evolution)
    (height : Height) (D : ℝ) (j : UnitVector R) (hj : (j : R) ^ 2 = -1) :
    IsUnit (diamond.transportedPole ε height D j) :=
  ⟨diamond.transportedPoleUnits ε height D j hj, rfl⟩

theorem Plane.transported_pole_inverse_formula (diamond : Plane E) (ε : Evolution)
    (height : Height) (D : ℝ) (j : UnitVector R) (hj : (j : R) ^ 2 = -1) :
    Ring.inverse (diamond.transportedPole ε height D j) =
      (D ^ 2 + (height : ℝ) ^ 2)⁻¹ •
        (algebraMap ℝ R D - (diamond.eta ε * (height : ℝ)) • (j : R)) := by
  rw [show diamond.transportedPole ε height D j =
    (diamond.transportedPoleUnits ε height D j hj : R) from rfl, Ring.inverse_unit]
  rfl

variable [CompleteSpace R]

/-- Exact variation of the transported finite-height inverse, in the
noncommutative sandwich order. The same fixed pole side multiplies both
the transported unit and its derivative. -/
theorem Plane.transported_pole_inverse_variation (diamond : Plane E) (ε : Evolution)
    (height : Height) (D : ℝ → ℝ) (j : ℝ → UnitVector R)
    {y dD : ℝ} {dj : R} (hD : HasDerivAt D dD y)
    (hj : HasDerivAt (fun y => (j y : R)) dj y)
    (hjSq : (j y : R) ^ 2 = -1) :
    let A (t : ℝ) := diamond.transportedPole ε height (D t) (j t)
    let R₀ := Ring.inverse (A y)
    HasDerivAt (fun t => Ring.inverse (A t))
      (-R₀ * (algebraMap ℝ R dD + (diamond.eta ε * (height : ℝ)) • dj) * R₀) y := by
  let A (t : ℝ) := diamond.transportedPole ε height (D t) (j t)
  let V := algebraMap ℝ R dD + (diamond.eta ε * (height : ℝ)) • dj
  let L : ℝ →L[ℝ] R := (1 : ℝ →L[ℝ] ℝ).smulRight (1 : R)
  have hL (d : ℝ) : L d = algebraMap ℝ R d := by
    simp [L, Algebra.algebraMap_eq_smul_one]
  have hD' := L.hasFDerivAt.comp_hasDerivAt y hD
  have hA : HasDerivAt A V y := by
    simpa [A, V, Plane.transportedPole, Function.comp_def, hL] using
      hD'.add (hj.const_smul (diamond.eta ε * (height : ℝ)))
  obtain ⟨u, hu⟩ := diamond.transported_pole_isUnit ε height (D y) (j y) hjSq
  change (u : R) = A y at hu
  have hI := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at hI
  have h := hI.comp_hasDerivAt y hA
  have hinv : Ring.inverse (A y) = (↑u⁻¹ : R) := by
    rw [← hu, Ring.inverse_unit]
  change HasDerivAt (fun t => Ring.inverse (A t))
    (-Ring.inverse (A y) * V * Ring.inverse (A y)) y
  simpa [Function.comp_def, ContinuousLinearMap.mulLeftRight_apply, hinv] using h

/-- In the original carrier quotient, the imaginary transported unit
is the literal product of the scalar imaginary unit with the carrier root. -/
def quotientPoleUnit : UnitVector QuotientCarrier :=
  ⟨directedUnit, by
    simp only [quotient_character_norm, directedUnit, map_mul, AlgEquiv.commutes, poleRoot,
      quotientCharacterEquiv_root, generator]
    change max ‖Complex.I * 1‖ ‖Complex.I * -1‖ = 1
    simp⟩

theorem quotient_pole_unit_sq : (quotientPoleUnit : QuotientCarrier) ^ 2 = -1 := by
  apply quotientCharacterEquiv.injective
  simp only [map_pow, map_neg, map_one, quotientPoleUnit, directedUnit, map_mul,
    AlgEquiv.commutes, poleRoot, quotientCharacterEquiv_root]
  ext <;> simp [generator, Complex.I_sq]

theorem Plane.transported_pole_quotient (diamond : Plane E) (ε : Evolution)
    (height : Height) (D : ℝ) :
    diamond.transportedPole ε height D quotientPoleUnit = diamond.poleDenominator ε height D := by
  rw [diamond.pole_denominator_literal, Plane.transportedPole, Algebra.smul_def]
  have hmap (r : ℝ) : algebraMap ℝ ℂ r = (r : ℂ) := rfl
  simp only [IsScalarTower.algebraMap_apply ℝ ℂ QuotientCarrier, hmap,
    quotientPoleUnit, directedUnit, Complex.ofReal_mul, map_mul]
  ring

end UV.SectorPlane
