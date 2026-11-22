import UV.ExtendCurvaturePotential

/-! The block curvature square on the fixed Euclidean sector-plane
coordinates and the two orthonormal internal one-form directions. -/

noncomputable section

open MeasureTheory Real
open scoped BigOperators

namespace UV.AdvanceCurvatureAction

open UV.ExtendCurvaturePotential

abbrev Color (n : ℕ) := Fin n → ℝ
abbrev Direction := Fin 4 ⊕ Fin 2
abbrev HorizontalPair := {p : Fin 4 × Fin 4 // p.1 < p.2}
abbrev WedgeDirection := HorizontalPair ⊕ ((Fin 4 × Fin 2) ⊕ Unit)

/-- The ordered orthonormal two-form coordinate basis. The last coordinate
is the source's oriented θ¹ ∧ θ² component. -/
def wedgeDirections : WedgeDirection → Direction × Direction
  | .inl p => (.inl p.1.1, .inl p.1.2)
  | .inr (.inl p) => (.inl p.1, .inr p.2)
  | .inr (.inr ()) => (.inr 0, .inr 1)

def algebraBracket {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (U W : Color n) : Color n :=
  fun c => ∑ a, ∑ b, B c a b * (U a * W b)

@[simp] theorem algebraBracket_zero_left {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (W : Color n) : algebraBracket B 0 W = 0 := by
  funext c
  simp [algebraBracket]

@[simp] theorem algebraBracket_zero_right {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (U : Color n) : algebraBracket B U 0 = 0 := by
  funext c
  simp [algebraBracket]

def connectionValue {n : ℕ} (A : Fin 2 → Color n) : Direction → Color n
  | .inl _ => 0
  | .inr a => A a

def partialConnection {n : ℕ} (D : Fin 4 → Fin 2 → Color n) : Direction → Direction → Color n
  | .inl j, .inr a => D j a
  | _, _ => 0

/-- Components of dA + A ∧ A in the ordered orthonormal two-form basis. -/
def curvatureComponent {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (A : Fin 2 → Color n) (D : Fin 4 → Fin 2 → Color n) (i j : Direction) : Color n :=
  partialConnection D i j - partialConnection D j i +
    algebraBracket B (connectionValue A i) (connectionValue A j)

@[simp] theorem curvature_horizontal_horizontal {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (A : Fin 2 → Color n) (D : Fin 4 → Fin 2 → Color n) (i j : Fin 4) :
    curvatureComponent B A D (.inl i) (.inl j) = 0 := by
  simp [curvatureComponent, partialConnection, connectionValue]

@[simp] theorem curvature_horizontal_internal {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (A : Fin 2 → Color n) (D : Fin 4 → Fin 2 → Color n) (i : Fin 4) (j : Fin 2) :
    curvatureComponent B A D (.inl i) (.inr j) = D i j := by
  simp [curvatureComponent, partialConnection, connectionValue]

@[simp] theorem curvature_internal {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (A : Fin 2 → Color n) (D : Fin 4 → Fin 2 → Color n) (i j : Fin 2) :
    curvatureComponent B A D (.inr i) (.inr j) = algebraBracket B (A i) (A j) := by
  simp [curvatureComponent, partialConnection, connectionValue]

def colorSquare {n : ℕ} (v : Color n) : ℝ := ∑ c, (v c)^2

theorem colorSquare_zero (n : ℕ) : colorSquare (0 : Color n) = 0 := by
  simp [colorSquare]

def blockCurvatureHalfSquare {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (A : Fin 2 → Color n) (D : Fin 4 → Fin 2 → Color n) : ℝ :=
  (1/2 : ℝ) * ∑ p : WedgeDirection,
    colorSquare (curvatureComponent B A D (wedgeDirections p).1 (wedgeDirections p).2)

theorem block_curvature_decomposition {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (A : Fin 2 → Color n) (D : Fin 4 → Fin 2 → Color n) :
    blockCurvatureHalfSquare B A D =
      (1/2 : ℝ) * ((∑ i, ∑ j, colorSquare (D i j)) + colorSquare (algebraBracket B (A 0) (A 1))) := by
  unfold blockCurvatureHalfSquare
  simp only [Fintype.sum_sum_type, wedgeDirections, curvature_horizontal_horizontal, colorSquare_zero,
    Finset.sum_const_zero, zero_add, curvature_horizontal_internal, curvature_internal,
    Fintype.sum_prod_type, Fintype.sum_unique]

def twoSlots {E : Type*} (x y : E) : Fin 2 → E := fun i => if i = 0 then x else y

@[simp] theorem twoSlots_first {E : Type*} (x y : E) : twoSlots x y 0 = x := by simp [twoSlots]
@[simp] theorem twoSlots_second {E : Type*} (x y : E) : twoSlots x y 1 = y := by simp [twoSlots]

/-- The three diagonal blocks are X θ¹, Y θ², and U θ¹ + W θ². Only
the third block has an internal commutator coefficient. -/
theorem three_block_curvature_decomposition {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (X Y U W : Color n) (dX dY dU dW : Fin 4 → Color n) :
    blockCurvatureHalfSquare B (twoSlots X 0) (fun i => twoSlots (dX i) 0) +
      blockCurvatureHalfSquare B (twoSlots 0 Y) (fun i => twoSlots 0 (dY i)) +
      blockCurvatureHalfSquare B (twoSlots U W) (fun i => twoSlots (dU i) (dW i)) =
      (1/2 : ℝ) * (∑ i, (colorSquare (dX i) + colorSquare (dY i) +
        colorSquare (dU i) + colorSquare (dW i))) +
        (1/2 : ℝ) * colorSquare (algebraBracket B U W) := by
  simp only [block_curvature_decomposition, Fin.sum_univ_two, twoSlots_first, twoSlots_second,
    algebraBracket_zero_left, algebraBracket_zero_right, colorSquare_zero, add_zero, zero_add,
    Finset.sum_add_distrib]
  ring

private theorem bracketDensity_apply {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (U W : Fin n → ContinuousField) (x : Torus) :
    bracketDensity B U W x = (1/2 : ℝ) * colorSquare (algebraBracket B (fun a => U a x) (fun a => W a x)) := by
  simp only [bracketDensity, bracketCoordinate, colorSquare, algebraBracket,
    ContinuousMap.smul_apply, ContinuousMap.sum_apply, ContinuousMap.mul_apply, ContinuousMap.pow_apply,
    smul_eq_mul]

def kineticDensity {n : ℕ} (dX dY dU dW : Fin 4 → Fin n → ContinuousField) : ContinuousField :=
  (1/2 : ℝ) • ∑ i, ∑ c, ((dX i c)^2 + (dY i c)^2 + (dU i c)^2 + (dW i c)^2)

private theorem kineticDensity_apply {n : ℕ} (dX dY dU dW : Fin 4 → Fin n → ContinuousField)
    (x : Torus) : kineticDensity dX dY dU dW x =
      (1/2 : ℝ) * (∑ i, (colorSquare (fun c => dX i c x) + colorSquare (fun c => dY i c x) +
        colorSquare (fun c => dU i c x) + colorSquare (fun c => dW i c x))) := by
  simp only [kineticDensity, colorSquare, ContinuousMap.add_apply, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, ContinuousMap.pow_apply, smul_eq_mul, Finset.sum_add_distrib]

/-- The literal pointwise block square integrates to the four copied
kinetic terms plus the squared bracket potential of the same fields.
The arrays dX through dW are the coefficients of the four exterior gradients. -/
theorem integrated_sector_action {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (X Y U W : Fin n → ContinuousField) (dX dY dU dW : Fin 4 → Fin n → ContinuousField) :
    (∫ x, blockCurvatureHalfSquare B (twoSlots (fun a => X a x) 0)
        (fun i => twoSlots (fun c => dX i c x) 0) +
      blockCurvatureHalfSquare B (twoSlots 0 (fun a => Y a x))
        (fun i => twoSlots 0 (fun c => dY i c x)) +
      blockCurvatureHalfSquare B (twoSlots (fun a => U a x) (fun a => W a x))
        (fun i => twoSlots (fun c => dU i c x) (fun c => dW i c x)) ∂normalizedTorusVolume) =
      normalizedIntegral (kineticDensity dX dY dU dW) + normalizedIntegral (bracketDensity B U W) := by
  rw [← map_add]
  change (∫ x, _ ∂normalizedTorusVolume) = (∫ x, (kineticDensity dX dY dU dW + bracketDensity B U W) x
    ∂normalizedTorusVolume)
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [ContinuousMap.add_apply, bracketDensity_apply, kineticDensity_apply]
  exact three_block_curvature_decomposition B (fun a => X a x) (fun a => Y a x)
    (fun a => U a x) (fun a => W a x) (fun i c => dX i c x) (fun i c => dY i c x)
    (fun i c => dU i c x) (fun i c => dW i c x)

end UV.AdvanceCurvatureAction
