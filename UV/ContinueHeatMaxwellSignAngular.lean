import UV.ContinueHeatMaxwellSign
import UV.ContinueRelativeVariance

/-! Algebra of the two-mark Wilson heat-link jet and its four-dimensional angular reduction. -/

noncomputable section

namespace UV.HeatMaxwell

open UV.SectorPlane UV.RelativeSoft
open scoped RealInnerProductSpace

private abbrev Components := ℝ × ℝ × ℝ

/-- Coordinates in the ordered vectors k, e₁, e₂ of the Euclidean sector. -/
def heatCarrierVector (k : EuclideanPlaneMomentum) (v : Components) : EuclideanPlaneMomentum :=
  v.1 • k + v.2.1 • softLongitudinal.val + v.2.2 • softTransverse.val

/-- Euclidean contraction of two vectors written in the marked-ray coordinates. -/
def heatGram (u k₁ k₂ : ℝ) (v w : Components) : ℝ :=
  u * v.1 * w.1 + k₁ * (v.1 * w.2.1 + v.2.1 * w.1) +
    k₂ * (v.1 * w.2.2 + v.2.2 * w.1) + v.2.1 * w.2.1 + v.2.2 * w.2.2

theorem heatGram_eq_inner (k : EuclideanPlaneMomentum) (v w : Components) :
    ⟪heatCarrierVector k v, heatCarrierVector k w⟫ =
      heatGram (‖k‖ ^ 2) ⟪k, softLongitudinal.val⟫ ⟪k, softTransverse.val⟫ v w := by
  have h₁ : ⟪softLongitudinal.val, softLongitudinal.val⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, softLongitudinal.property, one_pow]
  have h₂ : ⟪softTransverse.val, softTransverse.val⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, softTransverse.property, one_pow]
  have h₂₁ : ⟪softTransverse.val, softLongitudinal.val⟫ = 0 := by
    rw [real_inner_comm, softTransverse_perpendicular]
  simp only [heatCarrierVector, heatGram, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, softTransverse_perpendicular,
    h₁, h₂, h₂₁, real_inner_comm softLongitudinal.val k, real_inner_comm softTransverse.val k]
  ring

def heatK : Components := (1, 0, 0)

def heatH₁ (k₁ : ℝ) : Components := (-2 * k₁, 1, 0)

def heatH₁₁ (k₁ : ℝ) : Components := (4 * k₁ ^ 2 - 2, -4 * k₁, 0)

def heatH₂ (k₂ : ℝ) : Components := (-2 * k₂, 0, 1)

def heatH₁₁₂ (k₁ k₂ : ℝ) : Components :=
  (-2 * k₂ * (4 * k₁ ^ 2 - 2), 8 * k₁ * k₂, 4 * k₁ ^ 2 - 2)

def heatH₁₁₂₂ (k₁ k₂ : ℝ) : Components :=
  ((4 * k₁ ^ 2 - 2) * (4 * k₂ ^ 2 - 2), -4 * k₁ * (4 * k₂ ^ 2 - 2),
    -4 * k₂ * (4 * k₁ ^ 2 - 2))

/-- The quadratic coefficient of the midpoint bubble plus the direct contact.
The variable q is e⁻²ᵘ/D. The mark moments from the two chord integrals
are 1/24 for the first mark and 1/12 for the direct contact. -/
def heatTwoMarkQuadratic (u k₁ k₂ q : ℝ) : ℝ :=
  let dot := heatGram u k₁ k₂
  let a₀ := dot heatK (heatH₂ k₂)
  let a₁ := dot (heatH₁ k₁) (heatH₂ k₂) / 2
  let a₂ := dot heatK (heatH₁₁₂ k₁ k₂) / 24 + dot (heatH₁₁ k₁) (heatH₂ k₂) / 8
  let b₀ := dot (heatH₂ k₂) (heatH₂ k₂)
  let b₂ := dot (heatH₂ k₂) (heatH₁₁₂ k₁ k₂) / 12
  let d₁ := dot heatK (heatH₁ k₁)
  let d₂ := (dot heatK (heatH₁₁ k₁) + dot (heatH₁ k₁) (heatH₁ k₁)) / 4
  let cross₂ := (dot heatK (heatH₁₁ k₁) - dot (heatH₁ k₁) (heatH₁ k₁)) / 4
  let numerator₀ := 2 * q ^ 2 * a₀ ^ 2 - q * b₀
  let numerator₂ := q ^ 2 * (2 * (2 * a₀ * a₂ - a₁ ^ 2) - cross₂ * b₀) - q * b₂
  numerator₂ - numerator₀ * (2 * q * d₂ - (q * d₁) ^ 2) -
    q * dot heatK (heatH₁₁₂₂ k₁ k₂) / 12

def heatAngle00 (u q : ℝ) : ℝ :=
  -q * (6 * q * u - 9 * q + 4 * u - 2) / 12

def heatAngle10 (u q : ℝ) : ℝ :=
  -q * (12 * q ^ 2 * u ^ 2 - 12 * q ^ 2 * u + 3 * q ^ 2 -
    12 * q * u + 12 * q - 2 * u + 3) / 3

def heatAngle01 (u q : ℝ) : ℝ :=
  q * (24 * q ^ 2 * u ^ 3 - 36 * q ^ 2 * u ^ 2 + 18 * q ^ 2 * u - 3 * q ^ 2 -
    22 * q * u ^ 2 + 31 * q * u - 13 * q + 4 * u - 4) / 3

def heatAngle11 (u q : ℝ) : ℝ :=
  2 * q * (48 * q ^ 3 * u ^ 4 - 96 * q ^ 3 * u ^ 3 + 72 * q ^ 3 * u ^ 2 -
    24 * q ^ 3 * u + 3 * q ^ 3 - 72 * q ^ 2 * u ^ 3 + 144 * q ^ 2 * u ^ 2 -
    90 * q ^ 2 * u + 18 * q ^ 2 + 28 * q * u ^ 2 - 56 * q * u + 24 * q -
    4 * u + 8) / 3

theorem heatTwoMarkQuadratic_expand (u k₁ k₂ q : ℝ) :
    heatTwoMarkQuadratic u k₁ k₂ q = heatAngle00 u q +
      heatAngle10 u q * k₁ ^ 2 + heatAngle01 u q * k₂ ^ 2 +
      heatAngle11 u q * (k₁ ^ 2 * k₂ ^ 2) := by
  unfold heatTwoMarkQuadratic heatAngle00 heatAngle10 heatAngle01 heatAngle11
  simp only [heatGram, heatK, heatH₁, heatH₁₁, heatH₂, heatH₁₁₂, heatH₁₁₂₂]
  ring

/-- Normalized angular mean using the S³ moments u/4, u/4 and u²/24. -/
def heatAngularMean (u q : ℝ) : ℝ :=
  heatAngle00 u q + heatAngle10 u q * (u / 4) + heatAngle01 u q * (u / 4) +
    heatAngle11 u q * (u ^ 2 / 24)

def heatRadialPrimitive₁ (u : ℝ) : ℝ := u * (2 * u ^ 2 - 9 * u + 3) / 36

def heatRadialPrimitive₂ (u : ℝ) : ℝ := -(2 * u - 1) * (2 * u ^ 2 - 6 * u + 5) / 24

def heatRadialPrimitive₃ (u : ℝ) : ℝ := (2 * u - 1) ^ 3 / 36

def heatRadialPrimitive (u z : ℝ) : ℝ :=
  heatRadialPrimitive₁ u * z + heatRadialPrimitive₂ u * z ^ 2 + heatRadialPrimitive₃ u * z ^ 3

/-- The explicit total derivative after substituting
z′ = z(1−z)(1/u−2). -/
def heatRadialPrimitiveDerivative (u z : ℝ) : ℝ :=
  let z' := z * (1 - z) * (1 / u - 2)
  (6 * u ^ 2 - 18 * u + 3) / 36 * z + heatRadialPrimitive₁ u * z' +
    (-(12 * u ^ 2 - 28 * u + 16) / 24) * z ^ 2 + heatRadialPrimitive₂ u * (2 * z * z') +
    (2 * u - 1) ^ 2 / 6 * z ^ 3 + heatRadialPrimitive₃ u * (3 * z ^ 2 * z')

/-- The signed radial polynomial and exact total derivative are the angular
reduction of the midpoint bubble and direct contact quadratic jet. -/
theorem heatAngularMean_reduction {u : ℝ} (hu : u ≠ 0) (z : ℝ) :
    u * heatAngularMean u (z / u) =
      z ^ 2 * signPolynomial u / (6 * u) + heatRadialPrimitiveDerivative u z := by
  unfold heatAngularMean heatAngle00 heatAngle10 heatAngle01 heatAngle11
    signPolynomial heatRadialPrimitiveDerivative heatRadialPrimitive₁
    heatRadialPrimitive₂ heatRadialPrimitive₃
  field_simp
  ring

end UV.HeatMaxwell
