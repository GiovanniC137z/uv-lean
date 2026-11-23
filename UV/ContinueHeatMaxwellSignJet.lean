import UV.ContinueHeatMaxwellSignAngular
import Mathlib.Algebra.Polynomial.Coeff

/-! Extraction of the second coefficient from the literal normalized bubble and contact jets. -/

noncomputable section

namespace UV.HeatMaxwell

/-- Coefficients up to t² in the ordinary univariate Taylor convention. -/
structure HeatScalarJet where
  constant : ℝ
  linear : ℝ
  quadratic : ℝ

private def HeatScalarJet.add (a b : HeatScalarJet) : HeatScalarJet :=
  ⟨a.constant + b.constant, a.linear + b.linear, a.quadratic + b.quadratic⟩

private def HeatScalarJet.scale (c : ℝ) (a : HeatScalarJet) : HeatScalarJet :=
  ⟨c * a.constant, c * a.linear, c * a.quadratic⟩

private def HeatScalarJet.sub (a b : HeatScalarJet) : HeatScalarJet := a.add (b.scale (-1))

private def HeatScalarJet.mul (a b : HeatScalarJet) : HeatScalarJet :=
  ⟨a.constant * b.constant, a.constant * b.linear + a.linear * b.constant,
    a.constant * b.quadratic + a.linear * b.linear + a.quadratic * b.constant⟩

private def HeatScalarJet.unitInverse (a : HeatScalarJet) : HeatScalarJet :=
  ⟨1, -a.linear, a.linear ^ 2 - a.quadratic⟩

/-- The normalized denominator inverse cancels through quadratic order. -/
theorem heatScalarJet_unitInverse (a : HeatScalarJet) (ha : a.constant = 1) :
    a.mul a.unitInverse = ⟨1, 0, 0⟩ := by
  cases a
  simp only [HeatScalarJet.mul, HeatScalarJet.unitInverse] at ⊢
  simp only at ha
  subst_vars
  simp
  ring

def HeatScalarJet.ofPolynomial (p : Polynomial ℝ) : HeatScalarJet :=
  ⟨p.coeff 0, p.coeff 1, p.coeff 2⟩

/-- The truncated product is exactly the product of ordinary polynomial
coefficients in degrees zero, one, and two. -/
theorem heatScalarJet_mul_polynomial (p q : Polynomial ℝ) :
    HeatScalarJet.ofPolynomial (p * q) = (HeatScalarJet.ofPolynomial p).mul (HeatScalarJet.ofPolynomial q) := by
  have h₁ : Finset.antidiagonal (1 : ℕ) = {(0, 1), (1, 0)} := by decide
  have h₂ : Finset.antidiagonal (2 : ℕ) = {(0, 2), (1, 1), (2, 0)} := by decide
  simp [HeatScalarJet.ofPolynomial, HeatScalarJet.mul, Polynomial.coeff_mul, h₁, h₂, add_assoc]

private abbrev Components := ℝ × ℝ × ℝ

private structure VectorJet where
  constant : Components
  linear : Components
  quadratic : Components

private def vectorScale (c : ℝ) (v : Components) : Components :=
  (c * v.1, c * v.2.1, c * v.2.2)

private def vectorZero : Components := (0, 0, 0)

private def dotJet (dot : Components → Components → ℝ) (a b : VectorJet) : HeatScalarJet :=
  ⟨dot a.constant b.constant,
    dot a.constant b.linear + dot a.linear b.constant,
    dot a.constant b.quadratic + dot a.linear b.linear + dot a.quadratic b.constant⟩

private def normalizedDenominator (q u : ℝ) (dot : Components → Components → ℝ)
    (h : VectorJet) : HeatScalarJet :=
  (dotJet dot h h).scale q |>.add ⟨1 - q * u, 0, 0⟩

/-- The literal numerator, the two normalized fermion denominators, and
the direct Wilson contact, with all products taken through degree two. -/
def heatBubbleContactJet (u k₁ k₂ q : ℝ) : HeatScalarJet :=
  let dot := heatGram u k₁ k₂
  let minus : VectorJet :=
    ⟨heatK, vectorScale (-1 / 2) (heatH₁ k₁), vectorScale (1 / 8) (heatH₁₁ k₁)⟩
  let plus : VectorJet :=
    ⟨heatK, vectorScale (1 / 2) (heatH₁ k₁), vectorScale (1 / 8) (heatH₁₁ k₁)⟩
  let mark : VectorJet :=
    ⟨heatH₂ k₂, vectorZero, vectorScale (1 / 24) (heatH₁₁₂ k₁ k₂)⟩
  let markSquare := dotJet dot mark mark
  let mixed := ((dotJet dot minus mark).mul (dotJet dot plus mark)).scale 2
  let crossed := (dotJet dot minus plus).mul markSquare
  let numerator := (mixed.sub crossed).scale (q ^ 2) |>.sub (markSquare.scale (q * (1 - q * u)))
  let denominator := (normalizedDenominator q u dot minus).mul (normalizedDenominator q u dot plus)
  let contact := dotJet dot ⟨heatK, vectorZero, vectorZero⟩
    ⟨(4 * k₂ ^ 2 - 2, 0, -4 * k₂), vectorZero, vectorScale (1 / 12) (heatH₁₁₂₂ k₁ k₂)⟩
  (numerator.mul denominator.unitInverse).sub (contact.scale q)

/-- Expansion of the literal bubble and contact gives the quadratic
coefficient used in the spherical and radial sign calculation. -/
theorem heatBubbleContactJet_quadratic (u k₁ k₂ q : ℝ) :
    (heatBubbleContactJet u k₁ k₂ q).quadratic = heatTwoMarkQuadratic u k₁ k₂ q := by
  simp only [heatBubbleContactJet, heatTwoMarkQuadratic, normalizedDenominator, dotJet,
    vectorScale, vectorZero, HeatScalarJet.add, HeatScalarJet.sub, HeatScalarJet.scale,
    HeatScalarJet.mul, HeatScalarJet.unitInverse, heatGram, heatK, heatH₁, heatH₁₁, heatH₂,
    heatH₁₁₂, heatH₁₁₂₂]
  ring

end UV.HeatMaxwell
