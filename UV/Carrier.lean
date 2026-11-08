import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic

/-! The scalar carrier in its two-character realization ℂ × ℂ.
This is the explicit character model, not a formal construction of the quotient.
Source: prop:carrier-reality-adjoint. -/

noncomputable section
namespace UV.Carrier

abbrev Algebra := ℂ × ℂ

def generator : Algebra := (1, -1)
def reality (z : Algebra) : Algebra := (star z.2, star z.1)

@[simp] theorem reality_involutive (z : Algebra) : reality (reality z) = z := by
  simp [reality]

@[simp] theorem generator_sq : generator * generator = 1 := by
  ext <;> norm_num [generator]

@[simp] theorem reality_generator : reality generator = -generator := by
  ext <;> norm_num [reality, generator]

theorem reality_generator_mul_generator : reality generator * generator = -1 := by
  rw [reality_generator, neg_mul, generator_sq]

theorem character_reality (z : Algebra) :
    (reality z).1 = star z.2 ∧ (reality z).2 = star z.1 := ⟨rfl, rfl⟩

/-- No normalized complex-linear functional can be positive for this reality. -/
theorem no_normalized_positive_functional :
    ¬ ∃ ω : Algebra →ₗ[ℂ] ℂ, ω 1 = 1 ∧
      ∀ z : Algebra, 0 ≤ (ω (reality z * z)).re := by
  rintro ⟨ω, hω, hpos⟩
  have h := hpos generator
  rw [reality_generator_mul_generator, map_neg, hω] at h
  norm_num at h

end UV.Carrier
