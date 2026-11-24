import UV.ContinueCompressedModesPairRelative

/-! The original relative-momentum tensor coefficient with both
external field strengths and both ordered carrier denominators. -/

noncomputable section
open MeasureTheory UV.SectorPlane
open scoped BigOperators
namespace UV.PairCurvature

private def pairExternalField (φ : Fin 4 → Fin 4 → ℂ) (Q : DiracMomentum)
    (u : UnitVector DiracMomentum) (a : Fin 4 × Fin 4) :=
  φ a.1 a.2 * (((Q a.1*u.val a.2-Q a.2*u.val a.1)/2:ℝ):ℂ)

private theorem pairExternalField_bound (φ : Fin 4 → Fin 4 → ℂ) (hφ : ∀ i j, ‖φ i j‖ ≤ 1)
    (Q : DiracMomentum) (u : UnitVector DiracMomentum) (a : Fin 4 × Fin 4) :
    ‖pairExternalField φ Q u a‖ ≤ ‖Q‖ := by
  have hu (i : Fin 4) : |u.val i| ≤ 1 := by
    simpa only [← Real.norm_eq_abs,u.property] using PiLp.norm_apply_le u.val i
  have hQ (i : Fin 4) : |Q i| ≤ ‖Q‖ := PiLp.norm_apply_le Q i
  have hf : |(Q a.1*u.val a.2-Q a.2*u.val a.1)/2| ≤ ‖Q‖ := by
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    apply (div_le_iff₀ (by norm_num)).2
    calc
      _ ≤ |Q a.1*u.val a.2|+|Q a.2*u.val a.1| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (Q a.1*u.val a.2) (Q a.2*u.val a.1)
      _ ≤ _ := by
        simp only [abs_mul]
        nlinarith [mul_le_mul (hQ a.1) (hu a.2) (abs_nonneg _) (norm_nonneg Q),
          mul_le_mul (hQ a.2) (hu a.1) (abs_nonneg _) (norm_nonneg Q)]
  rw [pairExternalField,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul (hφ _ _) hf (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

private def relativeOrderedResponse (φ : Fin 4 → Fin 4 → ℂ) (m ℓ ω : ℝ)
    (P : ChargeSpatialMomentum) (Q : DiracMomentum) (u v : UnitVector DiracMomentum) : ℂ :=
  ∑ a : Fin 4 × Fin 4, ∑ b : Fin 4 × Fin 4,
    pairExternalField φ Q u a * star (pairExternalField φ Q v b) *
      ∫ k, rawTransfer m ℓ ω P k b.1 b.2 a.1 a.2

def relativeTwoSourceResponse (φ : Fin 4 → Fin 4 → ℂ) (m ℓ ω : ℝ)
    (P : ChargeSpatialMomentum) (Q : DiracMomentum) (u v : UnitVector DiracMomentum) : ℂ :=
  relativeOrderedResponse φ m ℓ ω P Q u v + relativeOrderedResponse φ m ℓ (-ω) P Q v u

/-- The undisintegrated transfer of the physical spin-tensor entries
has a uniform quadratic bound in the Euclidean external four-momentum.
The estimate uses the original spin spaces at their distinct momenta. -/
theorem relative_two_source_quadratic (φ : Fin 4 → Fin 4 → ℂ) (hφ : ∀ i j, ‖φ i j‖ ≤ 1)
    {m ℓ : ℝ} (hm : 0 < m) (hℓ : 0 < ℓ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ChargeSpatialMomentum), ‖P‖ ≤ R →
      ∀ (ω : ℝ) (Q : DiracMomentum) (u v : UnitVector DiracMomentum),
        ‖relativeTwoSourceResponse φ m ℓ ω P Q u v‖ ≤ C*‖Q‖^2 := by
  obtain ⟨B,hB,hAbs⟩ := rawTransfer_absolute_uniform hm hℓ hR
  refine ⟨512*B,by positivity,?_⟩
  intro P hP ω Q u v
  have hOrder (W : ℝ) (u v : UnitVector DiracMomentum) :
      ‖relativeOrderedResponse φ m ℓ W P Q u v‖ ≤ 256*B*‖Q‖^2 := by
    have hTerm (a b : Fin 4 × Fin 4) :
        ‖pairExternalField φ Q u a * star (pairExternalField φ Q v b) *
          ∫ k, rawTransfer m ℓ W P k b.1 b.2 a.1 a.2‖ ≤ ‖Q‖*‖Q‖*B := by
      have hI := (norm_integral_le_integral_norm (fun k => rawTransfer m ℓ W P k b.1 b.2 a.1 a.2)).trans
        (hAbs P hP W b.1 b.2 a.1 a.2)
      rw [norm_mul,norm_mul,norm_star]
      exact mul_le_mul (mul_le_mul (pairExternalField_bound φ hφ Q u a) (pairExternalField_bound φ hφ Q v b)
        (norm_nonneg _) (norm_nonneg _)) hI (norm_nonneg _) (by positivity)
    unfold relativeOrderedResponse
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _a : Fin 4 × Fin 4, ∑ _b : Fin 4 × Fin 4, ‖Q‖*‖Q‖*B :=
        Finset.sum_le_sum (fun a _ => (norm_sum_le _ _).trans (Finset.sum_le_sum (fun b _ => hTerm a b)))
      _ = _ := by simp [nsmul_eq_mul]; ring
  unfold relativeTwoSourceResponse
  calc
    _ ≤ 256*B*‖Q‖^2 + 256*B*‖Q‖^2 := (norm_add_le _ _).trans
      (add_le_add (hOrder ω u v) (hOrder (-ω) v u))
    _ = _ := by ring

end UV.PairCurvature
