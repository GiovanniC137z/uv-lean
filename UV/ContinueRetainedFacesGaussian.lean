import UV.ContinueRetainedFacesPhysical
import UV.ContinueRetainedGaussianMomentTransport

/-! The retained loop-score criterion for the normalized sewn Fourier
mass itself, including the four independent Cartesian loop slots. -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace UV

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ] {n : ℕ}

/-- The normalized physical retained-score Gaussian moment is width
integrable exactly under the strict simultaneous-face inequalities,
when the remaining density has the stated two-sided power bounds. -/
theorem retainedK_widthIntegral_finite_iff_faces
    (C : Matrix ι (Fin n) ℝ) (J : Matrix κ (Fin n) ℝ)
    (hC : C.rank = Fintype.card ι)
    (hM : (Matrix.fromRows C J).rank = Fintype.card ι + Fintype.card κ)
    (β : Fin n → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (ρ : (Fin n → ℝ) → ℝ≥0∞) (lo hi : ℝ≥0∞)
    (hlo : lo ≠ 0) (hlo' : lo ≠ ⊤) (hhi : hi ≠ ⊤)
    (hρ : ∀ᵐ t ∂directionalSchwingerMeasure (Fin n),
      lo * ENNReal.ofReal (retainedWidthDensity β t) ≤ ρ t ∧
        ρ t ≤ hi * ENNReal.ofReal (retainedWidthDensity β t)) :
    (∫⁻ t, ρ t * retainedK h t C J ∂directionalSchwingerMeasure (Fin n)) < ⊤ ↔
      ∀ S : Finset (Fin n), S.Nonempty → retainedFaceAdmissible β h
        (retainedWidthDefect (Matrix.fromRows C J))
        (retainedWidthMissingScore (Matrix.fromRows C J)) S := by
  obtain ⟨l, u, hl, hu, hcomp⟩ := retainedK_comparison (E := Fin n) (S := ι) (L := κ) h hh
  refine retainedPhysicalWidth_finite_iff_faces C J hC hM β hh ρ
    (fun t => retainedK h t C J) lo hi (min l 1) u hlo hlo' hhi
    (lt_min hl zero_lt_one).ne' ((min_le_right l 1).trans_lt ENNReal.one_lt_top).ne hu.ne hρ ?_
  filter_upwards [retainedWidth_ae_positive (n := n)] with t ht
  obtain ⟨hblo, hbhi⟩ := hcomp t ht C J hC hM
  exact ⟨(mul_le_mul_right' (min_le_left l 1) _).trans hblo, hbhi⟩

/-- Only an upper bound on the remaining width density is needed for
convergence of the same normalized retained-score Gaussian moment. -/
theorem retainedK_widthIntegral_finite_of_upper
    (C : Matrix ι (Fin n) ℝ) (J : Matrix κ (Fin n) ℝ)
    (hC : C.rank = Fintype.card ι)
    (hM : (Matrix.fromRows C J).rank = Fintype.card ι + Fintype.card κ)
    (β : Fin n → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (ρ : (Fin n → ℝ) → ℝ≥0∞) (hi : ℝ≥0∞) (hhi : hi ≠ ⊤)
    (hρ : ∀ᵐ t ∂directionalSchwingerMeasure (Fin n),
      ρ t ≤ hi * ENNReal.ofReal (retainedWidthDensity β t))
    (faces : ∀ S : Finset (Fin n), S.Nonempty → retainedFaceAdmissible β h
      (retainedWidthDefect (Matrix.fromRows C J))
      (retainedWidthMissingScore (Matrix.fromRows C J)) S) :
    (∫⁻ t, ρ t * retainedK h t C J ∂directionalSchwingerMeasure (Fin n)) < ⊤ := by
  obtain ⟨_, u, _, hu, hcomp⟩ := retainedK_comparison (E := Fin n) (S := ι) (L := κ) h hh
  refine retainedPhysicalWidth_finite_of_upper C J hC hM β hh ρ
    (fun t => retainedK h t C J) hi u hhi hu.ne hρ ?_ faces
  filter_upwards [retainedWidth_ae_positive (n := n)] with t ht
  exact (hcomp t ht C J hC hM).2

end UV
