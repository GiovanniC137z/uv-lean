import UV.ContinueGaugeRootDifferential
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The integrated diagonal of the complete normalized magnetic fibre
expansion. The continuous conserved wave number uses dk/(2π). -/

noncomputable section
open Real MeasureTheory Filter
open scoped ENNReal
namespace UV.RootMagnetic

def landauFibreDiagonal (b t x : ℝ) (n : ℕ) (k : ℝ) : ℝ :=
  exp (-(landauLevel |b| n*t)) * (‖normalizedLandauMode |b| n (x+k/b)‖^2/(2*π))

private theorem landauFibreDiagonal_nonnegative (b t x : ℝ) (n : ℕ) (k : ℝ) :
    0 ≤ landauFibreDiagonal b t x n k := by unfold landauFibreDiagonal; positivity

private theorem landauFibreDiagonal_measurable (b t x : ℝ) (n : ℕ) :
    Measurable (landauFibreDiagonal b t x n) := by
  have hn : Continuous (normalizedLandauMode |b| n) :=
    Complex.continuous_ofReal.comp (real_mode_smooth |b| n).continuous
  unfold landauFibreDiagonal
  fun_prop

theorem normalized_landau_level_integral {b : ℝ} (hb : b ≠ 0) (t x : ℝ) (n : ℕ) :
    ∫ k, landauFibreDiagonal b t x n k =
      exp (-((2*(n:ℝ)+1)*(|b| * t))) * (|b|/(2*π)) := by
  unfold landauFibreDiagonal
  rw [integral_const_mul, root_landau_level_density b x _ (root_landau_mode_norm (abs_pos.2 hb) n)]
  simp only [landauLevel, mul_assoc]

private theorem normalized_landau_level_integrable {b : ℝ} (hb : b ≠ 0) (t x : ℝ) (n : ℕ) :
    Integrable (landauFibreDiagonal b t x n) := by
  by_contra h
  have hI := normalized_landau_level_integral hb t x n
  rw [integral_undef h] at hI
  exact (mul_pos (exp_pos _) (div_pos (abs_pos.2 hb) (mul_pos two_pos Real.pi_pos))).ne' hI.symm

/-- Tonelli applied to the actual spectral diagonal before the wave-number
integral gives the scalar heat density, with the free two-dimensional
factor restored on the right. The nonnegative sum may be taken first. -/
theorem normalized_landau_fibre_heat {b t : ℝ} (hb : b ≠ 0) (ht : 0 < t) (x : ℝ) :
    (∫⁻ k, ∑' n : ℕ, ENNReal.ofReal (landauFibreDiagonal b t x n k)) =
      ENNReal.ofReal (4*π*t * UV.ContinueNormalHolonomy.scalarMagneticDiagonal b t) := by
  have hmeas (n : ℕ) : AEMeasurable (fun k => ENNReal.ofReal (landauFibreDiagonal b t x n k)) volume :=
    (ENNReal.measurable_ofReal.comp (landauFibreDiagonal_measurable b t x n)).aemeasurable
  rw [lintegral_tsum hmeas]
  have hLI (n : ℕ) : (∫⁻ k, ENNReal.ofReal (landauFibreDiagonal b t x n k)) =
      ENNReal.ofReal (exp (-((2*(n:ℝ)+1)*(|b| * t))) * (|b|/(2*π))) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (normalized_landau_level_integrable hb t x n)
      (Eventually.of_forall (landauFibreDiagonal_nonnegative b t x n)),
      normalized_landau_level_integral hb t x n]
  simp_rw [hLI]
  have hsum : Summable (fun n : ℕ => exp (-((2*(n:ℝ)+1)*(|b| * t)))) := by
    have he (n : ℕ) : exp (-((2*(n:ℝ)+1)*(|b| * t))) =
        exp (-(|b| * t)) * (exp (-(2 * |b| * t)))^n := by
      rw [← exp_nat_mul, ← exp_add]; congr 1; ring
    simp_rw [he]
    exact (summable_geometric_of_lt_one (exp_nonneg _) (exp_lt_one_iff.2 (by
      have h : 0 < 2 * |b| * t := by positivity
      linarith))).mul_left _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hsum.mul_right (|b|/(2*π))),
    tsum_mul_right, UV.ContinueNormalHolonomy.scalarMagneticDiagonal_landau hb ht]
  congr 1
  field_simp [Real.pi_ne_zero,ht.ne']
  ring
  apply tsum_congr
  intro n
  congr 1
  ring

end UV.RootMagnetic
