import UV.ContinueRetainedGaussianSchur
import Mathlib.MeasureTheory.Integral.Pi

/-! Gaussian mass on the four Cartesian components of the retained loop
momenta. The Gaussian seam density is evaluated at zero before integrating
the characteristic in the loop variables. -/

noncomputable section

open Matrix MeasureTheory Set
open scoped Matrix BigOperators InnerProductSpace ENNReal

namespace UV

variable {R : Type*} [Fintype R] [DecidableEq R]

/-- A centered Gaussian factor with real quadratic form (x^T A x/2). -/
def retainedGaussian (A : Matrix R R ℝ) (x : EuclideanSpace ℝ R) : ℝ :=
  Real.exp (-(((WithLp.ofLp x) ⬝ᵥ (A *ᵥ WithLp.ofLp x)) / 2))

omit [DecidableEq R] in
theorem retainedGaussian_ofReal (A : Matrix R R ℝ) (x : EuclideanSpace ℝ R) :
    (retainedGaussian A x : ℂ) = networkSPDWave ((2 : ℝ) • A) 0 x := by
  simp only [networkSPDWave, inner_zero_left, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_mul, retainedGaussian, smul_mulVec, dotProduct_smul, smul_eq_mul]
  congr 2
  ring

theorem retainedGaussian_integrable (A : Matrix R R ℝ) (hA : A.PosDef) :
    Integrable (retainedGaussian A) := by
  have hw := networkSPDWave_integrable ((2 : ℝ) • A) (hA.smul (by norm_num)) 0
  have he (x : EuclideanSpace ℝ R) :
      ‖networkSPDWave ((2 : ℝ) • A) 0 x‖ = retainedGaussian A x := by
    rw [← retainedGaussian_ofReal, Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ retainedGaussian A x from (Real.exp_pos _).le)]
  simpa only [he] using hw.norm

theorem retainedGaussian_integral (A : Matrix R R ℝ) (hA : A.PosDef) :
    (∫ x, retainedGaussian A x) = Real.sqrt ((2 * Real.pi) ^ Fintype.card R / A.det) := by
  have hw := networkSPDWave_integral ((2 : ℝ) • A) (hA.smul (by norm_num)) 0
  simp_rw [← retainedGaussian_ofReal, integral_complex_ofReal] at hw
  simp only [WithLp.ofLp_zero, mulVec_zero, dotProduct_zero, neg_zero, Real.exp_zero,
    mul_one] at hw
  apply Complex.ofReal_injective
  rw [hw, det_smul, show 4 * Real.pi = 2 * (2 * Real.pi) by ring, mul_pow]
  have hp : (2 : ℝ) ^ Fintype.card R ≠ 0 := pow_ne_zero _ (by norm_num)
  congr 2
  exact mul_div_mul_left _ _ hp

/-- Independent four-dimensional Cartesian product over all score rows. -/
def retainedFourGaussian (A : Matrix R R ℝ) (x : Fin 4 → EuclideanSpace ℝ R) : ℝ :=
  ∏ μ, retainedGaussian A (x μ)

omit [DecidableEq R] in
theorem retainedFourGaussian_pos (A : Matrix R R ℝ) (x : Fin 4 → EuclideanSpace ℝ R) :
    0 < retainedFourGaussian A x := Finset.prod_pos fun _ _ => Real.exp_pos _

theorem retainedFourGaussian_integrable (A : Matrix R R ℝ) (hA : A.PosDef) :
    Integrable (retainedFourGaussian A) :=
  Integrable.fintype_prod fun _ => retainedGaussian_integrable A hA

theorem retainedFourGaussian_integral (A : Matrix R R ℝ) (hA : A.PosDef) :
    (∫ x, retainedFourGaussian A x) = ((2 * Real.pi) ^ Fintype.card R / A.det) ^ 2 := by
  unfold retainedFourGaussian
  rw [integral_fintype_prod_volume_eq_pow, retainedGaussian_integral A hA,
    Fintype.card_fin, show (4 : ℕ) = 2 * 2 by decide, pow_mul, Real.sq_sqrt]
  exact div_nonneg (by positivity) hA.det_pos.le

/-- The centered seam density evaluated at the sewn value zero. -/
def retainedSeamDensityAtZero (A : Matrix R R ℝ) : ℝ :=
  (∫ x, retainedFourGaussian A⁻¹ x)⁻¹

theorem retainedSeamDensityAtZero_formula (A : Matrix R R ℝ) (hA : A.PosDef) :
    retainedSeamDensityAtZero A =
      ((2 * Real.pi) ^ (2 * Fintype.card R) * A.det ^ 2)⁻¹ := by
  rw [retainedSeamDensityAtZero, retainedFourGaussian_integral A⁻¹ hA.inv,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv, div_inv_eq_mul, mul_pow, ← pow_mul]
  congr 3
  exact Nat.mul_comm _ _

variable {E S L : Type*} [Fintype E] [Fintype S] [Fintype L]
variable [DecidableEq E] [DecidableEq S] [DecidableEq L]

/-- The absolute Fourier mass with the seam factor and the loop normalization,
in the four normalized Cartesian coordinates. -/
def retainedK0 (t : E → ℝ) (C : Matrix S E ℝ) (J : Matrix L E ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (retainedSeamDensityAtZero (retainedGram t C) /
    (2 * Real.pi) ^ (4 * Fintype.card L)) *
    ∫⁻ x, ENNReal.ofReal (retainedFourGaussian (retainedSchur t C J) x)

theorem retainedK0_eq (t : E → ℝ) (ht : ∀ e, 0 < t e)
    (C : Matrix S E ℝ) (J : Matrix L E ℝ) (hC : C.rank = Fintype.card S)
    (hM : (fromRows C J).rank = Fintype.card S + Fintype.card L) :
    retainedK0 t C J =
      ENNReal.ofReal (((2 * Real.pi) ^ (2 * (Fintype.card S + Fintype.card L)) *
        (retainedGram t (fromRows C J)).det ^ 2)⁻¹) := by
  have hA := (retainedGram_posDef_iff_rank t ht C).mpr hC
  have hQ := (retainedSchur_posDef_iff_rank t ht C J hC).mpr hM
  have hi := ofReal_integral_eq_lintegral_ofReal (retainedFourGaussian_integrable _ hQ)
    (ae_of_all _ fun x => (retainedFourGaussian_pos (retainedSchur t C J) x).le)
  rw [retainedK0, ← hi, retainedFourGaussian_integral _ hQ, retainedSeamDensityAtZero_formula _ hA,
    ← ENNReal.ofReal_mul (by positivity), ← retainedSchur_det t ht C J hC]
  congr 1
  have hpi : 0 < 2 * Real.pi := by positivity
  have h4 (n : ℕ) : (2 * Real.pi) ^ (4 * n) = ((2 * Real.pi) ^ n) ^ 4 := by
    rw [Nat.mul_comm, pow_mul]
  have h2 (n : ℕ) : (2 * Real.pi) ^ (2 * n) = ((2 * Real.pi) ^ n) ^ 2 := by
    rw [Nat.mul_comm, pow_mul]
  rw [Nat.mul_add, pow_add, h2 (Fintype.card S), h2 (Fintype.card L), h4]
  field_simp [hA.det_pos.ne', hQ.det_pos.ne', hpi.ne']

end UV
