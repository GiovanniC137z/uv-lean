import UV.ContinueRetainedGaussianMass
import Mathlib.Probability.Distributions.Gaussian.Real

/-! The Gaussian sewing calculation by Fourier integration at the zero seam
value. Both the loop score and the seam score use the actual displacement
columns and their independent positive-width Gaussian laws. -/

noncomputable section

open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators InnerProductSpace ENNReal

namespace UV

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Independent Gaussian displacement slots in one Cartesian direction. -/
def retainedSlotMeasure (t : E → ℝ) : Measure (E → ℝ) :=
  Measure.pi fun e => gaussianReal 0 (Real.toNNReal (t e))

/-- Characteristic of the row scores in a single Cartesian direction. -/
def retainedSlotCharacteristic {R : Type*} [Fintype R]
    (t : E → ℝ) (A : Matrix R E ℝ) (u : EuclideanSpace ℝ R) : ℂ :=
  ∫ y, Complex.exp (((WithLp.ofLp u) ⬝ᵥ A *ᵥ y : ℝ) * Complex.I) ∂retainedSlotMeasure t

omit [DecidableEq E] in
private theorem retained_dot_transpose (R : Type*) [Fintype R]
    (A : Matrix R E ℝ) (x : R → ℝ) (y : E → ℝ) :
    x ⬝ᵥ A *ᵥ y = ∑ e, y e * ((Aᵀ *ᵥ x) e) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
  rfl

theorem retainedSlotCharacteristic_eq {R : Type*} [Fintype R]
    (t : E → ℝ) (ht : ∀ e, 0 ≤ t e) (A : Matrix R E ℝ) (u : EuclideanSpace ℝ R) :
    retainedSlotCharacteristic t A u = (retainedGaussian (retainedGram t A) u : ℂ) := by
  let x := WithLp.ofLp u
  let p := Aᵀ *ᵥ x
  have hphase (y : E → ℝ) :
      Complex.exp (((x ⬝ᵥ A *ᵥ y : ℝ) : ℂ) * Complex.I) =
        ∏ e, Complex.exp (((p e * y e : ℝ) : ℂ) * Complex.I) := by
    rw [retained_dot_transpose, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro e _
    rw [mul_comm (y e)]
  have hgram : x ⬝ᵥ retainedGram t A *ᵥ x = ∑ e, t e * p e ^ 2 := by
    rw [retainedGram, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
      ← mulVec_transpose]
    apply Finset.sum_congr rfl
    intro e _
    change p e * (diagonal t *ᵥ p) e = t e * p e ^ 2
    rw [mulVec_diagonal]
    ring
  have he (e : E) :
      (∫ y : ℝ, Complex.exp (((p e * y : ℝ) : ℂ) * Complex.I)
        ∂gaussianReal 0 (Real.toNNReal (t e))) =
        (Real.exp (-(t e * p e ^ 2 / 2)) : ℂ) := by
    simp_rw [Complex.ofReal_mul]
    rw [← charFun_apply_real, charFun_gaussianReal, Complex.ofReal_exp]
    push_cast
    rw [Real.coe_toNNReal _ (ht e)]
    ring_nf
  change (∫ y, Complex.exp (((x ⬝ᵥ A *ᵥ y : ℝ) : ℂ) * Complex.I)
    ∂retainedSlotMeasure t) = _
  unfold retainedSlotMeasure
  simp_rw [hphase]
  rw [integral_fintype_prod_eq_prod (fun e y => Complex.exp (((p e * y : ℝ) : ℂ) * Complex.I))]
  simp_rw [he]
  simp only [retainedGaussian]
  change _ = (Real.exp (-(x ⬝ᵥ retainedGram t A *ᵥ x / 2)) : ℂ)
  rw [hgram, Finset.sum_div, ← Finset.sum_neg_distrib, Real.exp_sum, Complex.ofReal_prod]

variable {S L : Type*} [Fintype S] [Fintype L] [DecidableEq S]

/-- Sew a single Cartesian direction by Fourier inversion in the seam dual
variable at zero. -/
def retainedSewnOne (t : E → ℝ) (C : Matrix S E ℝ) (J : Matrix L E ℝ)
    (v : EuclideanSpace ℝ L) : ℂ :=
  (∫ u : EuclideanSpace ℝ S, retainedSlotCharacteristic t (fromRows C J)
    (WithLp.toLp 2 ((WithLp.ofLp u) ⊕ᵥ (WithLp.ofLp v)))) /
      ((2 * Real.pi : ℝ) : ℂ) ^ Fintype.card S

theorem retainedSewnOne_eq (t : E → ℝ) (ht : ∀ e, 0 < t e)
    (C : Matrix S E ℝ) (J : Matrix L E ℝ) (hC : C.rank = Fintype.card S)
    (v : EuclideanSpace ℝ L) :
    retainedSewnOne t C J v = ((retainedGaussian (retainedSchur t C J) v *
      (∫ u, retainedGaussian (retainedGram t C) u) /
        (2 * Real.pi) ^ Fintype.card S : ℝ) : ℂ) := by
  have hA := (retainedGram_posDef_iff_rank t ht C).mpr hC
  letI := hA.isUnit.invertible
  let shift : EuclideanSpace ℝ S :=
    WithLp.toLp 2 (((retainedGram t C)⁻¹ * retainedCross t C J) *ᵥ WithLp.ofLp v)
  have hintegrand (u : EuclideanSpace ℝ S) :
      retainedSlotCharacteristic t (fromRows C J)
        (WithLp.toLp 2 ((WithLp.ofLp u) ⊕ᵥ (WithLp.ofLp v))) =
      ((retainedGaussian (retainedSchur t C J) v * retainedGaussian (retainedGram t C) (u + shift) : ℝ) : ℂ) := by
    rw [retainedSlotCharacteristic_eq t (fun e => (ht e).le), retainedGram_fromRows]
    have hs := schur_complement_eq₁₁ (retainedCross t C J) (retainedGram t J)
      (WithLp.ofLp u) (WithLp.ofLp v) hA.1
    simp only [star_trivial, ← dotProduct_mulVec] at hs
    simp only [retainedGaussian, WithLp.ofLp_toLp, WithLp.ofLp_add]
    change (Real.exp (-(((WithLp.ofLp u ⊕ᵥ WithLp.ofLp v) ⬝ᵥ
      fromBlocks (retainedGram t C) (retainedCross t C J) (retainedCross t C J)ᴴ
        (retainedGram t J) *ᵥ (WithLp.ofLp u ⊕ᵥ WithLp.ofLp v)) / 2)) : ℂ) = _
    rw [hs]
    simp only [retainedSchur, shift, WithLp.ofLp_toLp, add_div, neg_add, Real.exp_add]
    rw [mul_comm]
  simp only [retainedSewnOne, hintegrand, integral_complex_ofReal, integral_const_mul,
    integral_add_right_eq_self, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]

/-- The unnormalized sewn Fourier coefficient in the four independent slots. -/
def retainedSewnFourier (t : E → ℝ) (C : Matrix S E ℝ) (J : Matrix L E ℝ)
    (v : Fin 4 → EuclideanSpace ℝ L) : ℂ :=
  ∏ μ, retainedSewnOne t C J (v μ)

theorem retainedSewnFourier_eq (t : E → ℝ) (ht : ∀ e, 0 < t e)
    (C : Matrix S E ℝ) (J : Matrix L E ℝ) (hC : C.rank = Fintype.card S)
    (v : Fin 4 → EuclideanSpace ℝ L) :
    retainedSewnFourier t C J v =
      ((retainedSeamDensityAtZero (retainedGram t C) *
        retainedFourGaussian (retainedSchur t C J) v : ℝ) : ℂ) := by
  have hA := (retainedGram_posDef_iff_rank t ht C).mpr hC
  unfold retainedSewnFourier
  simp_rw [retainedSewnOne_eq t ht C J hC]
  rw [← Complex.ofReal_prod]
  rw [Complex.ofReal_inj]
  simp_rw [mul_div_assoc]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← retainedFourGaussian, retainedSeamDensityAtZero_formula _ hA,
    retainedGaussian_integral _ hA, div_pow, show (4 : ℕ) = 2 * 2 by decide,
    pow_mul (Real.sqrt _), Real.sq_sqrt (div_nonneg (by positivity) hA.det_pos.le)]
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [Nat.mul_comm 2 (Fintype.card S), pow_mul]
  field_simp [hA.det_pos.ne', hpi.ne']
  rw [pow_mul]

/-- The actual absolute sewn Fourier mass with the loop measure normalized
by the full (4L)-dimensional Fourier factor. -/
theorem retainedK0_integral_sewn (t : E → ℝ) (ht : ∀ e, 0 < t e)
    (C : Matrix S E ℝ) (J : Matrix L E ℝ) (hC : C.rank = Fintype.card S) :
    retainedK0 t C J = ∫⁻ v, ENNReal.ofReal
      (‖retainedSewnFourier t C J v‖ / (2 * Real.pi) ^ (4 * Fintype.card L)) := by
  have hA := (retainedGram_posDef_iff_rank t ht C).mpr hC
  have hseam : 0 ≤ retainedSeamDensityAtZero (retainedGram t C) := by
    rw [retainedSeamDensityAtZero_formula _ hA]
    positivity
  have hm (v : Fin 4 → EuclideanSpace ℝ L) :
      ‖retainedSewnFourier t C J v‖ =
        retainedSeamDensityAtZero (retainedGram t C) * retainedFourGaussian (retainedSchur t C J) v := by
    rw [retainedSewnFourier_eq t ht C J hC, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg hseam (retainedFourGaussian_pos _ _).le)]
  rw [retainedK0, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext v
  rw [hm, mul_div_right_comm, ENNReal.ofReal_mul (div_nonneg hseam (by positivity))]

end UV
