import UV.ContinueRetainedFaces
import UV.ContinueRetainedGaussianMass
import UV.ContinueRetainedGaussianCofactor

/-! Applying the retained-face theorem to the actual Gaussian
normalization and to width measures bounded by the model density. -/

noncomputable section

open Function Set Finset MeasureTheory Filter
open scoped BigOperators ENNReal

namespace UV

/-- Widths are positive on the support of the product Lebesgue measure. -/
theorem retainedWidth_ae_positive {n : ℕ} :
    ∀ᵐ t : Fin n → ℝ ∂directionalSchwingerMeasure (Fin n), ∀ e, 0 < t e := by
  apply ae_all_iff.mpr
  intro e
  refine ((Measure.quasiMeasurePreserving_eval _ e).ae
    (ae_restrict_mem (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) 1)))).mono ?_
  exact fun t ht => ht.1

/-- The endpoint at width one has Lebesgue mass zero, so the reference
measure is exactly product Lebesgue measure on the manuscript's
half-open unit-width box. -/
theorem retainedWidthMeasure_eq_Ioc (n : ℕ) :
    directionalSchwingerMeasure (Fin n) =
      (volume : Measure (Fin n → ℝ)).restrict (univ.pi (fun _ => Ioc (0 : ℝ) 1)) := by
  unfold directionalSchwingerMeasure
  rw [volume_pi, Measure.restrict_pi_pi]
  simp only [restrict_Ioo_eq_restrict_Ioc]

theorem retainedIntegral_comparable {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (f g : E → ℝ≥0∞) (lo hi : ℝ≥0∞) (hlo : lo ≠ 0) (hlo' : lo ≠ ⊤) (hhi : hi ≠ ⊤)
    (hb : ∀ᵐ t ∂μ, lo * g t ≤ f t ∧ f t ≤ hi * g t) :
    (∫⁻ t, f t ∂μ) < ⊤ ↔ (∫⁻ t, g t ∂μ) < ⊤ := by
  constructor
  · intro hf
    have h := (lintegral_mono_ae (hb.mono fun _ ht => ht.1)).trans_lt hf
    rw [lintegral_const_mul' _ _ hlo'] at h
    by_contra! hg
    rw [top_le_iff.mp hg, ENNReal.mul_top hlo] at h
    exact (lt_irrefl _ h)
  · intro hg
    apply (lintegral_mono_ae (hb.mono fun _ ht => ht.2)).trans_lt
    rw [lintegral_const_mul' _ _ hhi]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hhi) hg

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {n : ℕ}

/-- Use any coefficient with two-sided finite positive constants
against the actual retained determinant integrand. -/
theorem retainedCoefficient_finite_iff_faces
    (A : Matrix (ι ⊕ κ) (Fin n) ℝ) (hA : A.rank = Fintype.card (ι ⊕ κ))
    (β : Fin n → ℝ) {h : ℝ} (hh : 0 ≤ h) (F : (Fin n → ℝ) → ℝ≥0∞)
    (lo hi : ℝ≥0∞) (hlo : lo ≠ 0) (hlo' : lo ≠ ⊤) (hhi : hi ≠ ⊤)
    (hb : ∀ᵐ t ∂directionalSchwingerMeasure (Fin n),
      lo * retainedCofactorWidthDensity A β h t ≤ F t ∧
        F t ≤ hi * retainedCofactorWidthDensity A β h t) :
    (∫⁻ t, F t ∂directionalSchwingerMeasure (Fin n)) < ⊤ ↔
      ∀ S : Finset (Fin n), S.Nonempty →
        retainedFaceAdmissible β h (retainedWidthDefect A) (retainedWidthMissingScore A) S :=
  (retainedIntegral_comparable _ _ _ lo hi hlo hlo' hhi hb).trans
    (retainedCofactorWidthDensity_finite_iff_faces A hA β hh)

/-- A one-sided upper density estimate suffices for convergence of the
physical coefficient under the same strict face inequalities. -/
theorem retainedCoefficient_finite_of_upper
    (A : Matrix (ι ⊕ κ) (Fin n) ℝ) (hA : A.rank = Fintype.card (ι ⊕ κ))
    (β : Fin n → ℝ) {h : ℝ} (hh : 0 ≤ h) (F : (Fin n → ℝ) → ℝ≥0∞)
    (hi : ℝ≥0∞) (hhi : hi ≠ ⊤)
    (hb : ∀ᵐ t ∂directionalSchwingerMeasure (Fin n),
      F t ≤ hi * retainedCofactorWidthDensity A β h t)
    (faces : ∀ S : Finset (Fin n), S.Nonempty →
      retainedFaceAdmissible β h (retainedWidthDefect A) (retainedWidthMissingScore A) S) :
    (∫⁻ t, F t ∂directionalSchwingerMeasure (Fin n)) < ⊤ := by
  apply (lintegral_mono_ae hb).trans_lt
  rw [lintegral_const_mul' _ _ hhi]
  exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hhi)
    ((retainedCofactorWidthDensity_finite_iff_faces A hA β hh).mpr faces)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem retainedScoreDelete_fromRows (C : Matrix ι (Fin n) ℝ) (J : Matrix κ (Fin n) ℝ)
    (q : κ) : retainedScoreDelete (Matrix.fromRows C J) q = retainedDeleteScore C J q := by
  ext (s | j) e <;> rfl

/-- For the actual unweighted normalized sewn Gaussian, the determinant
model differs pointwise by its exact width-independent normalization. -/
theorem retainedK0_widthDensity_eq
    (C : Matrix ι (Fin n) ℝ) (J : Matrix κ (Fin n) ℝ)
    (hC : C.rank = Fintype.card ι)
    (hM : (Matrix.fromRows C J).rank = Fintype.card ι + Fintype.card κ)
    (β t : Fin n → ℝ) (ht : ∀ e, 0 < t e) :
    ENNReal.ofReal (retainedWidthDensity β t) * retainedK0 t C J =
      ENNReal.ofReal (((2 * Real.pi) ^ (2 * (Fintype.card ι + Fintype.card κ)))⁻¹) *
        retainedCofactorWidthDensity (Matrix.fromRows C J) β 0 t := by
  have hβ : 0 ≤ retainedWidthDensity β t :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (ht i).le _
  have hπ : 0 ≤ ((2 * Real.pi) ^ (2 * (Fintype.card ι + Fintype.card κ)))⁻¹ := by positivity
  rw [retainedK0_eq t ht C J hC hM, retainedCofactorWidthDensity, Real.rpow_zero, mul_one,
    ← ENNReal.ofReal_mul hβ, ← ENNReal.ofReal_mul hπ]
  congr 1
  change retainedWidthDensity β t *
    ((2 * Real.pi) ^ (2 * (Fintype.card ι + Fintype.card κ)) *
      (retainedGram t (Matrix.fromRows C J)).det ^ 2)⁻¹ =
    ((2 * Real.pi) ^ (2 * (Fintype.card ι + Fintype.card κ)))⁻¹ *
      (retainedWidthDensity β t / (retainedGram t (Matrix.fromRows C J)).det ^ 2)
  rw [mul_inv, div_eq_mul_inv]
  ring

/-- The actual unweighted normalized Fourier mass has the sharp all-face
width criterion under the product model density. -/
theorem retainedK0_widthIntegral_finite_iff_faces
    (C : Matrix ι (Fin n) ℝ) (J : Matrix κ (Fin n) ℝ)
    (hC : C.rank = Fintype.card ι)
    (hM : (Matrix.fromRows C J).rank = Fintype.card ι + Fintype.card κ) (β : Fin n → ℝ) :
    (∫⁻ t, ENNReal.ofReal (retainedWidthDensity β t) * retainedK0 t C J
      ∂directionalSchwingerMeasure (Fin n)) < ⊤ ↔
      ∀ S : Finset (Fin n), S.Nonempty → retainedFaceAdmissible β 0
        (retainedWidthDefect (Matrix.fromRows C J))
        (retainedWidthMissingScore (Matrix.fromRows C J)) S := by
  let a : ℝ := ((2 * Real.pi) ^ (2 * (Fintype.card ι + Fintype.card κ)))⁻¹
  have ha : 0 < a := by dsimp only [a]; positivity
  refine retainedCoefficient_finite_iff_faces (Matrix.fromRows C J) (by simpa only [Fintype.card_sum])
    β (le_refl 0) _ (ENNReal.ofReal a) (ENNReal.ofReal a)
    (ENNReal.ofReal_ne_zero_iff.mpr ha) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top ?_
  filter_upwards [retainedWidth_ae_positive (n := n)] with t ht
  rw [retainedK0_widthDensity_eq C J hC hM β t ht]
  exact ⟨le_rfl, le_rfl⟩

/-- The determinant ratio appearing when the Gaussian carries a score
moment of order `h`. The seam and loop normalizations are in `retainedK0`. -/
def retainedPhysicalMomentModel (h : ℝ) (t : Fin n → ℝ)
    (C : Matrix ι (Fin n) ℝ) (J : Matrix κ (Fin n) ℝ) : ℝ≥0∞ :=
  retainedK0 t C J * ENNReal.ofReal ((1 + ∑ q : κ,
    (retainedGram t (retainedDeleteScore C J q)).det /
      (retainedGram t (Matrix.fromRows C J)).det) ^ h)

private theorem retainedMoment_widthDensity_eq
    (C : Matrix ι (Fin n) ℝ) (J : Matrix κ (Fin n) ℝ)
    (hC : C.rank = Fintype.card ι)
    (hM : (Matrix.fromRows C J).rank = Fintype.card ι + Fintype.card κ)
    (β t : Fin n → ℝ) (ht : ∀ e, 0 < t e) (h : ℝ) :
    ENNReal.ofReal (retainedWidthDensity β t) * retainedPhysicalMomentModel h t C J =
      ENNReal.ofReal (((2 * Real.pi) ^ (2 * (Fintype.card ι + Fintype.card κ)))⁻¹) *
        retainedCofactorWidthDensity (Matrix.fromRows C J) β h t := by
  have hβ : 0 ≤ retainedWidthDensity β t :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (ht i).le _
  rw [retainedPhysicalMomentModel, ← mul_assoc, retainedK0_widthDensity_eq C J hC hM β t ht,
    mul_assoc]
  congr 1
  unfold retainedCofactorWidthDensity
  rw [Real.rpow_zero, mul_one, ← ENNReal.ofReal_mul (div_nonneg hβ (sq_nonneg _))]
  simp_rw [retainedScoreDelete_fromRows]
  rfl

/-- Apply the face criterion to a coefficient with uniform two-sided
Gaussian-moment and width-weight estimates. Each comparison is with the
actual determinant of the stitched covariance. -/
theorem retainedPhysicalWidth_finite_iff_faces
    (C : Matrix ι (Fin n) ℝ) (J : Matrix κ (Fin n) ℝ)
    (hC : C.rank = Fintype.card ι)
    (hM : (Matrix.fromRows C J).rank = Fintype.card ι + Fintype.card κ)
    (β : Fin n → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (ρ K : (Fin n → ℝ) → ℝ≥0∞) (lρ uρ lK uK : ℝ≥0∞)
    (hlρ : lρ ≠ 0) (hlρ' : lρ ≠ ⊤) (huρ : uρ ≠ ⊤)
    (hlK : lK ≠ 0) (hlK' : lK ≠ ⊤) (huK : uK ≠ ⊤)
    (hρ : ∀ᵐ t ∂directionalSchwingerMeasure (Fin n),
      lρ * ENNReal.ofReal (retainedWidthDensity β t) ≤ ρ t ∧
        ρ t ≤ uρ * ENNReal.ofReal (retainedWidthDensity β t))
    (hK : ∀ᵐ t ∂directionalSchwingerMeasure (Fin n),
      lK * retainedPhysicalMomentModel h t C J ≤ K t ∧ K t ≤ uK * retainedPhysicalMomentModel h t C J) :
    (∫⁻ t, ρ t * K t ∂directionalSchwingerMeasure (Fin n)) < ⊤ ↔
      ∀ S : Finset (Fin n), S.Nonempty → retainedFaceAdmissible β h
        (retainedWidthDefect (Matrix.fromRows C J))
        (retainedWidthMissingScore (Matrix.fromRows C J)) S := by
  let a : ℝ := ((2 * Real.pi) ^ (2 * (Fintype.card ι + Fintype.card κ)))⁻¹
  have ha : 0 < a := by dsimp only [a]; positivity
  refine retainedCoefficient_finite_iff_faces (Matrix.fromRows C J) (by simpa only [Fintype.card_sum])
    β hh _ (lρ * lK * ENNReal.ofReal a) (uρ * uK * ENNReal.ofReal a) ?_ ?_ ?_ ?_
  · exact mul_ne_zero (mul_ne_zero hlρ hlK) (ENNReal.ofReal_ne_zero_iff.mpr ha)
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hlρ' hlK') ENNReal.ofReal_ne_top
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top huρ huK) ENNReal.ofReal_ne_top
  · filter_upwards [retainedWidth_ae_positive (n := n), hρ, hK] with t ht hr hk
    have he := retainedMoment_widthDensity_eq C J hC hM β t ht h
    rw [mul_assoc (lρ * lK), mul_assoc (uρ * uK), ← he]
    constructor
    · simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul' hr.1 hk.1
    · simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul' hr.2 hk.2

/-- An upper bound on the remaining width density and on the moment
is sufficient under the same strict face inequalities. -/
theorem retainedPhysicalWidth_finite_of_upper
    (C : Matrix ι (Fin n) ℝ) (J : Matrix κ (Fin n) ℝ)
    (hC : C.rank = Fintype.card ι)
    (hM : (Matrix.fromRows C J).rank = Fintype.card ι + Fintype.card κ)
    (β : Fin n → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (ρ K : (Fin n → ℝ) → ℝ≥0∞) (uρ uK : ℝ≥0∞) (huρ : uρ ≠ ⊤) (huK : uK ≠ ⊤)
    (hρ : ∀ᵐ t ∂directionalSchwingerMeasure (Fin n),
      ρ t ≤ uρ * ENNReal.ofReal (retainedWidthDensity β t))
    (hK : ∀ᵐ t ∂directionalSchwingerMeasure (Fin n), K t ≤ uK * retainedPhysicalMomentModel h t C J)
    (faces : ∀ S : Finset (Fin n), S.Nonempty → retainedFaceAdmissible β h
      (retainedWidthDefect (Matrix.fromRows C J))
      (retainedWidthMissingScore (Matrix.fromRows C J)) S) :
    (∫⁻ t, ρ t * K t ∂directionalSchwingerMeasure (Fin n)) < ⊤ := by
  let a : ℝ := ((2 * Real.pi) ^ (2 * (Fintype.card ι + Fintype.card κ)))⁻¹
  refine retainedCoefficient_finite_of_upper (Matrix.fromRows C J) (by simpa only [Fintype.card_sum])
    β hh _ (uρ * uK * ENNReal.ofReal a)
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top huρ huK) ENNReal.ofReal_ne_top) ?_ faces
  filter_upwards [retainedWidth_ae_positive (n := n), hρ, hK] with t ht hr hk
  have he := retainedMoment_widthDensity_eq C J hC hM β t ht h
  rw [mul_assoc (uρ * uK), ← he]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul' hr hk

end UV
