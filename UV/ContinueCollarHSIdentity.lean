import UV.ResumeCollarHeat
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space

/-! A Hilbert basis calculation on the complex radial L² space
identifies the weighted heat operator's squared Hilbert–Schmidt
sum with its positive diagonal readout. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ComplexInnerProductSpace

namespace UV.ContinueCollarHSIdentity

abbrev radialMeasure : Measure ℝ := (volume : Measure ℝ).restrict (Ioc 0 1)
abbrev RadialL2 := Lp ℂ 2 radialMeasure

theorem radial_measure_eq_open :
    radialMeasure = (volume : Measure ℝ).restrict (Ioo 0 1) :=
  (Measure.restrict_congr_set Ioo_ae_eq_Ioc).symm

/-- The scalar multiplier acts in the same radial coordinate as both
the determinant and the retained bridge. -/
def weightedCollarMultiplier (F : ℝ → ℝ) (t r : ℝ) : ℂ :=
  (Real.sqrt (F r) * Real.exp (-(r ^ (2 : ℕ)) / (2 * t)) : ℝ)

/-- Squared Hilbert–Schmidt sum in a countable Hilbert basis, allowing
the value infinity before the heat comparison is used. -/
def collarHSSq {ι : Type*} (b : HilbertBasis ι ℂ RadialL2)
    (A : RadialL2 →L[ℂ] RadialL2) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (‖A (b i)‖ ^ (2 : ℕ))

private theorem radial_l2_norm_sq_integral (v : RadialL2) :
    ‖v‖ ^ (2 : ℕ) = ∫ r, ‖v r‖ ^ (2 : ℕ) ∂radialMeasure := by
  have hi := L2.integrable_inner (𝕜 := ℂ) v v
  have he := congrArg RCLike.re (L2.inner_def (𝕜 := ℂ) v v)
  rw [← integral_re hi] at he
  simpa only [← norm_sq_eq_re_inner] using he

private theorem radial_l2_norm_sq_lintegral (v : RadialL2) :
    ENNReal.ofReal (‖v‖ ^ (2 : ℕ)) =
      ∫⁻ r, ENNReal.ofReal (‖v r‖ ^ (2 : ℕ)) ∂radialMeasure := by
  rw [radial_l2_norm_sq_integral]
  apply ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v))
  exact Eventually.of_forall fun _ => sq_nonneg _

private theorem radial_hilbert_basis_parseval {ι : Type*} (b : HilbertBasis ι ℂ RadialL2)
    (v : RadialL2) :
    (∑' i, ENNReal.ofReal (‖inner ℂ v (b i)‖ ^ (2 : ℕ))) = ENNReal.ofReal (‖v‖ ^ (2 : ℕ)) := by
  have h2 : 0 < (2 : ℝ≥0∞).toReal := by simp
  have hs₀ := lp.hasSum_norm h2 (b.repr v)
  have he : ∀ i, ‖inner ℂ v (b i)‖ = ‖b.repr v i‖ := by
    intro i
    rw [b.repr_apply_apply, norm_inner_symm]
  simp_rw [he]
  have hs : HasSum (fun i => ‖b.repr v i‖ ^ (2 : ℕ)) (‖v‖ ^ (2 : ℕ)) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map] using hs₀
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs.summable, hs.tsum_eq]

theorem weighted_collar_multiplier_norm_sq {F : ℝ → ℝ} {t r : ℝ} (hF : 0 ≤ F r) :
    ‖weightedCollarMultiplier F t r‖ ^ (2 : ℕ) =
      F r * Real.exp (-(r ^ (2 : ℕ)) / t) := by
  unfold weightedCollarMultiplier
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow, Real.sq_sqrt hF,
    ← Real.exp_nat_mul]
  congr 2
  push_cast
  by_cases ht : t = 0
  · simp [ht]
  · field_simp

/-- Parseval applies to the actual kernel row in the same radial
coordinate as the multiplier. The basis vectors are kept in L². -/
theorem weighted_collar_hs_sq_diagonal {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ RadialL2) {A : RadialL2 →L[ℂ] RadialL2}
    {rows : ℝ → RadialL2} {D F : ℝ → ℝ} {t : ℝ}
    (hF : ∀ᵐ r ∂radialMeasure, 0 ≤ F r)
    (hDiag : ∀ᵐ r ∂radialMeasure, ‖rows r‖ ^ (2 : ℕ) = D r)
    (hRows : ∀ i, ∀ᵐ r ∂radialMeasure,
      A (b i) r = weightedCollarMultiplier F t r * inner ℂ (rows r) (b i)) :
    collarHSSq b A =
      ∫⁻ r, ENNReal.ofReal (F r * Real.exp (-(r ^ (2 : ℕ)) / t) * D r) ∂radialMeasure := by
  unfold collarHSSq
  simp_rw [radial_l2_norm_sq_lintegral]
  rw [← lintegral_tsum (fun i =>
    ((Lp.aestronglyMeasurable (A (b i))).norm.aemeasurable.pow_const 2).ennreal_ofReal)]
  apply lintegral_congr_ae
  have hEvery : ∀ᵐ r ∂radialMeasure, ∀ i, _ := ae_all_iff.mpr hRows
  filter_upwards [hEvery, hF, hDiag] with r hr hFr hd
  simp_rw [hr, norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg ‖weightedCollarMultiplier F t r‖)]
  rw [ENNReal.tsum_mul_left, radial_hilbert_basis_parseval, weighted_collar_multiplier_norm_sq hFr, hd,
    ← ENNReal.ofReal_mul (mul_nonneg hFr (Real.exp_nonneg _))]

/-- For a real symmetric heat kernel, the diagonal semigroup
identity gives the squared norm of the actual kernel row. -/
theorem collar_kernel_row_norm_sq {row : RadialL2} {K : ℝ → ℝ → ℝ} {r D : ℝ}
    (hrow : ∀ᵐ y ∂radialMeasure, row y = (K r y : ℂ))
    (hsym : ∀ᵐ y ∂radialMeasure, K y r = K r y)
    (hsemi : (∫ y, K r y * K y r ∂radialMeasure) = D) :
    ‖row‖ ^ (2 : ℕ) = D := by
  rw [radial_l2_norm_sq_integral, ← hsemi]
  apply integral_congr_ae
  filter_upwards [hrow, hsym] with y hy hsy
  rw [hy, hsy, Complex.norm_real, Real.norm_eq_abs, sq_abs, pow_two]

/-- For a represented real symmetric heat kernel, the same-source
weighted operator's squared Hilbert–Schmidt sum equals the diagonal
integral with the exact retained Gaussian bridge factor. -/
theorem weighted_collar_hs_sq_from_semigroup {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ RadialL2) {A : RadialL2 →L[ℂ] RadialL2}
    {rows : ℝ → RadialL2} {K : ℝ → ℝ → ℝ} {D F : ℝ → ℝ} {t : ℝ}
    (hF : ∀ᵐ r ∂radialMeasure, 0 ≤ F r)
    (hKernelRows : ∀ᵐ r ∂radialMeasure, ∀ᵐ y ∂radialMeasure, rows r y = (K r y : ℂ))
    (hSymmetric : ∀ᵐ r ∂radialMeasure, ∀ᵐ y ∂radialMeasure, K y r = K r y)
    (hDiagonal : ∀ᵐ r ∂radialMeasure, (∫ y, K r y * K y r ∂radialMeasure) = D r)
    (hRows : ∀ i, ∀ᵐ r ∂radialMeasure,
      A (b i) r = weightedCollarMultiplier F t r * inner ℂ (rows r) (b i)) :
    collarHSSq b A =
      ∫⁻ r, ENNReal.ofReal (F r * Real.exp (-(r ^ (2 : ℕ)) / t) * D r) ∂radialMeasure := by
  apply weighted_collar_hs_sq_diagonal b hF _ hRows
  filter_upwards [hKernelRows, hSymmetric, hDiagonal] with r hr hsym hd
  exact collar_kernel_row_norm_sq hr hsym hd

end UV.ContinueCollarHSIdentity
