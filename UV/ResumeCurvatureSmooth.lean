import UV.ExtendCurvaturePotential
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! Smoothness of the actual transferred fields on the period-2π cover
of one fixed four-torus. The real sine/cosine selection and Euclidean
frequency are those of the existing Gaussian preparation. -/

noncomputable section

open MeasureTheory Real Filter
open scoped BigOperators Topology ContDiff

namespace UV.ResumeCurvatureSmooth

open UV.NextCurvatureLaw UV.NextCurvatureFourierSummability
open UV.ExtendCurvaturePotential UV.FurtherCurvatureShell
open UV.RevisionCurvatureDeterminant (latticeFrequency)

abbrev Cover := EuclideanSpace ℝ (Fin 4)

def coverPoint (x : Cover) : Torus :=
  fun j => (x j : AddCircle ((2 : ℝ) * π))

def phaseVector (k : TorusMode) : Cover :=
  WithLp.toLp 2 (fun j => (k j : ℝ))

def phaseLinear (k : TorusMode) : Cover →L[ℝ] ℝ :=
  innerSL ℝ (phaseVector k)

theorem phaseLinear_apply (k : TorusMode) (x : Cover) :
    phaseLinear k x = ∑ j, (k j : ℝ) * x j := by
  change @inner ℝ Cover _ (phaseVector k) x = _
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply, star_trivial, phaseVector, WithLp.ofLp_toLp]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

theorem phaseLinear_norm (k : TorusMode) : ‖phaseLinear k‖ = latticeFrequency k := by
  rw [phaseLinear, innerSL_apply_norm, EuclideanSpace.norm_eq, latticeFrequency]
  simp only [phaseVector, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]

private theorem phaseLinear_neg_norm (k : TorusMode) :
    ‖phaseLinear (-k)‖ = latticeFrequency k := by
  rw [phaseLinear_norm, latticeFrequency, latticeFrequency]
  simp only [Pi.neg_apply, Int.cast_neg, neg_sq]

theorem character_cover_eq_exp (k : TorusMode) (x : Cover) :
    torusCharacter k (coverPoint x) = Complex.exp ((phaseLinear k x : ℂ) * Complex.I) := by
  unfold torusCharacter coverPoint
  simp only [ContinuousMap.prod_apply, ContinuousMap.comp_apply]
  rw [phaseLinear_apply, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro j _
  change fourier (T := (2 : ℝ) * π) (k j) (x j : AddCircle ((2 : ℝ)*π)) = _
  rw [fourier_coe_apply]
  congr 1
  have h : (2 : ℂ) * (π : ℂ) ≠ 0 := mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr pi_ne_zero)
  push_cast
  apply (div_eq_iff h).2
  ring

def modeOnCover (k : MeanZeroMode) : Cover → ℝ :=
  if 0 < k.1 (firstActive k) then
    fun x => sqrt 2 • Real.cos (phaseLinear k x)
  else
    fun x => sqrt 2 • Real.sin (phaseLinear (-k.1) x)

theorem realTorusMode_cover_eq (k : MeanZeroMode) (x : Cover) :
    realTorusMode k (coverPoint x) = modeOnCover k x := by
  unfold realTorusMode modeOnCover
  split
  · simp only [ContinuousMap.smul_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      character_cover_eq_exp, Complex.exp_ofReal_mul_I_re]
  · simp only [ContinuousMap.smul_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      character_cover_eq_exp, Complex.exp_ofReal_mul_I_im]

theorem modeOnCover_contDiff (k : MeanZeroMode) (N : WithTop ℕ∞) :
    ContDiff ℝ N (modeOnCover k) := by
  unfold modeOnCover
  split
  · exact (Real.contDiff_cos.comp_continuousLinearMap (g := phaseLinear k)).const_smul _
  · exact (Real.contDiff_sin.comp_continuousLinearMap (g := phaseLinear (-k.1))).const_smul _

private theorem norm_iterated_cos_comp (q : ℕ) (L : Cover →L[ℝ] ℝ) (x : Cover) :
    ‖iteratedFDeriv ℝ q (Real.cos ∘ L) x‖ ≤ ‖L‖^q := by
  rw [L.iteratedFDeriv_comp_right (n := (q : WithTop ℕ∞)) Real.contDiff_cos x le_rfl]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  apply mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact Real.abs_iteratedDeriv_cos_le_one q (L x)

private theorem norm_iterated_sin_comp (q : ℕ) (L : Cover →L[ℝ] ℝ) (x : Cover) :
    ‖iteratedFDeriv ℝ q (Real.sin ∘ L) x‖ ≤ ‖L‖^q := by
  rw [L.iteratedFDeriv_comp_right (n := (q : WithTop ℕ∞)) Real.contDiff_sin x le_rfl]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  apply mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact Real.abs_iteratedDeriv_sin_le_one q (L x)

/-- Each signed real mode has the exact differentiation scale |k|^q
on the Euclidean cover, with its retained sqrt(2) real-mode normalization. -/
theorem mode_derivative_norm_bound (q : ℕ) (k : MeanZeroMode) (x : Cover) :
    ‖iteratedFDeriv ℝ q (modeOnCover k) x‖ ≤ sqrt 2 * latticeFrequency k ^ q := by
  unfold modeOnCover
  split
  · have hf : ContDiffAt ℝ (q : WithTop ℕ∞) (Real.cos ∘ phaseLinear k) x :=
      ((Real.contDiff_cos.comp_continuousLinearMap (g := phaseLinear k)).contDiffAt)
    change ‖iteratedFDeriv ℝ q (fun y => sqrt 2 • (Real.cos ∘ phaseLinear k) y) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' hf, norm_smul,
      Real.norm_of_nonneg (sqrt_nonneg _), ← phaseLinear_norm]
    exact mul_le_mul_of_nonneg_left (norm_iterated_cos_comp q _ _) (sqrt_nonneg _)
  · have hf : ContDiffAt ℝ (q : WithTop ℕ∞) (Real.sin ∘ phaseLinear (-k.1)) x :=
      ((Real.contDiff_sin.comp_continuousLinearMap (g := phaseLinear (-k.1))).contDiffAt)
    change ‖iteratedFDeriv ℝ q (fun y => sqrt 2 • (Real.sin ∘ phaseLinear (-k.1)) y) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' hf, norm_smul,
      Real.norm_of_nonneg (sqrt_nonneg _), ← phaseLinear_neg_norm]
    exact mul_le_mul_of_nonneg_left (norm_iterated_sin_comp q _ _) (sqrt_nonneg _)

def transferredOnCover {n : ℕ} (ℓ : ℝ) (X : ModeSlot n → ℝ)
    (a : Fin 2) (c : Fin n) (k : MeanZeroMode) : Cover → ℝ :=
  fun x => (derivativeWeight 0 ℓ k * X (k,(a,c))) • modeOnCover k x

private theorem transferredOnCover_smooth {n : ℕ} (ℓ : ℝ) (X : ModeSlot n → ℝ)
    (a : Fin 2) (c : Fin n) (k : MeanZeroMode) :
    ContDiff ℝ ∞ (transferredOnCover ℓ X a c k) :=
  (modeOnCover_contDiff k ∞).const_smul _

private def derivativeEnvelope {n : ℕ} (ℓ : ℝ) (X : ModeSlot n → ℝ)
    (a : Fin 2) (c : Fin n) (q : ℕ) (k : MeanZeroMode) : ℝ :=
  sqrt 2 * (derivativeWeight q ℓ k * |X (k,(a,c))|)

private theorem derivativeEnvelope_eq {n : ℕ} (ℓ : ℝ) (X : ModeSlot n → ℝ)
    (a : Fin 2) (c : Fin n) (q : ℕ) (k : MeanZeroMode) :
    derivativeEnvelope ℓ X a c q k =
      (derivativeWeight 0 ℓ k * |X (k,(a,c))|) * (sqrt 2 * (1+latticeFrequency k)^q) := by
  unfold derivativeEnvelope derivativeWeight
  simp only [pow_zero, one_mul]
  ring

private theorem transferredOnCover_derivative_bound {n : ℕ} (ℓ : ℝ) (X : ModeSlot n → ℝ)
    (a : Fin 2) (c : Fin n) (q : ℕ) (k : MeanZeroMode) (x : Cover) :
    ‖iteratedFDeriv ℝ q (transferredOnCover ℓ X a c k) x‖ ≤ derivativeEnvelope ℓ X a c q k := by
  unfold transferredOnCover
  rw [iteratedFDeriv_const_smul_apply'
    (modeOnCover_contDiff k q).contDiffAt, norm_smul,
    norm_mul, Real.norm_of_nonneg (derivativeWeight_nonneg 0 ℓ k), Real.norm_eq_abs,
    derivativeEnvelope_eq]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (derivativeWeight_nonneg 0 ℓ k) (abs_nonneg _))
  refine (mode_derivative_norm_bound q k x).trans ?_
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (sqrt_nonneg _) (le_add_of_nonneg_left zero_le_one) q) (sqrt_nonneg _)

private theorem derivativeEnvelope_summable {n : ℕ} {ℓ : ℝ} {X : ModeSlot n → ℝ}
    (hs : ∀ q : ℕ, Summable fun i : ModeSlot n => derivativeWeight q ℓ i.1 * |X i|)
    (a : Fin 2) (c : Fin n) (q : ℕ) : Summable (derivativeEnvelope ℓ X a c q) := by
  let i : MeanZeroMode → ModeSlot n := fun k => (k, (a,c))
  have hi : Function.Injective i := fun _ _ hh => congrArg (fun j : ModeSlot n => j.1) hh
  simpa only [derivativeEnvelope, Function.comp_def, i] using
    ((hs q).comp_injective hi).mul_left (sqrt 2)

private theorem transferredTerm_norm_le_envelope {n : ℕ} (ℓ : ℝ) (X : ModeSlot n → ℝ)
    (a : Fin 2) (c : Fin n) (k : MeanZeroMode) :
    ‖transferredTerm ℓ X a c k‖ ≤ derivativeEnvelope ℓ X a c 0 k := by
  unfold transferredTerm
  rw [norm_smul, norm_mul, Real.norm_of_nonneg (derivativeWeight_nonneg 0 ℓ k), Real.norm_eq_abs,
      derivativeEnvelope_eq, pow_zero, mul_one]
  exact mul_le_mul_of_nonneg_left (realTorusMode_norm_bound k)
    (mul_nonneg (derivativeWeight_nonneg 0 ℓ k) (abs_nonneg _))

theorem fullTransferred_cover_eq_tsum {n : ℕ} {ℓ : ℝ} {X : ModeSlot n → ℝ}
    (hs : ∀ q : ℕ, Summable fun i : ModeSlot n => derivativeWeight q ℓ i.1 * |X i|)
    (a : Fin 2) (c : Fin n) (x : Cover) :
    fullTransferredField ℓ X a c (coverPoint x) =
      ∑' k, transferredOnCover ℓ X a c k x := by
  have ht : Summable (transferredTerm ℓ X a c) :=
    Summable.of_norm_bounded (derivativeEnvelope_summable hs a c 0)
      (transferredTerm_norm_le_envelope ℓ X a c)
  have h := (ContinuousMap.evalCLM ℝ (coverPoint x)).map_tsum ht
  change (∑' k, transferredTerm ℓ X a c k) (coverPoint x) =
    ∑' k, transferredTerm ℓ X a c k (coverPoint x) at h
  simpa only [fullTransferredField, transferredTerm, transferredOnCover, ContinuousMap.smul_apply,
    realTorusMode_cover_eq] using h

/-- At every positive normal separation, both fields in the common
preparation are smooth in the actual torus coordinates. -/
theorem ae_fullTransferred_smooth {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ᵐ X ∂commonGaussian n, ∀ (a : Fin 2) (c : Fin n),
      ContDiff ℝ ∞ (fun x => fullTransferredField ℓ X a c (coverPoint x)) := by
  filter_upwards [ae_weighted_transfer_summable n hℓ] with X hs
  intro a c
  simp_rw [fullTransferred_cover_eq_tsum hs a c]
  exact contDiff_tsum (transferredOnCover_smooth ℓ X a c)
    (fun q _ => derivativeEnvelope_summable hs a c q)
    (fun q k x _ => transferredOnCover_derivative_bound ℓ X a c q k x)

/-- The derivative of the field is the absolutely convergent series of the
same real signed Fourier modes. -/
theorem ae_fullTransferred_derivatives_eq_tsum {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ᵐ X ∂commonGaussian n, ∀ (a : Fin 2) (c : Fin n) (q : ℕ) (x : Cover),
      iteratedFDeriv ℝ q (fun y => fullTransferredField ℓ X a c (coverPoint y)) x =
        ∑' k, iteratedFDeriv ℝ q (transferredOnCover ℓ X a c k) x := by
  filter_upwards [ae_weighted_transfer_summable n hℓ] with X hs
  intro a c q x
  simp_rw [fullTransferred_cover_eq_tsum hs a c]
  exact iteratedFDeriv_tsum_apply (transferredOnCover_smooth ℓ X a c)
    (fun m _ => derivativeEnvelope_summable hs a c m)
    (fun m k y _ => transferredOnCover_derivative_bound ℓ X a c m k y) (by simp) x

end UV.ResumeCurvatureSmooth
