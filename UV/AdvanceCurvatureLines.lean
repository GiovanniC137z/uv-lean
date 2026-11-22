import UV.ContinueCurvatureModes

/-! The local signed-mode contraction at the literal spherical cutoff.
Both endpoints receive the normal transfer and the normalized real sine
and cosine in each opposite pair contribute one equal mode weight. -/

noncomputable section

open MeasureTheory Real Filter
open scoped BigOperators ComplexConjugate Topology

namespace UV.AdvanceCurvatureLines

open UV.ExtendCurvaturePotential UV.NextCurvatureLaw UV.FurtherCurvatureShell
open UV.NextCurvatureFourierSummability UV.ContinueCurvatureModes UV.FurtherCurvatureLine
open UV.RevisionCurvatureDeterminant (latticeFrequency)

def oppositeMode (k : MeanZeroMode) : MeanZeroMode := ⟨-k.1, neg_ne_zero.mpr k.2⟩

@[simp] theorem oppositeMode_oppositeMode (k : MeanZeroMode) :
    oppositeMode (oppositeMode k) = k := Subtype.ext (neg_neg _)

theorem opposite_firstActive (k : MeanZeroMode) :
    firstActive (oppositeMode k) = firstActive k := by
  unfold firstActive
  have hf : (Finset.univ.filter (fun j : Fin 4 => (oppositeMode k).1 j ≠ 0)) =
      Finset.univ.filter (fun j : Fin 4 => k.1 j ≠ 0) := by
    ext j
    simp [oppositeMode]
  congr 1

theorem firstActive_value_ne_zero (k : MeanZeroMode) : k.1 (firstActive k) ≠ 0 := by
  have hm : firstActive k ∈ Finset.univ.filter (fun j : Fin 4 => k.1 j ≠ 0) :=
    Finset.min'_mem _ _
  exact (Finset.mem_filter.mp hm).2

private theorem latticeFrequency_opposite (k : MeanZeroMode) :
    latticeFrequency (oppositeMode k) = latticeFrequency k := by
  simp [oppositeMode, latticeFrequency]

private theorem curvatureLine_opposite (ℓ : ℝ) (k : MeanZeroMode) :
    curvatureLine ℓ (oppositeMode k) = curvatureLine ℓ k := by
  simp only [curvatureLine, curvatureCovariance, latticeFrequency_opposite]

/-- Each signed sine/cosine pair has constant squared sum exactly two on
normalized Haar volume. -/
theorem signedMode_sq_pair (k : MeanZeroMode) (x : Torus) :
    realTorusMode k x ^ 2 + realTorusMode (oppositeMode k) x ^ 2 = 2 := by
  have hχ := torusCharacter_point_norm k.1 x
  have hSq : (torusCharacter k.1 x).re ^ 2 + (torusCharacter k.1 x).im ^ 2 = 1 := by
    rw [pow_two, pow_two, ← Complex.normSq_apply, ← Complex.sq_norm, hχ]
    norm_num
  have hs : (sqrt 2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num)
  unfold realTorusMode
  rw [opposite_firstActive]
  change
    ((if 0 < k.1 (firstActive k) then
        sqrt 2 • (⟨Complex.re, Complex.continuous_re⟩ : C(ℂ, ℝ)).comp (torusCharacter k.1)
      else sqrt 2 • (⟨Complex.im, Complex.continuous_im⟩ : C(ℂ, ℝ)).comp (torusCharacter (-k.1))) x)^2 +
    ((if 0 < -k.1 (firstActive k) then
        sqrt 2 • (⟨Complex.re, Complex.continuous_re⟩ : C(ℂ, ℝ)).comp (torusCharacter (-k.1))
      else sqrt 2 • (⟨Complex.im, Complex.continuous_im⟩ : C(ℂ, ℝ)).comp (torusCharacter (-(-k.1)))) x)^2 = _
  rcases lt_or_gt_of_ne (firstActive_value_ne_zero k) with h | h
  · simp only [if_neg (not_lt_of_ge h.le), if_pos (neg_pos.mpr h), ContinuousMap.smul_apply,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk, smul_eq_mul, mul_pow, hs]
    have hh := torusCharacter_point_norm (-k.1) x
    have hSq' : (torusCharacter (-k.1) x).re ^ 2 + (torusCharacter (-k.1) x).im ^ 2 = 1 := by
      rw [pow_two, pow_two, ← Complex.normSq_apply, ← Complex.sq_norm, hh]
      norm_num
    linarith
  · simp only [if_pos h, if_neg (not_lt_of_ge (neg_nonpos.mpr h.le)), ContinuousMap.smul_apply,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk, smul_eq_mul, neg_neg, mul_pow, hs]
    linarith

/-- Product of the two transfers and the exact variance of the common
preparation gives the contraction in the manuscript. -/
theorem transferWeight_sq_half (ℓ : ℝ) (k : MeanZeroMode) :
    (derivativeWeight 0 ℓ k)^2 / 2 = curvatureLine ℓ k := by
  unfold derivativeWeight curvatureLine
  have hv : 0 ≤ 2 * curvatureCovariance ℓ k := by
    unfold curvatureCovariance
    positivity
  rw [pow_zero, one_mul, mul_pow, Real.sq_sqrt hv, ← Real.exp_nat_mul]
  push_cast
  rw [show (2 : ℝ) * (-ℓ * latticeFrequency k) = -2 * ℓ * latticeFrequency k by ring]
  ring

/-- The covariance at a single torus point is independent of that point
at each symmetric spherical cutoff. -/
theorem localized_spherical_line_sum (Λ ℓ : ℝ) (x : Torus) :
    (∑ k ∈ retainedModes Λ, curvatureLine ℓ k * realTorusMode k x ^ 2) =
      ∑ k ∈ retainedModes Λ, curvatureLine ℓ k := by
  classical
  have hsub : ∀ k : MeanZeroMode,
      k ∈ retainedModes Λ ↔ oppositeMode k ∈ retainedModes Λ := by
    intro k
    rw [mem_retainedModes, mem_retainedModes, latticeFrequency_opposite]
  let f (k : MeanZeroMode) := curvatureLine ℓ k * realTorusMode k x ^ 2
  have hinv : (∑ k ∈ retainedModes Λ, f k) = ∑ k ∈ retainedModes Λ, f (oppositeMode k) := by
    exact (Finset.sum_bijective oppositeMode
      (Function.Involutive.bijective oppositeMode_oppositeMode) hsub
      (fun _ _ => rfl)).symm
  change (∑ k ∈ retainedModes Λ, f k) = _
  have hsum : (∑ k ∈ retainedModes Λ, f k) +
      (∑ k ∈ retainedModes Λ, f (oppositeMode k)) = 2 * ∑ k ∈ retainedModes Λ, curvatureLine ℓ k := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold f
    rw [curvatureLine_opposite, ← mul_add, signedMode_sq_pair, mul_comm]
  linarith

theorem retainedModes_tendsto : Tendsto retainedModes atTop atTop := by
  refine tendsto_atTop.mpr fun s => eventually_atTop.mpr ⟨∑ k ∈ s, latticeFrequency k, ?_⟩
  intro Λ hΛ k hk
  exact (mem_retainedModes Λ k).2 ((Finset.single_le_sum
    (f := fun k => latticeFrequency (k : MeanZeroMode)) (fun _ _ => sqrt_nonneg _) hk).trans hΛ)

theorem summable_positive_depth_line {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Summable (fun k : MeanZeroMode => curvatureLine ℓ k) := by
  obtain ⟨_,_,h⟩ := full_weighted_line_bound (s := 0) le_rfl
  simpa only [Function.comp_def, weightedLine, Real.rpow_zero, one_mul] using
    (h hℓ).1.comp_injective Subtype.val_injective

theorem spherical_line_sum_limit {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Tendsto (fun Λ : ℝ => ∑ k ∈ retainedModes Λ, curvatureLine ℓ k) atTop
      (𝓝 (∑' k : MeanZeroMode, curvatureLine ℓ k)) :=
  (summable_positive_depth_line hℓ).hasSum.comp retainedModes_tendsto

end UV.AdvanceCurvatureLines
