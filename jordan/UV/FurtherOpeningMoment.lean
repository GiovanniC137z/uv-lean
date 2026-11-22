import UV.FurtherOpeningCLT

/-! The unbounded half-power moment under the critical Poisson limit.
A second moment bound controls the error of bounded continuous truncations. -/

noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal Nat ProbabilityTheory

namespace UV

private def criticalPoissonWeight (r : ℝ≥0) (n : ℕ) : ℝ :=
  Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n !

private theorem criticalPoissonWeight_pos (r : ℝ≥0) (n : ℕ) : 0 ≤ criticalPoissonWeight r n := by
  dsimp [criticalPoissonWeight]
  positivity

private theorem criticalPoissonWeight_succ (r : ℝ≥0) (n : ℕ) :
    criticalPoissonWeight r (n + 1) * ((n : ℝ) + 1) = (r : ℝ) * criticalPoissonWeight r n := by
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  unfold criticalPoissonWeight
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

private theorem criticalPoisson_hasSum_one (r : ℝ≥0) : HasSum (criticalPoissonWeight r) 1 :=
  hasSum_one_poissonMeasure r

private theorem criticalPoisson_hasSum_first (r : ℝ≥0) :
    HasSum (fun n : ℕ ↦ criticalPoissonWeight r n * (n : ℝ)) (r : ℝ) := by
  have h := (criticalPoisson_hasSum_one r).mul_left (r : ℝ)
  rw [mul_one] at h
  apply (hasSum_nat_add_iff' 1).mp
  simpa only [Finset.sum_range_one, Nat.cast_zero, Nat.cast_add, Nat.cast_one, mul_zero,
    sub_zero, criticalPoissonWeight_succ] using h

private theorem criticalPoisson_hasSum_second (r : ℝ≥0) :
    HasSum (fun n : ℕ ↦ criticalPoissonWeight r n * (n : ℝ) ^ 2) ((r : ℝ) * (r + 1)) := by
  have he : (fun n : ℕ ↦ criticalPoissonWeight r (n + 1) * ((n + 1 : ℕ) : ℝ) ^ 2) =
      fun n : ℕ ↦ (r : ℝ) * (criticalPoissonWeight r n * n + criticalPoissonWeight r n) := by
    funext n
    push_cast
    calc
      _ = (criticalPoissonWeight r (n + 1) * (n + 1 : ℝ)) * (n + 1) := by ring
      _ = _ := by rw [criticalPoissonWeight_succ]; ring
  have hs : HasSum (fun n : ℕ ↦ criticalPoissonWeight r (n + 1) * ((n + 1 : ℕ) : ℝ) ^ 2)
      ((r : ℝ) * (r + 1)) := by
    rw [he]
    exact ((criticalPoisson_hasSum_first r).add (criticalPoisson_hasSum_one r)).mul_left (r : ℝ)
  apply (hasSum_nat_add_iff' 1).mp
  simpa only [Finset.sum_range_one, Nat.cast_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, sub_zero] using hs

private theorem criticalPoisson_hasSum_variance (r : ℝ≥0) :
    HasSum (fun n : ℕ ↦ criticalPoissonWeight r n * ((n : ℝ) - r) ^ 2) (r : ℝ) := by
  have h := ((criticalPoisson_hasSum_second r).sub
    ((criticalPoisson_hasSum_first r).mul_left (2 * r : ℝ))).add
    ((criticalPoisson_hasSum_one r).mul_left ((r : ℝ) ^ 2))
  have he : (fun n : ℕ ↦ criticalPoissonWeight r n * ((n : ℝ) - r) ^ 2) =
      fun n : ℕ ↦ criticalPoissonWeight r n * n ^ 2 -
        (2 * r : ℝ) * (criticalPoissonWeight r n * n) + (r : ℝ) ^ 2 * criticalPoissonWeight r n := by
    funext n
    ring
  have hval : (r : ℝ) * (r + 1) - (2 * (r : ℝ)) * r + (r : ℝ) ^ 2 * 1 = (r : ℝ) := by ring
  rw [hval] at h
  rw [he]
  exact h

lemma openingCriticalMeasure_eq_map (M : ℝ) : (openingCriticalMeasure M : Measure ℝ) =
    (poissonMeasure M.toNNReal).map (fun n : ℕ ↦ ((n : ℝ) - M) / Real.sqrt M) := by
  change ((poissonMeasure M.toNNReal).map (Nat.cast : ℕ → ℝ)).map
      (fun x : ℝ ↦ (x - M) / Real.sqrt M) = _
  rw [Measure.map_map (by fun_prop) Measurable.of_discrete]
  rfl

/-- The normalized fluctuation has exactly unit second moment for every
positive real Poisson rate. -/
theorem openingCriticalMeasure_second_moment {M : ℝ} (hM : 0 < M) :
    Integrable (fun x : ℝ ↦ x ^ 2) (openingCriticalMeasure M : Measure ℝ) ∧
      (∫ x : ℝ, x ^ 2 ∂(openingCriticalMeasure M : Measure ℝ)) = 1 := by
  let r := M.toNNReal
  have h := (criticalPoisson_hasSum_variance r).div_const M
  rw [Real.coe_toNNReal M hM.le, div_self hM.ne'] at h
  have hs : HasSum (fun n : ℕ ↦ criticalPoissonWeight r n * (((n : ℝ) - M) / Real.sqrt M) ^ 2) 1 := by
    simpa only [div_pow, Real.sq_sqrt hM.le, mul_div_assoc] using h
  rw [openingCriticalMeasure_eq_map]
  constructor
  · apply (integrable_map_measure (by fun_prop) AEMeasurable.of_discrete).mpr
    apply integrable_poissonMeasure_iff.mpr
    change Summable (fun n : ℕ ↦ criticalPoissonWeight r n * ‖(((n : ℝ) - M) / Real.sqrt M) ^ 2‖)
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hs.summable
  · rw [integral_map AEMeasurable.of_discrete (by fun_prop), integral_poissonMeasure]
    simpa only [criticalPoissonWeight, smul_eq_mul] using hs.tsum_eq

theorem openingGaussianMeasure_second_moment :
    Integrable (fun x : ℝ ↦ x ^ 2) (openingGaussianMeasure : Measure ℝ) ∧
      (∫ x : ℝ, x ^ 2 ∂(openingGaussianMeasure : Measure ℝ)) = 1 := by
  change Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) ∧ _
  refine ⟨(memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq, ?_⟩
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (by fun_prop), integral_id_gaussianReal, NNReal.coe_one] at h
  change (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1
  simpa only [sub_zero] using h

def openingHalfMoment (x : ℝ) : ℝ := Real.sqrt (max (-x) 0)

lemma openingHalfMoment_nonneg (x : ℝ) : 0 ≤ openingHalfMoment x := Real.sqrt_nonneg _

lemma openingHalfMoment_fourth_le (x : ℝ) : openingHalfMoment x ^ 4 ≤ x ^ 2 := by
  rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, openingHalfMoment, Real.sq_sqrt (le_max_right _ _)]
  by_cases h : x ≤ 0
  · rw [max_eq_left (neg_nonneg.mpr h), neg_sq]
  · rw [max_eq_right (by linarith), zero_pow (by decide : (2 : ℕ) ≠ 0)]
    positivity

lemma openingHalfMoment_le (x : ℝ) : openingHalfMoment x ≤ 1 + x ^ 2 := by
  by_cases h : openingHalfMoment x ≤ 1
  · linarith [sq_nonneg x]
  · have hpow : openingHalfMoment x ≤ openingHalfMoment x ^ 4 := by
      simpa only [pow_one] using pow_le_pow_right₀ (le_of_not_ge h) (by decide : (1 : ℕ) ≤ 4)
    linarith [hpow.trans (openingHalfMoment_fourth_le x), sq_nonneg x]

lemma openingHalfMoment_continuous : Continuous openingHalfMoment := by
  unfold openingHalfMoment
  fun_prop

private def openingHalfMomentClip (K : ℝ) (hK : 0 ≤ K) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x ↦ min (openingHalfMoment x) K, openingHalfMoment_continuous.min continuous_const⟩
    K (fun x y ↦ by
      rw [Real.dist_eq]
      change |min (openingHalfMoment x) K - min (openingHalfMoment y) K| ≤ K
      apply abs_le.mpr
      constructor
      · linarith [min_le_right (openingHalfMoment y) K, le_min (openingHalfMoment_nonneg x) hK]
      · linarith [min_le_right (openingHalfMoment x) K, le_min (openingHalfMoment_nonneg y) hK])

lemma openingHalfMoment_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : Integrable (fun x : ℝ ↦ x ^ 2) μ) : Integrable openingHalfMoment μ := by
  apply ((integrable_const (1 : ℝ)).add h).mono' openingHalfMoment_continuous.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_of_nonneg (openingHalfMoment_nonneg x)]
  exact openingHalfMoment_le x

private theorem openingHalfMoment_clip_error {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : Integrable (fun x : ℝ ↦ x ^ 2) μ) (hm : (∫ x : ℝ, x ^ 2 ∂μ) = 1)
    {K : ℝ} (hK : 0 < K) :
    dist (∫ x, openingHalfMoment x ∂μ) (∫ x, openingHalfMomentClip K hK.le x ∂μ) ≤ 1 / K ^ 3 := by
  have hI := openingHalfMoment_integrable h
  have hB := (openingHalfMomentClip K hK.le).integrable μ
  have hM (x : ℝ) : 0 ≤ openingHalfMoment x - openingHalfMomentClip K hK.le x ∧
      openingHalfMoment x - openingHalfMomentClip K hK.le x ≤ x ^ 2 / K ^ 3 := by
    change 0 ≤ openingHalfMoment x - min (openingHalfMoment x) K ∧
      openingHalfMoment x - min (openingHalfMoment x) K ≤ x ^ 2 / K ^ 3
    constructor
    · exact sub_nonneg.mpr (min_le_left _ _)
    · by_cases hx : openingHalfMoment x ≤ K
      · rw [min_eq_left hx, sub_self]
        positivity
      · have hp : K ^ 3 ≤ openingHalfMoment x ^ 3 := pow_le_pow_left₀ hK.le (le_of_not_ge hx) _
        have hprod := mul_le_mul_of_nonneg_left hp (openingHalfMoment_nonneg x)
        have hu : openingHalfMoment x ≤ x ^ 2 / K ^ 3 := by
          apply (le_div_iff₀ (pow_pos hK 3)).mpr
          calc
            _ ≤ openingHalfMoment x * openingHalfMoment x ^ 3 := hprod
            _ = openingHalfMoment x ^ 4 := by ring
            _ ≤ _ := openingHalfMoment_fourth_le x
        rw [min_eq_right (le_of_not_ge hx)]
        linarith
  rw [Real.dist_eq, ← integral_sub hI hB, abs_of_nonneg (integral_nonneg fun x ↦ (hM x).1)]
  calc
    _ ≤ ∫ x : ℝ, x ^ 2 / K ^ 3 ∂μ := integral_mono (hI.sub hB) (h.div_const _) (fun x ↦ (hM x).2)
    _ = _ := by rw [integral_div, hm]

/-- Weak convergence plus the exact second moments yields convergence of
this unbounded square root of the negative part. -/
theorem openingCriticalHalfMoment_tendsto :
    Tendsto (fun M ↦ ∫ x, openingHalfMoment x ∂(openingCriticalMeasure M : Measure ℝ))
      atTop (𝓝 (∫ x, openingHalfMoment x ∂(openingGaussianMeasure : Measure ℝ))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let K : ℝ := max 1 (4 / ε)
  have hK : 0 < K := zero_lt_one.trans_le (le_max_left _ _)
  have hK0 : 1 ≤ K := le_max_left _ _
  have hK1 : 4 / ε ≤ K := le_max_right _ _
  have hres : 1 / K ^ 3 ≤ ε / 4 := by
    have hK3 : K ≤ K ^ 3 := by
      simpa only [pow_one] using pow_le_pow_right₀ hK0 (by decide : (1 : ℕ) ≤ 3)
    calc
      _ ≤ 1 / K := div_le_div_of_nonneg_left zero_le_one hK hK3
      _ ≤ _ := (div_le_iff₀ hK).mpr (by nlinarith [(div_le_iff₀ hε).mp hK1])
  let g := openingHalfMomentClip K hK.le
  have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    openingCriticalMeasure_tendsto_gaussian) g
  filter_upwards [eventually_gt_atTop (0 : ℝ), Metric.tendsto_nhds.mp ht (ε / 4) (by positivity)]
    with M hM hMt
  have hp := openingCriticalMeasure_second_moment hM
  have hg := openingGaussianMeasure_second_moment
  have h1 := openingHalfMoment_clip_error hp.1 hp.2 hK
  have h2 := openingHalfMoment_clip_error hg.1 hg.2 hK
  let A := ∫ x, openingHalfMoment x ∂(openingCriticalMeasure M : Measure ℝ)
  let B := ∫ x, g x ∂(openingCriticalMeasure M : Measure ℝ)
  let C := ∫ x, g x ∂(openingGaussianMeasure : Measure ℝ)
  let D := ∫ x, openingHalfMoment x ∂(openingGaussianMeasure : Measure ℝ)
  change dist A D < ε
  have hab : dist A B ≤ ε / 4 := h1.trans hres
  have hbc : dist B C < ε / 4 := hMt
  have hcd : dist C D ≤ ε / 4 := by rw [dist_comm]; exact h2.trans hres
  exact (dist_triangle4 A B C D).trans_lt (by linarith)

end UV
