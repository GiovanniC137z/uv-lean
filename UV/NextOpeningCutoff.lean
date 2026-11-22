import UV.NextOpeningDisplacement
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Group.Tannery

/-! The number cutoffs are bounded self-adjoint operators on the original
positive Fock space. On the vacuum, their genuine operator exponentials
converge strongly to the entire analytic-vector series. -/

noncomputable section

namespace UV

open Filter
open scoped Topology Nat ComplexInnerProductSpace ENNReal

private def opening.rank (m n : ℕ) : OpeningFock →L[ℂ] OpeningFock :=
  (innerSL ℂ (openingNumberState n)).smulRight (openingNumberState m)

@[simp] private theorem opening.inner_number (n : ℕ) (v : OpeningFock) :
    inner ℂ (openingNumberState n) v = v n := by
  rw [openingNumberState, lp.inner_single_left]
  simp

@[simp] private theorem opening.rank_apply (m n : ℕ) (v : OpeningFock) :
    opening.rank m n v = v n • openingNumberState m := by
  change inner ℂ (openingNumberState n) v • openingNumberState m = _
  rw [opening.inner_number]

@[simp] private theorem opening.numberState_apply (m n : ℕ) :
    openingNumberState m n = if m = n then 1 else 0 := by
  by_cases h : m = n
  · subst n
    simp [openingNumberState]
  · exact (lp.single_apply_ne (E := fun _ : ℕ => ℂ) 2 m 1 (Ne.symm h)).trans (if_neg h).symm

/-- Edges of the finite section of the actual position Jacobi matrix.
The operator is zero on the orthogonal complement of its number cutoff. -/
def openingJacobiCutoff (c : ℕ) : OpeningFock →L[ℂ] OpeningFock :=
  ∑ i ∈ Finset.range c, (Real.sqrt ((i + 1 : ℕ) : ℝ) : ℂ) •
    (opening.rank i (i + 1) + opening.rank (i + 1) i)

theorem openingJacobiCutoff_selfAdjoint (c : ℕ) :
    IsSelfAdjoint (openingJacobiCutoff c) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro v w
  simp only [ContinuousLinearMap.coe_coe, openingJacobiCutoff, ContinuousLinearMap.sum_apply,
    inner_sum, sum_inner, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    opening.rank_apply, inner_smul_right, inner_smul_left, inner_add_right, inner_add_left,
    Complex.conj_ofReal, opening.inner_number]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [← inner_conj_symm v (openingNumberState _)]
  simp only [opening.inner_number]
  ring

private theorem opening.cutoff_coeff (c n : ℕ) (v : OpeningFock) :
    openingJacobiCutoff c v n =
      (if n < c then (Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ) * v (n + 1) else 0) +
        (if 0 < n ∧ n ≤ c then (Real.sqrt (n : ℝ) : ℂ) * v (n - 1) else 0) := by
  simp only [openingJacobiCutoff, ContinuousLinearMap.sum_apply,
    lp.coeFn_sum, Finset.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, opening.rank_apply, lp.coeFn_smul, lp.coeFn_add,
    Pi.smul_apply, Pi.add_apply, smul_eq_mul, opening.numberState_apply]
  simp_rw [mul_add, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_add_distrib]
  cases n with
  | zero =>
    simp [Finset.sum_ite_eq', Finset.mem_range]
  | succ n =>
    simp only [Nat.add_left_inj, Finset.sum_ite_eq', Finset.mem_range,
      Nat.add_sub_cancel, Nat.zero_lt_succ, true_and, Nat.add_one_le_iff]

theorem openingJacobiCutoff_apply_of_supported (c : ℕ) (v : OpeningFock)
    (hv : ∀ n > c, v n = 0) (n : ℕ) :
    openingJacobiCutoff c v n = if n ≤ c then openingJacobi v n else 0 := by
  rw [opening.cutoff_coeff]
  by_cases h : n ≤ c
  · rw [if_pos h, openingJacobi]
    have hupper :
        (if n < c then (Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ) * v (n + 1) else 0) =
          (Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ) * v (n + 1) := by
      by_cases hh : n < c
      · rw [if_pos hh]
      · rw [if_neg hh, hv _ (by omega), mul_zero]
    rw [hupper]
    by_cases hn : 0 < n
    · rw [if_pos ⟨hn, h⟩]
    · have h0 : n = 0 := by omega
      simp [h0]
  · rw [if_neg h, if_neg (by omega), if_neg (by simp [h]), add_zero]

def openingCutoffPower (c k : ℕ) : OpeningFock :=
  (openingJacobiCutoff c ^ k) (openingNumberState 0)

@[simp] private theorem opening.cutoffPower_zero (c : ℕ) :
    openingCutoffPower c 0 = openingNumberState 0 := by
  simp [openingCutoffPower]

private theorem opening.cutoffPower_succ (c k : ℕ) :
    openingCutoffPower c (k + 1) = openingJacobiCutoff c (openingCutoffPower c k) := by
  rw [openingCutoffPower, pow_succ', ContinuousLinearMap.mul_apply]
  rfl

private theorem opening.cutoffPower_support (c k : ℕ) :
    (∀ n > c, openingCutoffPower c k n = 0) ∧
    (∀ n > k, openingCutoffPower c k n = 0) := by
  induction k with
  | zero =>
    rw [opening.cutoffPower_zero]
    constructor <;> intro n hn <;> simp [show 0 ≠ n by omega]
  | succ k ih =>
    rw [opening.cutoffPower_succ]
    constructor
    · intro n hn
      rw [openingJacobiCutoff_apply_of_supported _ _ ih.1, if_neg (by omega)]
    · intro n hn
      simp [openingJacobiCutoff_apply_of_supported _ _ ih.1, openingJacobi_support ih.2 n hn]

/-- A power that cannot have left the cutoff agrees with the true
position power in the original, common number coordinates. -/
theorem openingCutoffPower_eq (c k : ℕ) (h : k ≤ c) :
    openingCutoffPower c k = openingVacuumPower k := by
  induction k with
  | zero => simp
  | succ k ih =>
    ext n
    rw [opening.cutoffPower_succ,
      openingJacobiCutoff_apply_of_supported _ _ (opening.cutoffPower_support c k).1,
      ih (by omega)]
    by_cases hn : n ≤ c
    · rw [if_pos hn]
      rfl
    · rw [if_neg hn]
      exact (openingVacuumPowerSeq_support _ n (by omega)).symm

private theorem opening.cutoffPower_norm_sq_bound (c k : ℕ) :
    ‖openingCutoffPower c k‖ ^ 2 ≤ 4 ^ k * (k ! : ℝ) := by
  induction k with
  | zero => simp [openingNumberState, lp.norm_single]
  | succ k ih =>
    have h := opening.cutoffPower_support c k
    rw [opening.cutoffPower_succ]
    calc
      _ ≤ 4 * (k + 1 : ℝ) * ‖openingCutoffPower c k‖ ^ 2 :=
        openingJacobi_truncated_norm_sq_le _ _ h.2 (openingJacobiCutoff_apply_of_supported _ _ h.1)
      _ ≤ 4 * (k + 1 : ℝ) * (4 ^ k * (k ! : ℝ)) := by gcongr
      _ = _ := by rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]; ring

private theorem opening.cutoffPower_norm_bound (c k : ℕ) :
    ‖openingCutoffPower c k‖ ≤ 2 ^ k * Real.sqrt (k ! : ℝ) := by
  have h := opening.cutoffPower_norm_sq_bound c k
  have hs : (2 ^ k * Real.sqrt (k ! : ℝ)) ^ 2 = 4 ^ k * (k ! : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), ← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 (hs ▸ h)

def openingCutoffExp (c : ℕ) (z : ℂ) : OpeningFock →L[ℂ] OpeningFock :=
  NormedSpace.exp ℂ (z • openingJacobiCutoff c)

theorem openingCutoffExp_on_cut_unitary (c : ℕ) (u : ℝ) :
    openingCutoffExp c ((u : ℂ) * Complex.I) ∈ unitary (OpeningFock →L[ℂ] OpeningFock) := by
  have h : star ((u : ℂ) * Complex.I) = -((u : ℂ) * Complex.I) := by
    simp
  exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint ℂ
    ((openingJacobiCutoff_selfAdjoint c).smul_mem_skewAdjoint h)

private theorem opening.cutoffExp_apply (c : ℕ) (z : ℂ) :
    openingCutoffExp c z (openingNumberState 0) =
      ∑' k : ℕ, (z ^ k / (k ! : ℂ)) • openingCutoffPower c k := by
  let ev : (OpeningFock →L[ℂ] OpeningFock) →L[ℂ] OpeningFock :=
    ContinuousLinearMap.apply ℂ OpeningFock (openingNumberState 0)
  have hs := ev.hasSum (NormedSpace.expSeries_summable' (𝕂 := ℂ) (z • openingJacobiCutoff c)).hasSum
  change _ = ∑' k : ℕ, _
  rw [openingCutoffExp, NormedSpace.exp_eq_tsum]
  calc
    _ = ∑' k : ℕ, ev ((k !⁻¹ : ℂ) • (z • openingJacobiCutoff c) ^ k) := hs.tsum_eq.symm
    _ = _ := tsum_congr fun k => by
      have he : (z • openingJacobiCutoff c) ^ k = z ^ k • openingJacobiCutoff c ^ k := by
        have hcomm : Commute (algebraMap ℂ (OpeningFock →L[ℂ] OpeningFock) z)
            (openingJacobiCutoff c) := Algebra.commutes _ _
        rw [Algebra.smul_def z, hcomm.mul_pow,
          ← map_pow, ← Algebra.smul_def]
      rw [he, smul_smul, div_eq_mul_inv, mul_comm (k !⁻¹ : ℂ), map_smul]
      rfl

/-- The exponentials of the self-adjoint number cutoffs converge
on the vacuum in the norm of the full positive Fock space. -/
theorem openingCutoffExp_tendsto_vacuum (z : ℂ) :
    Tendsto (fun c : ℕ => openingCutoffExp c z (openingNumberState 0)) atTop
      (𝓝 (openingVacuumTaylor z)) := by
  simp_rw [opening.cutoffExp_apply]
  refine tendsto_tsum_of_dominated_convergence (openingVacuumTaylorMajorant_summable z) ?_ ?_
  · intro k
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop k] with c hc
    rw [openingCutoffPower_eq c k hc]
  · exact Eventually.of_forall fun c k =>
      openingVacuumTaylorMajorant_bound z k _ (opening.cutoffPower_norm_bound c k)

/-- At the physical on-cut displacement the strong cutoff vacuum
limit is the unit coherent vector with its exact phase. -/
theorem openingCutoffExp_tendsto_on_cut (u : ℝ) :
    Tendsto (fun c : ℕ => openingCutoffExp c ((u : ℂ) * Complex.I) (openingNumberState 0)) atTop
      (𝓝 (openingCoherentVector ((u : ℂ) * Complex.I))) := by
  rw [← openingVacuumTaylor_on_cut]
  exact openingCutoffExp_tendsto_vacuum _

end UV
