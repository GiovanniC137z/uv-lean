import UV.ContinueTwoBandFiniteSections

/-! The finite-section determinant limit of a product of two square
summable hopping factors with contractive norm product. The estimates
use both factors and are independent of the cutoff dimension. -/

noncomputable section
open Matrix Filter Set
open scoped Topology Matrix.Norms.L2Operator InnerProductSpace

namespace UV.SectorPlane

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis I ℂ H)

private def schurColumnCost (A B : H →L[ℂ] H) (i : I) : ℝ :=
  ‖A.adjoint (b i)‖ * ‖B (b i)‖

private theorem schur_column_summable (A B : H →L[ℂ] H)
    (hA : Summable (fun i => ‖A.adjoint (b i)‖^2)) (hB : Summable (fun i => ‖B (b i)‖^2)) :
    Summable (schurColumnCost b A B) := by
  apply ((hA.add hB).mul_left (1/2)).of_nonneg_of_le
    (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro i
  change ‖A.adjoint (b i)‖ * ‖B (b i)‖ ≤ 1/2*(‖A.adjoint (b i)‖^2+‖B (b i)‖^2)
  nlinarith [sq_nonneg (‖A.adjoint (b i)‖-‖B (b i)‖)]

/-- Cyclic trace of the two factors, with the cutoff removed. -/
def schurCycleTrace (A B : H →L[ℂ] H) (n : ℕ) : ℂ :=
  ∑' i, inner ℂ (A.adjoint (b i)) (((B*A)^n) (B (b i)))

variable [DecidableEq I]

private def schurDiagonal (s : Finset I) (A B : H →L[ℂ] H) (n : ℕ) (i : I) : ℂ :=
  if i ∈ s then inner ℂ (A.adjoint (b i)) (schurMiddle b s A B (B (b i)) n) else 0

private theorem schur_diagonal_bound (s : Finset I) (A B : H →L[ℂ] H) (n : ℕ) (i : I) :
    ‖schurDiagonal b s A B n i‖ ≤ (‖B‖*‖A‖)^n * schurColumnCost b A B i := by
  unfold schurDiagonal schurColumnCost
  split_ifs
  · exact (norm_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_left
      (schur_middle_bound b s A B (B (b i)) n) (norm_nonneg _)).trans_eq (by ring))
  · simp only [norm_zero]; positivity

private theorem schur_diagonal_trace (s : Finset I) (A B : H →L[ℂ] H) (n : ℕ) :
    ∑' i, schurDiagonal b s A B n i =
      ((schurSection b s A * schurSection b s B)^(n+1)).trace := by
  classical
  rw [tsum_eq_sum (s:=s) (fun i hi => show schurDiagonal b s A B n i = 0 from if_neg hi),Matrix.trace,←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro i _
  rw [schurDiagonal,if_pos i.property,ContinuousLinearMap.adjoint_inner_left]
  exact (schur_section_power_diagonal b s A B i n).symm

private theorem schur_trace_estimate (s : Finset I) (A B : H →L[ℂ] H)
    (hA : Summable (fun i => ‖A.adjoint (b i)‖^2)) (hB : Summable (fun i => ‖B (b i)‖^2)) (n : ℕ) :
    ‖((schurSection b s A * schurSection b s B)^(n+1)).trace‖ ≤
      (‖B‖*‖A‖)^n * ∑' i, schurColumnCost b A B i := by
  have hs := (schur_column_summable b A B hA hB).mul_left ((‖B‖*‖A‖)^n)
  have hnorm := hs.of_nonneg_of_le (fun i => norm_nonneg _) (schur_diagonal_bound b s A B n)
  rw [←schur_diagonal_trace b s A B n,←tsum_mul_left]
  exact (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum (schur_diagonal_bound b s A B n) hs)

theorem schur_trace_finite_section_limit (A B : H →L[ℂ] H)
    (hA : Summable (fun i => ‖A.adjoint (b i)‖^2)) (hB : Summable (fun i => ‖B (b i)‖^2)) (n : ℕ) :
    Tendsto (fun s => ((schurSection b s A * schurSection b s B)^(n+1)).trace)
      atTop (𝓝 (schurCycleTrace b A B n)) := by
  have hlim (i : I) : Tendsto (fun s => schurDiagonal b s A B n i) atTop
      (𝓝 (inner ℂ (A.adjoint (b i)) (((B*A)^n) (B (b i))))) := by
    apply (tendsto_const_nhds.inner (𝕜:=ℂ) (schur_middle_limit b A B (B (b i)) n)).congr'
    filter_upwards [eventually_ge_atTop ({i} : Finset I)] with s hs
    exact (if_pos (hs (Finset.mem_singleton_self i))).symm
  have hs := (schur_column_summable b A B hA hB).mul_left ((‖B‖*‖A‖)^n)
  have hx := tendsto_tsum_of_dominated_convergence hs hlim
    (Eventually.of_forall (fun s i => schur_diagonal_bound b s A B n i))
  simpa only [schur_diagonal_trace] using hx

/-- The determinant of the orthogonally truncated pair of actual
operators tends to the convergent exponential of their cyclic traces. -/
theorem twoBand_hilbert_schmidt_det_limit (A B : H →L[ℂ] H)
    (hA : Summable (fun i => ‖A.adjoint (b i)‖^2)) (hB : Summable (fun i => ‖B (b i)‖^2))
    (hr : ‖A‖*‖B‖ < 1) :
    let T := fun n : ℕ => schurCycleTrace b A B n / (n+1)
    Summable (fun n => ‖T n‖) ∧
      Tendsto (fun s : Finset I => (1-schurSection b s A * schurSection b s B).det)
        atTop (𝓝 (Complex.exp (-(∑' n, T n)))) := by
  intro T
  let K := fun s : Finset I => schurSection b s A * schurSection b s B
  let r := ‖B‖*‖A‖
  let C := ∑' i, schurColumnCost b A B i
  have hr0 : 0 ≤ r := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hr1 : r < 1 := (mul_comm ..).trans_lt hr
  have hK (s : Finset I) : ‖K s‖ < 1 :=
    (norm_mul_le _ _).trans_lt ((mul_le_mul (schur_section_opnorm b s A) (schur_section_opnorm b s B)
      (norm_nonneg _) (norm_nonneg _)).trans_lt hr)
  let f := fun (s : Finset I) (n : ℕ) => ((K s)^(n+1)).trace / ((n:ℂ)+1)
  have hlim (n : ℕ) : Tendsto (fun s => f s n) atTop (𝓝 (T n)) :=
    (schur_trace_finite_section_limit b A B hA hB n).div_const _
  have hb (s : Finset I) (n : ℕ) : ‖f s n‖ ≤ r^n*C := by
    have hN : 1 ≤ ‖(n:ℂ)+1‖ := by
      rw [←Nat.cast_one (R:=ℂ),←Nat.cast_add,Complex.norm_natCast]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    change ‖((K s)^(n+1)).trace / ((n:ℂ)+1)‖ ≤ _
    rw [norm_div]
    exact (div_le_self (norm_nonneg _) hN).trans (schur_trace_estimate b s A B hA hB n)
  have hs := (summable_geometric_of_lt_one hr0 hr1).mul_right C
  have hST := hs.of_nonneg_of_le (fun n => norm_nonneg (T n))
    (fun n => le_of_tendsto (hlim n).norm (Eventually.of_forall fun s => hb s n))
  have hx := tendsto_tsum_of_dominated_convergence hs hlim (Eventually.of_forall hb)
  refine ⟨hST,(Complex.continuous_exp.continuousAt.tendsto.comp hx.neg).congr' ?_⟩
  exact Eventually.of_forall fun s => (twoBand_contractive_det_series (K s) (hK s)).symm

end UV.SectorPlane
