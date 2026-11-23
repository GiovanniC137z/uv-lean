import UV.ContinueCollarCompactBasis
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! A summable family of squared basis-column norms yields a compact
operator by explicit finite-rank approximations in operator norm. -/

noncomputable section

open Set MeasureTheory Filter Metric
open scoped InnerProductSpace Topology

namespace UV.CollarEigenmode

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem opNorm_sq_le_columns (b : HilbertBasis ι ℝ H) (T : H →L[ℝ] H)
    (hs : Summable (fun i => ‖T (b i)‖^2)) :
    ‖T‖^2 ≤ ∑' i,‖T (b i)‖^2 := by
  let g : ℓ²(ι,ℝ) := ⟨fun i => ‖T (b i)‖,memℓp_gen (by simpa using hs)⟩
  have hg (i : ι) : ‖g i‖ = ‖T (b i)‖ := by simp [g]
  have hb : ‖T‖ ≤ ‖g‖ := by
    apply T.opNorm_le_bound (norm_nonneg _)
    intro x
    have h := lp.tsum_mul_le_mul_norm (p := 2) (q := 2) (by rw [Real.holderConjugate_iff]; norm_num) (b.repr x) g
    have H := (b.hasSum_repr x).mapL T
    simp only [map_smul] at H
    rw [← H.tsum_eq]
    apply (norm_tsum_le_tsum_norm (by simpa only [norm_smul,hg] using h.1)).trans
    simpa only [b.repr.norm_map,hg,norm_smul,mul_comm ‖g‖] using h.2
  have hsum := (lp.hasSum_norm (p := 2) (by norm_num) g).tsum_eq
  norm_num [hg] at hsum
  exact (pow_le_pow_left₀ (norm_nonneg _) hb 2).trans_eq hsum.symm

omit [CompleteSpace H] in
private theorem compact_rank_one (l : H →L[ℝ] ℝ) (v : H) : IsCompactOperator (l.smulRight v) := by
  apply (isCompactOperator_iff_image_closedBall_subset_compact (l.smulRight v).toLinearMap zero_lt_one).mpr
  refine ⟨(fun r : ℝ => r • v) '' Icc (-‖l‖) ‖l‖,isCompact_Icc.image (continuous_id.smul continuous_const),?_⟩
  rintro _ ⟨x,hx,rfl⟩
  have hnorm := (l.le_opNorm x).trans (mul_le_of_le_one_right (norm_nonneg _) (by simpa using hx))
  exact ⟨l x,abs_le.mp (by simpa only [Real.norm_eq_abs] using hnorm),rfl⟩

theorem compact_of_square_columns (b : HilbertBasis ι ℝ H) (T : H →L[ℝ] H)
    (hs : Summable (fun i => ‖T (b i)‖^2)) : IsCompactOperator T := by
  classical
  let P (i : ι) := (innerSL ℝ (b i)).smulRight (T (b i))
  have hPc (s : Finset ι) : IsCompactOperator (∑ i ∈ s,P i : H →L[ℝ] H) := by
    induction s using Finset.induction with
    | empty => simpa using (isCompactOperator_zero (M₁ := H) (M₂ := H))
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (compact_rank_one _ _).add ih
  have ht (s : Finset ι) (j : ι) : (T-∑ i ∈ s,P i) (b j) = if j ∈ s then 0 else T (b j) := by
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.sum_apply,P,ContinuousLinearMap.smulRight_apply,innerSL_apply,
      orthonormal_iff_ite.mp b.orthonormal,ite_smul,one_smul,zero_smul]
    by_cases h : j ∈ s <;> simp [h]
  have hp (s : Finset ι) : ‖T-∑ i ∈ s,P i‖^2 ≤ (∑' i,‖T (b i)‖^2)-∑ i ∈ s,‖T (b i)‖^2 := by
    let F := fun i => ‖T (b i)‖^2
    let trunc := fun i => if i ∈ s then F i else 0
    have htr : HasSum trunc (∑ i ∈ s,F i) := by
      have h : HasSum trunc (∑ i ∈ s,trunc i) := hasSum_sum_of_ne_finset_zero (s := s) (f := trunc) (fun i hi => if_neg hi)
      simpa [trunc] using h
    have hdiff : (fun i => ‖(T-∑ j ∈ s,P j) (b i)‖^2) = fun i => F i-trunc i := by
      funext i
      by_cases h : i ∈ s <;> simp [ht,trunc,F,h]
    have hh := hs.hasSum.sub htr
    rw [←hdiff] at hh
    exact (opNorm_sq_le_columns b _ hh.summable).trans_eq hh.tsum_eq
  have hcl : T ∈ closure {A : H →L[ℝ] H | IsCompactOperator A} := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    have hlim := (tendsto_const_nhds (x := ∑' i,‖T (b i)‖^2)).sub hs.hasSum
    have hev : ∀ᶠ s : Finset ι in atTop,(∑' i,‖T (b i)‖^2)-(∑ i ∈ s,‖T (b i)‖^2)<ε^2 :=
      hlim.eventually_lt_const (by simpa using sq_pos_of_pos hε)
    obtain ⟨s,hs'⟩ := hev.exists
    refine ⟨∑ i ∈ s,P i,hPc s,?_⟩
    rw [dist_eq_norm]
    nlinarith only [(hp s).trans_lt hs',hε,norm_nonneg (T-∑ i ∈ s,P i)]
  rw [isClosed_setOf_isCompactOperator.closure_eq] at hcl
  exact hcl

end UV.CollarEigenmode
