import UV.ContinueTwoBandFredholmExpansion
import UV.ContinueTwoBandFourierRankOne

/-! All-coupling Fredholm determinants from absolutely summable rank-one
expansions. Independent orthogonal cutoffs on the two slot spaces can
be removed together; the principal-minor bound is uniform in both. -/

noncomputable section
open Matrix Filter Set
open scoped Topology Matrix.Norms.L2Operator InnerProductSpace ComplexConjugate

namespace UV.SectorPlane

variable {I J H : Type*} [DecidableEq I] [DecidableEq J]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def schurNuclearDet (v u : I → H) : ℂ :=
  ∑' t : Finset I, Matrix.det (fun i j : t => -inner ℂ (v i) (u j))

private def projectMinor (d : HilbertBasis J ℂ H) (v u : I → H)
    (s : Finset I × Finset J) (t : Finset I) : ℂ :=
  if t ⊆ s.1 then Matrix.det (fun i j : t => -inner ℂ (v i) (schurProject d s.2 (u j))) else 0

omit [DecidableEq J] in
private theorem project_minor_bound (d : HilbertBasis J ℂ H) (v u : I → H)
    (s : Finset I × Finset J) (t : Finset I) :
    ‖projectMinor d v u s t‖ ≤ ∏ i ∈ t, (‖v i‖*‖u i‖) := by
  unfold projectMinor
  split_ifs
  · have h := schur_mixed_gram_bound (fun i : t => v i) (fun j : t => -schurProject d s.2 (u j))
    simp only [inner_neg_right,norm_neg] at h
    refine h.trans ((Finset.prod_le_prod (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun (i : t) _ => mul_le_mul_of_nonneg_left (schur_project_le d s.2 (u i)) (norm_nonneg (v i)))).trans_eq ?_)
    exact Finset.prod_coe_sort t (fun i => ‖v i‖*‖u i‖)
  · rw [norm_zero]
    exact Finset.prod_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)

omit [DecidableEq J] in
private theorem project_minor_limit (d : HilbertBasis J ℂ H) (v u : I → H) (t : Finset I) :
    Tendsto (fun s => projectMinor d v u s t) atTop
      (𝓝 (Matrix.det (fun i j : t => -inner ℂ (v i) (u j)))) := by
  have hJ : Tendsto (fun s : Finset I × Finset J => s.2) atTop atTop := by
    rw [←prod_atTop_atTop_eq]
    exact tendsto_snd
  have hM : Tendsto (fun s : Finset I × Finset J => (Matrix.of (fun i j : t => -inner ℂ (v i) (schurProject d s.2 (u j))))) atTop
      (𝓝 (Matrix.of (fun i j : t => -inner ℂ (v i) (u j)))) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j =>
      (tendsto_const_nhds.inner (𝕜:=ℂ) ((schur_project_tendsto d (u j)).comp hJ)).neg
  apply (continuous_id.matrix_det.continuousAt.tendsto.comp hM).congr'
  filter_upwards [eventually_ge_atTop (t,(∅ : Finset J))] with s hs
  exact (if_pos hs.1).symm

omit [DecidableEq J] in
theorem schur_projected_nuclear_det_limit (d : HilbertBasis J ℂ H) (v u : I → H)
    (hs : Summable (fun i => ‖v i‖*‖u i‖)) :
    Tendsto (fun s : Finset I × Finset J => (1 + Matrix.of (fun i j : s.1 =>
      -inner ℂ (v i) (schurProject d s.2 (u j)))).det)
      atTop (𝓝 (schurNuclearDet v u)) := by
  have h := tendsto_tsum_of_dominated_convergence
    (schur_finset_product_summable _ (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hs)
    (project_minor_limit d v u) (Eventually.of_forall (fun s t => project_minor_bound d v u s t))
  apply h.congr' (Eventually.of_forall fun s => ?_)
  change (∑' t, projectMinor d v u s t) = _
  rw [tsum_eq_sum (s:=s.1.powerset) (fun t ht => show projectMinor d v u s t = 0 from
    if_neg (fun hsub => ht (Finset.mem_powerset.mpr hsub))),schur_cut_minor_sum s.1 (fun i j => -inner ℂ (v i) (schurProject d s.2 (u j)))]
  exact Finset.sum_congr rfl fun t ht => if_pos (Finset.mem_powerset.mp ht)

variable [CompleteSpace H]

/-- Entries of the two independently truncated hopping factors. -/
def schurBetween (b : HilbertBasis I ℂ H) (d : HilbertBasis J ℂ H)
    (s : Finset I) (t : Finset J) (A : H →L[ℂ] H) : Matrix s t ℂ :=
  fun i j => inner ℂ (b i) (A (d j))

omit [DecidableEq J] in
private theorem schur_between_pair (b : HilbertBasis I ℂ H) (d : HilbertBasis J ℂ H)
    (s : Finset I) (t : Finset J) (A B : H →L[ℂ] H) :
    1-schurBetween b d s t A * schurBetween d b t s B =
      (1 + Matrix.of (fun i j : s => -inner ℂ (A.adjoint (b i)) (schurProject d t (B (b j))))) := by
  rw [sub_eq_add_neg]
  congr 1
  ext i j
  change -(∑ k : t, inner ℂ (b i) (A (d k)) * inner ℂ (d k) (B (b j))) =
    -inner ℂ (A.adjoint (b i)) (∑ k : t, inner ℂ (d k) (B (b j)) • d k)
  simp only [inner_sum,inner_smul_right,ContinuousLinearMap.adjoint_inner_left]
  exact congrArg Neg.neg (Finset.sum_congr rfl fun k _ => mul_comm _ _)

omit [DecidableEq J] in
/-- Full ordinary Fredholm limit on two separately exhausted Hilbert
bases. The norm product is unrestricted. -/
theorem twoBand_fredholm_independent_sections (b : HilbertBasis I ℂ H) (d : HilbertBasis J ℂ H)
    (A B : H →L[ℂ] H) (hA : Summable (fun i => ‖A (b i)‖^2))
    (hB : Summable (fun i => ‖B (b i)‖^2)) :
    Tendsto (fun s : Finset I × Finset J =>
      (1 - schurBetween b d s.1 s.2 A * schurBetween d b s.2 s.1 B).det)
      atTop (𝓝 (schurNuclearDet (fun i => A.adjoint (b i)) (fun i => B (b i)))) := by
  have h := SlabKernel.square_adjoint_columns b A hA
  have hc : Summable (fun i => ‖A.adjoint (b i)‖ * ‖B (b i)‖) := ((h.add hB).mul_left (1/2)).of_nonneg_of_le
    (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun i => by
      change ‖A.adjoint (b i)‖*‖B (b i)‖ ≤ 1/2*(‖A.adjoint (b i)‖^2+‖B (b i)‖^2)
      nlinarith [sq_nonneg (‖A.adjoint (b i)‖-‖B (b i)‖)])

  apply (schur_projected_nuclear_det_limit d _ _ hc).congr
  intro s
  exact congrArg Matrix.det (schur_between_pair b d s.1 s.2 A B).symm

/-- Sylvester's finite-dimensional identity passes to independently
exhausted sections. This identifies the determinants of the two possible
eliminations even for different slot bases. -/
theorem schur_nuclear_exchange (b : HilbertBasis I ℂ H) (d : HilbertBasis J ℂ H)
    (A B : H →L[ℂ] H) (ha : Summable (fun i => ‖A (b i)‖^2)) (hb : Summable (fun i => ‖B (b i)‖^2))
    (ha' : Summable (fun i => ‖A (d i)‖^2)) (hb' : Summable (fun i => ‖B (d i)‖^2)) :
    schurNuclearDet (fun i => A.adjoint (b i)) (fun i => B (b i)) =
      schurNuclearDet (fun j => B.adjoint (d j)) (fun j => A (d j)) := by
  have h₁ := twoBand_fredholm_independent_sections b d A B ha hb
  have h₂ := twoBand_fredholm_independent_sections d b B A hb' ha'
  have hw : Tendsto (Prod.swap : Finset I × Finset J → Finset J × Finset I) atTop atTop := by
    rw [←prod_atTop_atTop_eq,←prod_atTop_atTop_eq]
    exact tendsto_prod_swap
  apply tendsto_nhds_unique h₁ ((h₂.comp hw).congr (fun s => ?_))
  exact Matrix.det_one_sub_mul_comm _ _

theorem schur_nuclear_basis_independent (b : HilbertBasis I ℂ H) (d : HilbertBasis J ℂ H)
    (A B : H →L[ℂ] H) (ha : Summable (fun i => ‖A (b i)‖^2)) (hb : Summable (fun i => ‖B (b i)‖^2))
    (ha' : Summable (fun i => ‖A (d i)‖^2)) (hb' : Summable (fun i => ‖B (d i)‖^2)) :
    schurNuclearDet (fun i => A.adjoint (b i)) (fun i => B (b i)) =
      schurNuclearDet (fun j => A.adjoint (d j)) (fun j => B (d j)) :=
  (schur_nuclear_exchange b d A B ha hb ha' hb').trans (schur_nuclear_exchange d d B A hb' ha' hb' ha')

end UV.SectorPlane
