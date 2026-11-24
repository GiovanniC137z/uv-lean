import UV.ContinueTwoBandFredholm
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! Absolute summability of the finite principal minors of a summable
rank-one representation. The bounds hold at arbitrary coupling. -/

noncomputable section
open Matrix Filter Set Module Submodule InnerProductSpace
open scoped Topology InnerProductSpace ComplexConjugate

namespace UV.SectorPlane

private theorem gram_basis_det_bound {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (d : OrthonormalBasis ι ℂ E) (x : ι → E) :
    ‖d.toBasis.det x‖ ≤ ∏ i, ‖x i‖ := by
  have hd : finrank ℂ E = Fintype.card ι := finrank_eq_card_basis d.toBasis
  let b := gramSchmidtOrthonormalBasis hd x
  have h : d.toBasis.det x = d.toBasis.det b * b.toBasis.det x := by
    simp only [Basis.det_apply,←Matrix.det_mul]
    exact congrArg Matrix.det (d.toBasis.toMatrix_mul_toMatrix b.toBasis x).symm
  rw [h,norm_mul,d.det_to_matrix_orthonormalBasis b,one_mul,
    show b.toBasis.det x = _ from gramSchmidtOrthonormalBasis_det hd x,norm_prod]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => ?_)
  simpa only [b.orthonormal.norm_eq_one, one_mul] using norm_inner_le_norm (𝕜:=ℂ) (b i) (x i)

private theorem gram_mixed_bound_ordered {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (v u : ι → H) :
    ‖Matrix.det (fun i j => inner ℂ (v i) (u j))‖ ≤ ∏ i, (‖v i‖*‖u i‖) := by
  classical
  let G : Matrix ι ι ℂ := fun i j => inner ℂ (v i) (u j)
  by_cases he : G.det = 0
  · rw [show Matrix.det (fun i j => inner ℂ (v i) (u j)) = 0 from he,norm_zero]
    exact Finset.prod_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hu : LinearIndependent ℂ u := by
    let f : H →ₗ[ℂ] (ι → ℂ) := LinearMap.pi fun i => (innerSL ℂ (v i)).toLinearMap
    exact (show LinearIndependent ℂ (f ∘ u) from Matrix.linearIndependent_cols_of_det_ne_zero he).of_comp f
  let V := span ℂ (range u)
  let e := Basis.span hu
  letI : FiniteDimensional ℂ V := FiniteDimensional.of_fintype_basis e
  let d : OrthonormalBasis ι ℂ V := gramSchmidtOrthonormalBasis (finrank_eq_card_basis e) e
  let v' := fun i => V.orthogonalProjection (v i)
  have hproj (i j : ι) : inner ℂ (v' i) (e j) = G i j := by
    change inner ℂ (V.orthogonalProjection (v i)) (e j) = _
    rw [inner_orthogonalProjection_eq_of_mem_right]
    exact congrArg (inner ℂ (v i)) (Basis.span_apply hu j)
  let M := d.toBasis.toMatrix v'
  let N := d.toBasis.toMatrix e
  have hfac : Mᴴ*N = G := by
    ext i j
    rw [Matrix.mul_apply,← hproj]
    convert d.sum_inner_mul_inner (v' i) (e j) using 1
    apply Finset.sum_congr rfl
    intro k _
    simp [M,N,Matrix.conjTranspose_apply,Basis.toMatrix_apply,OrthonormalBasis.coe_toBasis_repr_apply,
      d.repr_apply_apply]
  change ‖G.det‖ ≤ _
  rw [←hfac,Matrix.det_mul,norm_mul,Matrix.det_conjTranspose,norm_star,Finset.prod_mul_distrib]
  apply mul_le_mul _ _ (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  · apply (gram_basis_det_bound d v').trans
    apply Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => ?_)
    exact V.norm_orthogonalProjection_apply_le (v i)
  · apply (gram_basis_det_bound d e).trans_eq
    exact Finset.prod_congr rfl fun i _ => congrArg norm (Basis.span_apply hu i)

theorem schur_mixed_gram_bound {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (v u : ι → H) :
    ‖Matrix.det (fun i j => inner ℂ (v i) (u j))‖ ≤ ∏ i, (‖v i‖*‖u i‖) := by
  classical
  let e := (Fintype.equivFin ι).symm
  let M : Matrix ι ι ℂ := fun i j => inner ℂ (v i) (u j)
  have h := gram_mixed_bound_ordered (v ∘ e) (u ∘ e)
  change ‖(M.submatrix e e).det‖ ≤ ∏ i, (fun j => ‖v j‖*‖u j‖) (e i) at h
  rw [Matrix.det_submatrix_equiv_self] at h
  exact h.trans_eq (e.prod_comp (fun j => ‖v j‖*‖u j‖))

theorem schur_finset_product_summable {I : Type*} (c : I → ℝ) (hn : ∀ i, 0 ≤ c i)
    (hs : Summable c) : Summable (fun t : Finset I => ∏ i ∈ t, c i) := by
  classical
  apply summable_of_sum_le (fun s => Finset.prod_nonneg fun i _ => hn i) (c := Real.exp (∑' i, c i))
  intro S
  let U := S.biUnion id
  have hsub : S ⊆ U.powerset := by
    intro s hs
    exact Finset.mem_powerset.mpr (fun i hi => Finset.mem_biUnion.mpr ⟨s,hs,hi⟩)
  calc
    _ ≤ ∑ t ∈ U.powerset, ∏ i ∈ t, c i := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun t _ _ => Finset.prod_nonneg fun i _ => hn i)
    _ = ∏ i ∈ U, (1+c i) := U.prod_one_add.symm
    _ ≤ ∏ i ∈ U, Real.exp (c i) := Finset.prod_le_prod
      (fun i _ => by linarith [hn i]) (fun i _ => by linarith [Real.add_one_le_exp (c i)])
    _ = Real.exp (∑ i ∈ U, c i) := (Real.exp_sum ..).symm
    _ ≤ _ := Real.exp_le_exp.mpr (hs.sum_le_tsum U fun i _ => hn i)

/-- Every finite mixed Gram determinant in the nuclear expansion is
absolutely summable over finite subsets, at arbitrary real or complex
coupling absorbed into either family. -/
theorem schur_nuclear_minor_summable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [DecidableEq I] (v u : I → H) (hs : Summable (fun i => ‖v i‖*‖u i‖)) :
    Summable (fun t : Finset I => ‖Matrix.det (fun i j : t => inner ℂ (v i) (u j))‖) := by
  apply (schur_finset_product_summable _ (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hs).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun t => ?_)
  exact (schur_mixed_gram_bound (fun i : t => v i) (fun i : t => u i)).trans_eq
    (Finset.prod_coe_sort t (fun i => ‖v i‖*‖u i‖))

end UV.SectorPlane
