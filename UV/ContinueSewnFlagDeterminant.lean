import UV.ContinueSewnFlagProjection
import UV.ContinueNetworkPrecisionChart
import UV.ContinueNetworkOrdered
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Data.Real.StarOrdered

/-! A positive routed Gram determinant dominates the contribution of
every invertible square selection of its actual loop rows. -/

noncomputable section
open Matrix Real Set
open scoped BigOperators Matrix
namespace UV.SewnFlags

open UV.ContinueNetworkPrecision

private theorem one_le_det_one_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    1 ≤ (1 + A).det := by
  let U := (hA.1.eigenvectorUnitary : Matrix ι ι ℝ)
  let a := hA.1.eigenvalues
  have hU : U * star U = 1 := (Matrix.mem_unitaryGroup_iff.mp hA.1.eigenvectorUnitary.2)
  have hA' : A = U * diagonal a * star U := hA.1.spectral_theorem
  have hD : U.det * (star U).det = 1 := by rw [← det_mul,hU,det_one]
  have he : 1 + A = U * diagonal (fun i => 1 + a i) * star U := by
    have h : diagonal (fun i => 1 + a i) = 1 + diagonal a := by
      ext i j
      by_cases hij : i=j <;> simp [hij]
    rw [h,mul_add,add_mul,mul_one,hU,← hA']
  rw [he,det_mul,det_mul,det_diagonal,mul_right_comm,hD,one_mul]
  simpa only [Finset.prod_const_one] using
    (Finset.prod_le_prod (s := Finset.univ) (f := fun _ : ι => (1:ℝ))
      (fun _ _ => zero_le_one) (fun i _ => le_add_of_nonneg_right (hA.eigenvalues_nonneg i)))

private theorem gram_posSemidef {E : Type*} [Fintype E] {L : ℕ}
    (C : Matrix E (Fin L) ℝ) (t : E → ℝ) (ht : ∀ e, 0 ≤ t e) :
    (residualGram C t).PosSemidef := by
  classical
  simpa only [residualGram,conjTranspose_eq_transpose_of_trivial] using
    (Matrix.PosSemidef.diagonal ht).conjTranspose_mul_mul_same C

def selectedRows {E : Type*} {L : ℕ} (C : Matrix E (Fin L) ℝ) (b : Fin L ↪ E) :
    Matrix (Fin L) (Fin L) ℝ := C.submatrix b id

private theorem selected_gram_difference {E : Type*} [Fintype E] {L : ℕ}
    (C : Matrix E (Fin L) ℝ) (t : E → ℝ) (ht : ∀ e, 0 ≤ t e) (b : Fin L ↪ E) :
    (residualGram C t - residualGram (selectedRows C b) (fun i => t (b i))).PosSemidef := by
  classical
  refine ⟨(gram_posSemidef C t ht).1.sub ((gram_posSemidef _ _ (fun i => ht (b i))).1), ?_⟩
  intro x
  rw [star_trivial,sub_mulVec,dotProduct_sub,residualGram_scalar_identity,residualGram_scalar_identity]
  apply sub_nonneg.mpr
  have he (i : Fin L) : (selectedRows C b *ᵥ x) i = (C *ᵥ x) (b i) := rfl
  simp_rw [he]
  calc _ = ∑ e ∈ Finset.univ.map b, t e * (C *ᵥ x) e ^ 2 :=
        (Finset.sum_map Finset.univ b (fun e => t e * (C *ᵥ x) e ^ 2)).symm
  _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun e _ _ =>
        mul_nonneg (ht e) (sq_nonneg _))

/-- The contribution of a selected square minor has the exact
determinant coefficient and one original duration for each selected row. -/
theorem routed_gram_dominates_selected_minor {E : Type*} [Fintype E] {L : ℕ}
    (C : Matrix E (Fin L) ℝ) (t : E → ℝ) (ht : ∀ e, 0 < t e)
    (b : Fin L ↪ E) (hb : (selectedRows C b).det ≠ 0) :
    (selectedRows C b).det^2*(∏ i, t (b i)) ≤ (residualGram C t).det := by
  let B := selectedRows C b
  let g := fun i => sqrt (t (b i))
  let P := diagonal g * B
  let M := residualGram C t
  have hPdet : P.det ≠ 0 := by
    unfold P
    rw [det_mul,det_diagonal]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => (sqrt_pos.mpr (ht (b i))).ne')) hb
  have hU : IsUnit P.det := isUnit_iff_ne_zero.mpr hPdet
  have hB : Pᵀ * P = residualGram B (fun i => t (b i)) := by
    unfold P residualGram
    rw [transpose_mul,diagonal_transpose,mul_assoc (Bᵀ),← mul_assoc (diagonal g),diagonal_mul_diagonal]
    have he : (fun i => g i*g i) = fun i => t (b i) := by
      funext i
      rw [← pow_two,sq_sqrt (ht (b i)).le]
    rw [he,← mul_assoc]
    congr!
  have hR : (M-Pᵀ*P).PosSemidef := by
    rw [hB]
    exact selected_gram_difference C t (fun e => (ht e).le) b
  have hR' : ((P⁻¹)ᵀ*(M-Pᵀ*P)*P⁻¹).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hR.conjTranspose_mul_mul_same P⁻¹
  have hI : (P⁻¹)ᵀ*(Pᵀ*P)*P⁻¹ = 1 := by
    calc _ = (P*P⁻¹)ᵀ*(P*P⁻¹) := by simp only [transpose_mul,mul_assoc]
    _ = _ := by rw [mul_nonsing_inv _ hU,transpose_one,one_mul]
  have hV := one_le_det_one_add hR'
  rw [mul_sub,sub_mul,hI,add_comm (1 : Matrix (Fin L) (Fin L) ℝ),
    sub_add_cancel] at hV
  have hInv : P⁻¹.det * P.det = 1 := det_nonsing_inv_mul_det _ hU
  rw [det_mul,det_mul,det_transpose] at hV
  have hP : P.det^2 ≤ M.det := by
    have h := mul_le_mul_of_nonneg_right hV (sq_nonneg P.det)
    have he : (P⁻¹.det*M.det*P⁻¹.det)*P.det^2 = M.det := by
      calc _ = (P⁻¹.det*P.det)^2*M.det := by ring
      _ = _ := by rw [hInv,one_pow,one_mul]
    rw [one_mul,he] at h
    exact h
  have hCoeff : P.det^2 = B.det^2 * ∏ i, t (b i) := by
    unfold P
    rw [det_mul,det_diagonal,mul_pow,← Finset.prod_pow,mul_comm]
    simp only [g,sq_sqrt (ht _).le]
  rwa [hCoeff] at hP

def routingShortPrefix {N : ℕ} (j : Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun i => i ≤ j

private def reverseRoutingRows {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ) (i : Fin N) :
    EuclideanSpace ℝ (Fin L) →ₗ[ℝ] ℝ :=
  (LinearMap.proj i.rev).comp ((Matrix.mulVecLin C).comp (WithLp.linearEquiv 2 ℝ (Fin L → ℝ)).toLinearMap)

private theorem routing_face_is_reverse_nullspace {N L : ℕ}
    (C : Matrix (Fin N) (Fin L) ℝ) (j : Fin N) :
    routingFace C (routingShortPrefix j) = nullPrefix (reverseRoutingRows C) j.rev.val := by
  ext x
  constructor
  · intro h i hi
    change (C *ᵥ x.ofLp) i.rev = 0
    apply h
    simpa only [routingShortPrefix,Finset.mem_filter,Finset.mem_univ,true_and,Fin.rev_le_iff]
      using (not_le.mpr hi)
  · intro h e he
    have hi : e.rev.val < j.rev.val := by
      have ht : ¬ j.rev ≤ e.rev := by simpa [routingShortPrefix,Fin.le_rev_iff] using he
      exact lt_of_not_ge ht
    have hz := h e.rev hi
    change (C *ᵥ x.ofLp) e.rev.rev = 0 at hz
    simpa only [Fin.rev_rev] using hz

/-- Scanning from largest to smallest duration selects one square
minor that realizes every short-prefix codimension simultaneously. -/
theorem reverse_greedy_routed_minor {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (hC : Function.Injective C.mulVec) :
    ∃ b : Fin L ↪ Fin N, (selectedRows C b).det ≠ 0 ∧ ∀ j : Fin N,
      Fintype.card {i : Fin L // b i ≤ j} =
        Module.finrank ℝ (routingFace C (routingShortPrefix j)) := by
  let rows := reverseRoutingRows C
  have hspan := rowSpan_top_of_injective rows (by
    intro x y h
    apply WithLp.ofLp_injective
    apply hC
    funext e
    have he := congrFun h e.rev
    change (C *ᵥ x.ofLp) e.rev.rev = (C *ᵥ y.ofLp) e.rev.rev at he
    simpa only [Fin.rev_rev] using he)
  let ee := greedyEuclideanIndex rows hspan
  let b : Fin L ↪ Fin N := ⟨fun i => (ee i).1.rev,
    fun _ _ h => ee.injective (Subtype.ext (Fin.rev_injective h))⟩
  refine ⟨b, ?_, ?_⟩
  · apply (isUnit_iff_ne_zero).mp
    apply (Matrix.isUnit_iff_isUnit_det _).1
    apply Matrix.mulVec_injective_iff_isUnit.1
    intro x y h
    have he : greedyCoordinates rows hspan (WithLp.toLp 2 x) =
        greedyCoordinates rows hspan (WithLp.toLp 2 y) := by
      funext i
      let k := ee.symm i
      have hk : ee k = i := ee.apply_symm_apply i
      rw [← hk,greedyCoordinates_apply,greedyCoordinates_apply]
      exact congrFun h k
    exact congrArg WithLp.ofLp ((greedyCoordinates rows hspan).injective he)
  · intro j
    rw [routing_face_is_reverse_nullspace, nullPrefix_finrank rows hspan j.rev.isLt.le]
    let f : {i : Fin L // b i ≤ j} ≃ WeakIndex rows j.rev.val :=
      ee.subtypeEquiv (fun i => by
        change (ee i).1.rev ≤ j ↔ j.rev.val ≤ (ee i).1.val
        exact Fin.rev_le_iff)
    exact Fintype.card_congr f

private theorem selected_duration_ratio_product {N L : ℕ} (b : Fin L ↪ Fin N) {t : Fin N → ℝ}
    (ht : t ∈ directionalOrderedSet N) :
    (∏ i, t (b i)) =
      ∏ j, directionalOrderedRatios t j^Fintype.card {i : Fin L // b i ≤ j} := by
  have h₁ (i : Fin L) := directionalOrderedTime_eq_ratio_product ht (b i)
  simp_rw [h₁]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  rw [← Finset.prod_filter,Finset.prod_const,Fintype.card_subtype]

/-- One fixed, positive minor constant suffices on the entire positive
short-time chamber. Its exponent on each Schwinger ratio is exactly
the dimension of the loop directions invisible outside that prefix. -/
theorem short_routed_determinant_bound {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (hC : Function.Injective C.mulVec) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : Fin N → ℝ, t ∈ directionalOrderedSet N →
      K * (∏ j, directionalOrderedRatios t j ^
        Module.finrank ℝ (routingFace C (routingShortPrefix j))) ≤ (residualGram C t).det := by
  obtain ⟨b,hb,hcount⟩ := reverse_greedy_routed_minor C hC
  refine ⟨(selectedRows C b).det^2,sq_pos_of_ne_zero hb,?_⟩
  intro t ht
  have hp (i : Fin N) : 0 < t i := ((directionalOrderedSet_mem_iff t).1 ht).2 i |>.1
  have h := routed_gram_dominates_selected_minor C t hp b hb
  rw [selected_duration_ratio_product b ht] at h
  simpa only [hcount] using h

end UV.SewnFlags
