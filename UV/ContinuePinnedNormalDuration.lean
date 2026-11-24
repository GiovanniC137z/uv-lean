import UV.ContinueRetainedFacesPhysical

/-! For equal held positions the normal Gaussian leaves the polynomial
`(∏ t) det(C_I diag(t⁻¹) C_Iᵀ)`. Increasing durations give decreasing
precision weights. A greedy basis for the latter selects the maximal
complementary monomial and realizes the exact corner exponents. -/

noncomputable section
open MeasureTheory Real Filter Set Matrix UV.ContinueNetworkPrecision
open scoped ENNReal BigOperators Matrix
namespace UV

def pinnedDurationPolynomial {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (t : Fin n → ℝ) : ℝ :=
  (∏ i, t i) * retainedGramDet A (fun i => (t i)⁻¹)

def pinnedDurationNullity {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (S : Finset (Fin n)) : ℕ :=
  S.card - (retainedColumns A S).rank

private theorem pinned_complement_product {n : ℕ} (B : Finset (Fin n)) (t : Fin n → ℝ)
    (ht : ∀ i, 0 < t i) :
    (∏ i, t i) * (∏ i ∈ B, (t i)⁻¹) = ∏ i ∈ Bᶜ, t i := by
  rw [Finset.prod_inv_distrib,← Finset.prod_mul_prod_compl B t,mul_right_comm,mul_inv_cancel₀,
    one_mul]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => (ht i).ne')

/-- The exact positive polynomial is the complementary Cauchy–Binet
sum with the square of each original incidence minor as coefficient. -/
theorem pinnedDurationPolynomial_eq_minor_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (t : Fin n → ℝ) (ht : ∀ i, 0 < t i) :
    pinnedDurationPolynomial A t = ∑ B ∈ Finset.univ.powersetCard (Fintype.card ι),
      retainedMinorCoefficient A B * ∏ i ∈ Bᶜ, t i := by
  unfold pinnedDurationPolynomial
  rw [retainedGramDet_eq_basis_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B _
  rw [mul_left_comm,pinned_complement_product B t ht]

theorem pinnedDurationPolynomial_ordered_bounds {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (hA : A.rank = Fintype.card ι) :
    let B := (greedyRows A.col n)ᶜ
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧ ∀ t : Fin n → ℝ,
      Monotone t → (∀ i, 0 < t i) →
      lo * (∏ i ∈ B, t i) ≤ pinnedDurationPolynomial A t ∧
      pinnedDurationPolynomial A t ≤ hi * (∏ i ∈ B, t i) := by
  dsimp only
  obtain ⟨lo,hi,hlo,hhi,h⟩ := retainedGramDet_greedy_comparison A hA
  refine ⟨lo,hi,hlo,hhi,fun t hmono ht => ?_⟩
  have hAnti : Antitone (fun i => (t i)⁻¹) := fun i j hij => inv_anti₀ (ht i) (hmono hij)
  obtain ⟨hl,hu⟩ := h (fun i => (t i)⁻¹) hAnti (fun i => inv_nonneg.mpr (ht i).le)
  have hW : 0 ≤ ∏ i, t i := Finset.prod_nonneg (fun i _ => (ht i).le)
  have hl' := mul_le_mul_of_nonneg_left hl hW
  have hu' := mul_le_mul_of_nonneg_left hu hW
  rw [mul_left_comm,pinned_complement_product _ t ht] at hl'
  rw [mul_left_comm (∏ i, t i) hi,pinned_complement_product _ t ht] at hu'
  exact ⟨hl',hu'⟩

private def pinnedDurationExponent {n : ℕ} (η : Fin n → ℝ) (α : ℝ)
    (B : Finset (Fin n)) (i : Fin n) : ℝ :=
  η i - α*(if i ∈ B then 1 else 0)

private theorem pinnedDurationExponent_density {n : ℕ} (η : Fin n → ℝ) (α : ℝ)
    (B : Finset (Fin n)) (t : Fin n → ℝ) (ht : ∀ i, 0 < t i) :
    directionalOrderedDensity (pinnedDurationExponent η α B) t =
      ENNReal.ofReal ((retainedWidthDensity η t) * (∏ i ∈ B, t i)^(-α)) := by
  have he (i : Fin n) : t i^(pinnedDurationExponent η α B i-1) =
      t i^(η i-1) * if i ∈ B then t i^(-α) else 1 := by
    unfold pinnedDurationExponent
    by_cases h : i ∈ B
    · rw [if_pos h,if_pos h,mul_one,show η i-α-1 = (η i-1)+(-α) by ring,rpow_add (ht i)]
    · rw [if_neg h,if_neg h,mul_zero,sub_zero,mul_one]
  unfold directionalOrderedDensity retainedWidthDensity
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => rpow_nonneg (ht i).le _)]
  simp_rw [he]
  rw [Finset.prod_mul_distrib,← Finset.prod_filter,Finset.filter_mem_eq_inter,Finset.univ_inter,
    Real.finset_prod_rpow _ _ (fun i _ => (ht i).le)]

private theorem pinnedDurationExponent_prefix {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (η : Fin n → ℝ) (α : ℝ) (j : Fin n) :
    let S := Finset.univ.filter (fun i : Fin n => i ≤ j)
    directionalOrderedPrefix (pinnedDurationExponent η α (greedyRows A.col n)ᶜ) j =
      (∑ i ∈ S, η i) - α * pinnedDurationNullity A S := by
  classical
  dsimp only
  let S := Finset.univ.filter (fun i : Fin n => i ≤ j)
  let G := greedyRows A.col n
  have hG : (S.filter (· ∈ G)).card = (retainedColumns A S).rank := by
    have he : S.filter (· ∈ G) = G.filter (fun i => i.val < j.val+1) := by
      ext i
      simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,Fin.le_def,Nat.lt_succ_iff,and_comm]
    rw [he,greedyRows_filter_prefix _ j.isLt]
    have h := retainedGreedy_prefix_count A (j.val+1)
    have hS : (Finset.univ.filter fun i : Fin n => i.val < j.val+1) = S := by
      ext i
      simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,Fin.le_def,Nat.lt_succ_iff]
    rw [hS] at h
    exact h
  have hC : (S.filter (· ∈ Gᶜ)).card = pinnedDurationNullity A S := by
    have h := Finset.filter_card_add_filter_neg_card_eq_card (s := S) (fun i => i ∈ G)
    simp_rw [← Finset.mem_compl] at h
    rw [hG] at h
    unfold pinnedDurationNullity
    omega
  unfold directionalOrderedPrefix pinnedDurationExponent
  rw [← Finset.sum_filter,Finset.sum_sub_distrib,← Finset.mul_sum]
  change _ - α*(∑ i ∈ S, if i ∈ Gᶜ then (1:ℝ) else 0) = _
  have hSum : (∑ i ∈ S, if i ∈ Gᶜ then (1:ℝ) else 0) = (S.filter (· ∈ Gᶜ)).card := by
    rw [← Finset.sum_filter]
    simp
  rw [hSum,hC]

def pinnedDurationDensity {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (η : Fin n → ℝ) (α : ℝ) (t : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (retainedWidthDensity η t * (pinnedDurationPolynomial A t)^(-α))

private theorem pinnedDurationDensity_sector_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (hA : A.rank = Fintype.card ι)
    (η : Fin n → ℝ) {α : ℝ} (hα : 0 ≤ α) :
    (∫⁻ t in directionalOrderedSet n, pinnedDurationDensity A η α t) < ⊤ ↔
      ∀ j : Fin n, let S := Finset.univ.filter (fun i : Fin n => i ≤ j)
        α * pinnedDurationNullity A S < ∑ i ∈ S, η i := by
  let B := (greedyRows A.col n)ᶜ
  obtain ⟨lo,hi,hlo,hhi,hbounds⟩ := pinnedDurationPolynomial_ordered_bounds A hA
  have hLo : 0 < hi^(-α) := rpow_pos_of_pos hhi _
  have hHi : 0 < lo^(-α) := rpow_pos_of_pos hlo _
  have hb (t : Fin n → ℝ) (hmem : t ∈ directionalOrderedSet n) :
      ENNReal.ofReal (hi^(-α)) * directionalOrderedDensity (pinnedDurationExponent η α B) t ≤
        pinnedDurationDensity A η α t ∧
      pinnedDurationDensity A η α t ≤
        ENNReal.ofReal (lo^(-α)) * directionalOrderedDensity (pinnedDurationExponent η α B) t := by
    obtain ⟨hs,ht⟩ := (directionalOrderedSet_mem_iff t).mp hmem
    have ht₀ (i : Fin n) : 0 < t i := (ht i).1
    let P := ∏ i ∈ B, t i
    have hP : 0 < P := Finset.prod_pos (fun i _ => ht₀ i)
    obtain ⟨hl,hu⟩ := hbounds t hs.monotone ht₀
    have hp : 0 < pinnedDurationPolynomial A t := (mul_pos hlo hP).trans_le hl
    have hW : 0 ≤ retainedWidthDensity η t := Finset.prod_nonneg (fun i _ => rpow_nonneg (ht₀ i).le _)
    rw [pinnedDurationExponent_density η α B t ht₀, ← ENNReal.ofReal_mul hLo.le,
      ← ENNReal.ofReal_mul hHi.le]
    unfold pinnedDurationDensity
    change ENNReal.ofReal (hi^(-α) * (retainedWidthDensity η t * P^(-α))) ≤ _ ∧
      _ ≤ ENNReal.ofReal (lo^(-α) * (retainedWidthDensity η t * P^(-α)))
    constructor
    · rw [mul_left_comm,← mul_rpow hhi.le hP.le]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (rpow_le_rpow_of_nonpos hp hu (neg_nonpos.mpr hα)) hW)
    · rw [mul_left_comm (lo^(-α)),← mul_rpow hlo.le hP.le]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (rpow_le_rpow_of_nonpos (mul_pos hlo hP) hl (neg_nonpos.mpr hα)) hW)
  refine (retainedIntegral_comparable _ _ _ _ _ (ENNReal.ofReal_ne_zero_iff.mpr hLo)
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    ((ae_restrict_mem (directionalOrderedSet_open n).measurableSet).mono hb)).trans ?_
  change directionalOrderedCost (pinnedDurationExponent η α B) < ⊤ ↔ _
  rw [directionalOrderedCost_finite_iff]
  simp only [B,pinnedDurationExponent_prefix,sub_pos]

private theorem pinnedDurationDensity_reindex {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (σ : Equiv.Perm (Fin n)) (η : Fin n → ℝ) (α : ℝ)
    (t : Fin n → ℝ) :
    pinnedDurationDensity (A.submatrix id σ) (η ∘ σ) α t =
      pinnedDurationDensity A η α (t ∘ σ.symm) := by
  have hprod := (Equiv.prod_comp σ.symm t).symm
  have hW : retainedWidthDensity (η ∘ σ) t = retainedWidthDensity η (t ∘ σ.symm) := by
    unfold retainedWidthDensity
    exact Fintype.prod_equiv σ _ _ (by intro i; simp)
  unfold pinnedDurationDensity pinnedDurationPolynomial
  rw [hW,retainedGramDet_reindex,hprod]
  rfl

/-- Sharp simultaneous short-duration criterion for the actual positive
complementary determinant. Every nonempty edge set is tested by an
ordering, including equality faces where the integral diverges. -/
theorem pinnedDurationDensity_finite_iff_faces {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (hA : A.rank = Fintype.card ι)
    (η : Fin n → ℝ) {α : ℝ} (hα : 0 ≤ α) :
    (∫⁻ t, pinnedDurationDensity A η α t ∂directionalSchwingerMeasure (Fin n)) < ⊤ ↔
      ∀ S : Finset (Fin n), S.Nonempty → α * pinnedDurationNullity A S < ∑ i ∈ S, η i := by
  have hs (σ : Equiv.Perm (Fin n)) : (A.submatrix id σ).rank = Fintype.card ι :=
    (Matrix.rank_submatrix A (Equiv.refl ι) σ).trans hA
  rw [directionalSchwinger_finite_iff_ordered_sectors]
  simp_rw [directionalPermutedSector_lintegral_eq,← pinnedDurationDensity_reindex,
    pinnedDurationDensity_sector_iff _ (hs _) _ hα]
  have he (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
      (α * pinnedDurationNullity (A.submatrix id σ) S < ∑ i ∈ S, (η ∘ σ) i) ↔
        α * pinnedDurationNullity A (S.map σ.toEmbedding) < ∑ i ∈ S.map σ.toEmbedding, η i := by
    unfold pinnedDurationNullity
    rw [retainedColumns_rank_map,Finset.card_map,Finset.sum_map]
    rfl
  simp_rw [he]
  constructor
  · intro h S hS
    obtain ⟨σ,j,_,hj⟩ := route_subset_is_nonempty_prefix S hS
    exact hj ▸ h σ j
  · intro h σ j
    apply h
    refine ⟨σ j,Finset.mem_map.mpr ⟨j,?_ ,rfl⟩⟩
    simp

end UV
