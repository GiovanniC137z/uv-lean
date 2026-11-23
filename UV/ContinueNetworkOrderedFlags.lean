import UV.ContinueNetworkOrderedCentered
import UV.ContinueNetworkPrecisionDegreeChart
import UV.ContinueNetworkPrecisionDegreeCost

/-! Match the selected weak coordinates and ordered route labels with
the original routed kernel flags in momentum space. -/

noncomputable section

open scoped BigOperators ENNReal

namespace UV

open ContinueNetworkPrecision

/-- The prefix includes the route at position j. -/
def directionalSectorPrefixEdges {m : ℕ} (j : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => i ≤ j)

theorem directionalSectorPrefixEdges_mem {m : ℕ} (j e : Fin m) :
    e ∈ directionalSectorPrefixEdges j ↔ e ≤ j := by
  simp [directionalSectorPrefixEdges]

private theorem directionalWeakRow_mem_prefix {m d : ℕ}
    (label : Fin d → Option (Fin m)) (j : Fin m) (i : Fin d) :
    i ∈ directionalGaussianWeakRows label (directionalSectorPrefixEdges j) ↔
      (label i).elim False (fun e => e ≤ j) := by
  unfold directionalGaussianWeakRows
  cases h : label i with
  | none => simp [h, Finset.mem_map]
  | some e => simp [h, Finset.mem_map, directionalSectorPrefixEdges]

private theorem directionalWeakRow_strong_prefix {m d : ℕ}
    (label : Fin d → Option (Fin m)) (j : Fin m) (i : Fin d) :
    i ∉ directionalGaussianWeakRows label (directionalSectorPrefixEdges j) ↔
      (label i).elim True (fun e => j.val + 1 ≤ e.val) := by
  rw [directionalWeakRow_mem_prefix]
  cases label i with
  | none => simp
  | some e =>
      change ¬ e.val ≤ j.val ↔ j.val + 1 ≤ e.val
      omega

/-- Turn the greedy flags in slot-index notation into the actual selected
weak coordinate set used by polynomial degree and Gaussian powers. -/
theorem directionalSectorFlag_weak_coordinates {m d a : ℕ} {b : Fin m → ℕ}
    (A : DirectionalMomentum d →ₗ[ℝ] DirectionalMomentum a)
    (C : ∀ e, DirectionalMomentum d →ₗ[ℝ] DirectionalMomentum (b e))
    (chart : DirectionalMomentum d ≃L[ℝ] DirectionalMomentum d)
    (label : Fin d → Option (Fin m))
    (hflag : ∀ j : ℕ, j ≤ m →
        Module.finrank ℝ (sourceNullFlag A C j) =
          Nat.card {i : Fin d // (label i).elim False (fun e => e.val < j)} ∧
        ∀ k : DirectionalMomentum d, k ∈ sourceNullFlag A C j ↔
          ∀ i : Fin d, (label i).elim True (fun e => j ≤ e.val) → chart k i = 0)
    (j : Fin m) :
    Module.finrank ℝ (sourceNullFlag A C (j.val + 1)) =
      (directionalGaussianWeakRows label (directionalSectorPrefixEdges j)).card ∧
    ∀ k : DirectionalMomentum d, k ∈ sourceNullFlag A C (j.val + 1) ↔
      ∀ i ∉ directionalGaussianWeakRows label (directionalSectorPrefixEdges j), chart k i = 0 := by
  obtain ⟨hc, hk⟩ := hflag (j.val + 1) j.isLt
  refine ⟨?_, fun k => ?_⟩
  · classical
    rw [hc, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext i
    rw [directionalWeakRow_mem_prefix]
    cases h : label i with
    | none => simp [h]
    | some e =>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, h, Option.elim_some]
        change e.val < j.val + 1 ↔ e.val ≤ j.val
        omega
  · rw [hk k]
    exact forall_congr' fun i => imp_congr (directionalWeakRow_strong_prefix label j i).symm Iff.rfl

/-- The strict endpoint inequalities on supported monomials are exactly
the physical subspace dimension and ray-degree inequalities for one
ordered sector. Zero-dimensional flags are automatic at positive line powers. -/
theorem directionalCenteredSectorCost_finite_iff_power {m d a : ℕ} {b : Fin m → ℕ}
    (A : DirectionalMomentum d →ₗ[ℝ] DirectionalMomentum a)
    (C : ∀ e, DirectionalMomentum d →ₗ[ℝ] DirectionalMomentum (b e))
    (ν : Fin m → ℝ) (P : MvPolynomial (Fin d) ℂ)
    (hν : ∀ e, 0 < ν e) (hP : P ≠ 0)
    (hinj : Function.Injective (fun k : DirectionalMomentum d => (A k, fun e => C e k))) :
    directionalCenteredSectorCost A C ν P < ⊤ ↔
      ∀ j : Fin m,
        let K := sourceNullFlag A C (j.val + 1)
        0 < Module.finrank ℝ K →
          (Module.finrank ℝ K : ℝ) + directionalDegree K P <
            2 * ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ≤ j), ν i := by
  obtain ⟨chart, label, hflag, hcost⟩ := directionalCenteredSectorCost_finite_iff A C ν P hinj
  let T := directionalPolynomialComposeLinear chart.symm.toContinuousLinearMap P
  have hT : T ≠ 0 := directionalPolynomialComposeLinear_ne_zero chart.symm hP
  let K (j : Fin m) := sourceNullFlag A C (j.val + 1)
  let W (j : Fin m) := directionalGaussianWeakRows label (directionalSectorPrefixEdges j)
  have hdim (j : Fin m) : Module.finrank ℝ (K j) = (W j).card :=
    (directionalSectorFlag_weak_coordinates A C chart label hflag j).1
  have hdeg (j : Fin m) : directionalDegree (K j) P = weakDegree (W j) T :=
    directionalDegree_eq_weakDegree P hP (K j) chart (W j)
      (directionalSectorFlag_weak_coordinates A C chart label hflag j).2
  have hsum (j : Fin m) :
      directionalOrderedPrefix ν j = ∑ i ∈ directionalSectorPrefixEdges j, ν i := by
    simp only [directionalOrderedPrefix, directionalSectorPrefixEdges, Finset.sum_filter]
  have hpoint (j : Fin m) :
      (∀ β ∈ T.support, 0 < directionalOrderedPrefix (directionalMonomialExponent ν label β) j) ↔
        (Module.finrank ℝ (K j) : ℝ) + directionalDegree (K j) P <
          2 * ∑ i ∈ directionalSectorPrefixEdges j, ν i := by
    have hm := directionalOrderedPrefix_all_monomials_iff_weakDegree T hT ν label j
    change (_ ↔ ((W j).card : ℝ) + (weakDegree (W j) T : ℝ) <
      2 * directionalOrderedPrefix ν j) at hm
    rwa [← hdim j, ← hdeg j, hsum j] at hm
  change _ ↔ ∀ j, 0 < Module.finrank ℝ (K j) →
    (Module.finrank ℝ (K j) : ℝ) + directionalDegree (K j) P <
      2 * ∑ i ∈ directionalSectorPrefixEdges j, ν i
  rw [hcost]
  constructor
  · intro h j _
    exact (hpoint j).1 (fun β hβ => h β hβ j)
  · intro h β hβ j
    apply (hpoint j).2 ?_ β hβ
    by_cases hj : 0 < Module.finrank ℝ (K j)
    · exact h j hj
    · have hK : Module.finrank ℝ (K j) = 0 := Nat.eq_zero_of_not_pos hj
      have hW : W j = ∅ := Finset.card_eq_zero.mp ((hdim j).symm.trans hK)
      have hp : 0 < ∑ i ∈ directionalSectorPrefixEdges j, ν i :=
        Finset.sum_pos (fun i _ => hν i) ⟨j, (directionalSectorPrefixEdges_mem j j).2 le_rfl⟩
      have hzero : weakDegree (∅ : Finset (Fin d)) T = 0 := by
        unfold weakDegree
        apply le_antisymm _ (Nat.zero_le _)
        exact Finset.sup_le fun β _ => by simp [weakMonomialDegree]
      rw [hK, hdeg j, hW, hzero]
      simpa only [Nat.cast_zero, zero_add] using mul_pos (by norm_num : 0 < (2 : ℝ)) hp

/-- Simultaneous-scale classification for the centered and factorized
Gaussian with actual routing. Each permutation identifies a genuine
ordered sector and keeps the original line labels in its prefix. -/
theorem directionalCenteredSchwingerCost_finite_iff_power {m d a : ℕ} {b : Fin m → ℕ}
    (A : DirectionalMomentum d →ₗ[ℝ] DirectionalMomentum a)
    (C : ∀ e, DirectionalMomentum d →ₗ[ℝ] DirectionalMomentum (b e))
    (ν : Fin m → ℝ) (P : MvPolynomial (Fin d) ℂ)
    (hν : ∀ e, 0 < ν e) (hP : P ≠ 0)
    (hinj : Function.Injective (fun k : DirectionalMomentum d => (A k, fun e => C e k))) :
    directionalCenteredSchwingerCost A C ν P < ⊤ ↔
      ∀ (σ : Equiv.Perm (Fin m)) (j : Fin m),
        let K := sourceNullFlag A (fun e => C (σ e)) (j.val + 1)
        0 < Module.finrank ℝ K →
          (Module.finrank ℝ K : ℝ) + directionalDegree K P <
            2 * ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ≤ j), ν (σ i) := by
  rw [directionalCenteredSchwingerCost_finite_iff_sectors]
  apply forall_congr'
  intro σ
  apply directionalCenteredSectorCost_finite_iff_power A (fun e => C (σ e)) (ν ∘ σ) P
    (fun i => hν (σ i)) hP
  intro x y hxy
  have hA : A x = A y := congrArg Prod.fst hxy
  have hC (i : Fin m) : C i x = C i y := by
    have he : C (σ (σ.symm i)) x = C (σ (σ.symm i)) y :=
      congrArg (fun p : DirectionalMomentum a × (∀ e, DirectionalMomentum (b (σ e))) =>
        p.2 (σ.symm i)) hxy
    rwa [σ.apply_symm_apply i] at he
  exact hinj (Prod.ext hA (funext hC))

end UV
