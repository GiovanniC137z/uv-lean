import UV.ContinueNetworkPrefixSubsets
import UV.ContinueNetworkRayTranslation
import UV.ContinueNetworkPrecisionChart

/-! Identifying every physical routed kernel K_S with the sorted
Schwinger flag. The same subspace carries the actual ray degree. -/

noncomputable section

namespace UV

open scoped BigOperators
open ContinueNetworkPrecision

variable {m d : ℕ} {b : Fin m → ℕ}

/-- Actual weak subspace of the Gaussian precision and the line
factors whose labels lie outside S. -/
def directionalPowerSubspace
    (Q : DirectionalMomentum d →L[ℝ] DirectionalMomentum d)
    (C : ∀ e, DirectionalMomentum d →L[ℝ] DirectionalMomentum (b e)) (S : Finset (Fin m)) :
    Submodule ℝ (DirectionalMomentum d) where
  carrier := {k | Q k = 0 ∧ ∀ e ∉ S, C e k = 0}
  zero_mem' := ⟨map_zero _,fun _ _ => map_zero _⟩
  add_mem' := by
    rintro k p ⟨hQ,hC⟩ ⟨hQ',hC'⟩
    exact ⟨by rw [map_add,hQ,hQ',add_zero],fun e he => by rw [map_add,hC e he,hC' e he,add_zero]⟩
  smul_mem' := by
    rintro r k ⟨hQ,hC⟩
    exact ⟨by rw [map_smul,hQ,smul_zero],fun e he => by rw [map_smul,hC e he,smul_zero]⟩

/-- Numerical condition on each nonzero weak subspace in the manuscript,
using the degree of the actual polynomial restrictions. -/
def directionalPowerCondition
    (Q : DirectionalMomentum d →L[ℝ] DirectionalMomentum d)
    (C : ∀ e, DirectionalMomentum d →L[ℝ] DirectionalMomentum (b e))
    (ν : Fin m → ℝ) (P : MvPolynomial (Fin d) ℂ) : Prop :=
  ∀ S : Finset (Fin m),
    let K := directionalPowerSubspace Q C S
    0 < Module.finrank ℝ K →
      (Module.finrank ℝ K : ℝ) + directionalDegree K P < 2 * ∑ e ∈ S, ν e

theorem directional_power_condition_translate
    (Q : DirectionalMomentum d →L[ℝ] DirectionalMomentum d)
    (C : ∀ e, DirectionalMomentum d →L[ℝ] DirectionalMomentum (b e))
    (ν : Fin m → ℝ) (P : MvPolynomial (Fin d) ℂ) (v : DirectionalMomentum d) :
    directionalPowerCondition Q C ν (translateDirectionalPolynomial v P) ↔
      directionalPowerCondition Q C ν P := by
  unfold directionalPowerCondition
  simp only [directionalDegree_translate]

theorem directional_power_subspace_empty
    (Q : DirectionalMomentum d →L[ℝ] DirectionalMomentum d)
    (C : ∀ e, DirectionalMomentum d →L[ℝ] DirectionalMomentum (b e))
    (hvis : ∀ k, Q k = 0 → (∀ e, C e k = 0) → k = 0) :
    directionalPowerSubspace Q C ∅ = ⊥ := by
  apply le_antisymm _ bot_le
  intro k hk
  change Q k = 0 ∧ ∀ e ∉ (∅ : Finset (Fin m)), C e k = 0 at hk
  change k = 0
  exact hvis k hk.1 (fun e => hk.2 e (Finset.notMem_empty e))

/-- Subspace identities are independent of which Schwinger ordering
realizes a fixed initial set of routes. -/
theorem directional_power_subspace_prefix
    (Q : DirectionalMomentum d →L[ℝ] DirectionalMomentum d)
    (C : ∀ e, DirectionalMomentum d →L[ℝ] DirectionalMomentum (b e))
    {a : ℕ} (A : DirectionalMomentum d →ₗ[ℝ] DirectionalMomentum a)
    (hker : ∀ k, A k = 0 ↔ Q k = 0) (σ : Equiv.Perm (Fin m)) (j : Fin m) :
    sourceNullFlag A (fun e => (C (σ e)).toLinearMap) (j.val+1) =
      directionalPowerSubspace Q C ((Finset.univ.filter (fun i : Fin m => i ≤ j)).map σ.toEmbedding) := by
  ext k
  change (A k = 0 ∧ ∀ i : Fin m, j.val+1 ≤ i.val → C (σ i) k = 0) ↔
    (Q k = 0 ∧ ∀ e ∉ (Finset.univ.filter (fun i : Fin m => i ≤ j)).map σ.toEmbedding, C e k = 0)
  rw [hker]
  constructor
  · rintro ⟨hQ,hC⟩
    refine ⟨hQ,fun e he => ?_⟩
    have hb : ¬ σ.symm e ≤ j := fun h => he ((route_prefix_mem_iff σ j e).mpr h)
    have hval : j.val+1 ≤ (σ.symm e).val := by
      have hl : j < σ.symm e := lt_of_not_ge hb
      exact (show j.val < (σ.symm e).val from hl)
    exact (congrArg (fun i => C i k = 0) (σ.apply_symm_apply e)).mp (hC (σ.symm e) hval)
  · rintro ⟨hQ,hC⟩
    refine ⟨hQ,fun i hi => hC (σ i) ?_⟩
    rw [route_prefix_mem_iff,Equiv.symm_apply_apply]
    intro he
    have hb : i.val ≤ j.val := he
    omega

theorem directional_power_prefix_sum (ν : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) (j : Fin m) :
    (∑ e ∈ (Finset.univ.filter (fun i : Fin m => i ≤ j)).map σ.toEmbedding, ν e) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ≤ j), ν (σ i) := by
  rw [Finset.sum_map]
  rfl

end UV
