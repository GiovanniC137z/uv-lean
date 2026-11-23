import UV.ContinueNetworkPowerSubspaces
import UV.ContinueNetworkPositiveFactor
import UV.ContinueNetworkOrderedFlags

/-! Absolute integrability of the literal directional model on the
intrinsic Euclidean loop coordinates, with all positive real powers,
the actual complex polynomial, and the routed weak subspaces. -/

noncomputable section

namespace UV

open MeasureTheory
open scoped InnerProductSpace BigOperators ENNReal
open ContinueNetworkPrecision

variable {m d : ℕ} {b : Fin m → ℕ}

private theorem centered_schwinger_cost_eq
    (Q : DirectionalMomentum d →L[ℝ] DirectionalMomentum d)
    (A : DirectionalMomentum d →L[ℝ] DirectionalMomentum d)
    (C : ∀ e, DirectionalMomentum d →L[ℝ] DirectionalMomentum (b e))
    (ν : Fin m → ℝ) (P : MvPolynomial (Fin d) ℂ)
    (hQ : ∀ x, ‖A x‖^2 = inner ℝ x (Q x)) :
    directionalSchwingerCost Q 0 C (fun _ => 0) ν P =
      directionalCenteredSchwingerCost A.toLinearMap (fun e => (C e).toLinearMap) ν P := by
  unfold directionalSchwingerCost directionalCenteredSchwingerCost directionalOrderedDensity
  apply lintegral_congr
  intro τ
  congr 1
  apply lintegral_congr
  intro k
  unfold directionalSchwingerGaussian sourcePrecision
  simp only [inner_zero_left,add_zero,ContinuousLinearMap.coe_coe,hQ]
  rw [neg_add,sub_eq_add_neg]

private theorem directional_model_power_iff_centered_zero
    (Q : DirectionalMomentum d →L[ℝ] DirectionalMomentum d)
    (C : ∀ e, DirectionalMomentum d →L[ℝ] DirectionalMomentum (b e))
    (ν : Fin m → ℝ) (hν : ∀ e, 0 < ν e) (P : MvPolynomial (Fin d) ℂ) (hP : P ≠ 0)
    (hSym : ∀ k k', inner ℝ k (Q k') = inner ℝ k' (Q k))
    (hPSD : ∀ k, 0 ≤ inner ℝ k (Q k))
    (hvis : ∀ k, Q k = 0 → (∀ e, C e k = 0) → k = 0) :
    Integrable (directionalAbsoluteModel Q 0 C (fun _ => 0) ν P) ↔ directionalPowerCondition Q C ν P := by
  obtain ⟨A,_,_,hQ,hker⟩ := directionalQuadratic_positive_factor Q hSym hPSD
  have hinj : Function.Injective
      (fun k : DirectionalMomentum d => (A.toLinearMap k, fun e => (C e).toLinearMap k)) := by
    intro k l h
    have he : A k = A l := congrArg Prod.fst h
    have hC (e : Fin m) : C e k = C e l := congrFun (congrArg Prod.snd h) e
    have hA : Q (k-l) = 0 := (hker (k-l)).mp (by rw [map_sub,he,sub_self])
    exact sub_eq_zero.mp (hvis (k-l) hA (fun e => by rw [map_sub,hC e,sub_self]))
  rw [directionalAbsoluteModel_integrable_iff_schwinger Q 0 C _ ν hν P,
    centered_schwinger_cost_eq Q A C ν P hQ,
    directionalCenteredSchwingerCost_finite_iff_power A.toLinearMap (fun e => (C e).toLinearMap)
      ν P hν hP hinj]
  unfold directionalPowerCondition
  constructor
  · intro h S
    dsimp only
    intro hS
    by_cases hn : S.Nonempty
    · obtain ⟨σ,j,_,he⟩ := route_subset_is_nonempty_prefix S hn
      have ht := h σ j
      dsimp only at ht
      rw [directional_power_subspace_prefix Q C A.toLinearMap hker σ j,
        ← directional_power_prefix_sum ν σ j,he] at ht
      exact ht hS
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      rw [he, directional_power_subspace_empty Q C hvis,finrank_bot] at hS
      exact (Nat.lt_irrefl _ hS).elim
  · intro h σ j
    dsimp only
    rw [directional_power_subspace_prefix Q C A.toLinearMap hker σ j, ← directional_power_prefix_sum ν σ j]
    exact h _

private theorem directional_model_power_of_admissible
    (Q : DirectionalMomentum d →L[ℝ] DirectionalMomentum d) (h : DirectionalMomentum d)
    (C : ∀ e, DirectionalMomentum d →L[ℝ] DirectionalMomentum (b e)) (p : ∀ e, DirectionalMomentum (b e))
    (ν : Fin m → ℝ) (hν : ∀ e, 0 < ν e) (P : MvPolynomial (Fin d) ℂ) (hP : P ≠ 0)
    (hSym : ∀ k k', inner ℝ k (Q k') = inner ℝ k' (Q k))
    (hPSD : ∀ k, 0 ≤ inner ℝ k (Q k))
    (horth : ∀ k, Q k = 0 → inner ℝ h k = 0)
    (hvis : ∀ k, Q k = 0 → (∀ e, C e k = 0) → k = 0) :
    Integrable (directionalAbsoluteModel Q h C p ν P) ↔ directionalPowerCondition Q C ν P := by
  obtain ⟨v,hv⟩ := directional_kernel_drift_center Q h hSym horth
  let P' := translateDirectionalPolynomial v P
  let p' (e : Fin m) := C e v + p e
  calc
    _ ↔ Integrable (directionalAbsoluteModel Q 0 C p' ν P') := by
      rw [hv]
      exact directional_model_integrable_iff_centered Q v C p ν P hSym
    _ ↔ Integrable (directionalAbsoluteModel Q 0 C (fun _ => 0) ν P') :=
      directional_model_integrable_iff_unshifted Q 0 C p' ν (fun e => (hν e).le) P'
    _ ↔ directionalPowerCondition Q C ν P' := directional_model_power_iff_centered_zero
      Q C ν hν P' (translate_directional_polynomial_nonzero hP v) hSym hPSD hvis
    _ ↔ _ := directional_power_condition_translate Q C ν P v

/-- Full necessary and sufficient power count for the literal
nonzero-polynomial directional absolute integrand. The dimension is
positive and both the source precision and momentum routes use their
original Euclidean inner products. -/
theorem directionalAbsoluteModel_integrable_iff_directional_power
    (Q : DirectionalMomentum (d+1) →L[ℝ] DirectionalMomentum (d+1))
    (h : DirectionalMomentum (d+1))
    (C : ∀ e, DirectionalMomentum (d+1) →L[ℝ] DirectionalMomentum (b e))
    (p : ∀ e, DirectionalMomentum (b e)) (ν : Fin m → ℝ) (hν : ∀ e, 0 < ν e)
    (P : MvPolynomial (Fin (d+1)) ℂ) (hP : P ≠ 0)
    (hSym : ∀ k k', inner ℝ k (Q k') = inner ℝ k' (Q k)) :
    Integrable (directionalAbsoluteModel Q h C p ν P) ↔
      (∀ k, 0 ≤ inner ℝ k (Q k)) ∧
      (∀ k, Q k = 0 → inner ℝ h k = 0) ∧
      (∀ k, Q k = 0 → (∀ e, C e k = 0) → k = 0) ∧
      directionalPowerCondition Q C ν P := by
  constructor
  · intro H
    obtain ⟨hPSD,horth,hvis⟩ := directionalAbsoluteModel_sign_drift_visibility
      Q h C p ν (fun e => (hν e).le) P hSym hP H
    exact ⟨hPSD,horth,hvis,(directional_model_power_of_admissible
      Q h C p ν hν P hP hSym hPSD horth hvis).mp H⟩
  · rintro ⟨hPSD,horth,hvis,H⟩
    exact (directional_model_power_of_admissible Q h C p ν hν P hP hSym hPSD horth hvis).mpr H

theorem directionalAbsoluteModel_not_integrable_at_power_equality
    (Q : DirectionalMomentum (d+1) →L[ℝ] DirectionalMomentum (d+1))
    (h : DirectionalMomentum (d+1))
    (C : ∀ e, DirectionalMomentum (d+1) →L[ℝ] DirectionalMomentum (b e))
    (p : ∀ e, DirectionalMomentum (b e)) (ν : Fin m → ℝ) (hν : ∀ e, 0 < ν e)
    (P : MvPolynomial (Fin (d+1)) ℂ) (hP : P ≠ 0)
    (hSym : ∀ k k', inner ℝ k (Q k') = inner ℝ k' (Q k))
    (S : Finset (Fin m)) (hS : 0 < Module.finrank ℝ (directionalPowerSubspace Q C S))
    (he : (Module.finrank ℝ (directionalPowerSubspace Q C S) : ℝ) +
      directionalDegree (directionalPowerSubspace Q C S) P = 2 * ∑ e ∈ S, ν e) :
    ¬ Integrable (directionalAbsoluteModel Q h C p ν P) := by
  intro H
  have H' := ((directionalAbsoluteModel_integrable_iff_directional_power Q h C p ν hν P hP hSym).mp H).2.2.2 S hS
  dsimp only at H'
  rw [he] at H'
  exact (lt_irrefl _ H').elim

end UV
