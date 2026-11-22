import UV.NextOpeningCutoff
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! The oscillator position as a densely defined partial linear map.
Both Jacobi cutoffs and vacuum powers use its literal coefficients. -/

noncomputable section

namespace UV

open Filter
open scoped Topology Nat ComplexInnerProductSpace ENNReal

def openingNumberCore : Submodule ℂ OpeningFock where
  carrier := {v | ∃ c : ℕ, ∀ n > c, v n = 0}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro v w ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨max c d, fun n hn => by
      simp [hc n (lt_of_le_of_lt (le_max_left c d) hn),
        hd n (lt_of_le_of_lt (le_max_right c d) hn)]⟩
  smul_mem' := by
    rintro z v ⟨c, hc⟩
    exact ⟨c, fun n hn => by simp [lp.coeFn_smul, hc n hn]⟩

private theorem opening.single_mem_core (n : ℕ) (z : ℂ) :
    lp.single 2 n z ∈ openingNumberCore :=
  ⟨n, fun k hk => lp.single_apply_ne (E := fun _ : ℕ => ℂ) 2 n z (by omega)⟩

theorem openingNumberCore_dense : Dense (openingNumberCore : Set OpeningFock) := by
  intro v
  refine mem_closure_of_tendsto (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) v) ?_
  exact Eventually.of_forall fun s => openingNumberCore.sum_mem fun n _ =>
    opening.single_mem_core n (v n)

private def opening.coreSupport (v : openingNumberCore) : ℕ := Classical.choose v.property

private theorem opening.coreSupport_zero (v : openingNumberCore) (n : ℕ)
    (hn : opening.coreSupport v < n) : (v : OpeningFock) n = 0 :=
  Classical.choose_spec v.property n hn

private def opening.coreJacobi (v : openingNumberCore) : OpeningFock :=
  openingJacobiCutoff (opening.coreSupport v + 1) v

private theorem opening.coreJacobi_apply (v : openingNumberCore) (n : ℕ) :
    opening.coreJacobi v n = openingJacobi v n := by
  rw [opening.coreJacobi, openingJacobiCutoff_apply_of_supported]
  · by_cases h : n ≤ opening.coreSupport v + 1
    · rw [if_pos h]
    · rw [if_neg h, openingJacobi_support (opening.coreSupport_zero v) _ (by omega)]
  · exact fun i hi => opening.coreSupport_zero v i (by omega)

def openingJacobiOnCore : OpeningFock →ₗ.[ℂ] OpeningFock where
  domain := openingNumberCore
  toFun :=
    { toFun := opening.coreJacobi
      map_add' := by
        intro v w
        ext n
        simp only [lp.coeFn_add, Pi.add_apply, opening.coreJacobi_apply,
          Submodule.coe_add, openingJacobi]
        ring
      map_smul' := by
        intro z v
        ext n
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, opening.coreJacobi_apply,
          Submodule.coe_smul, openingJacobi, RingHom.id_apply]
        ring }

theorem openingJacobiOnCore_apply (v : openingJacobiOnCore.domain) (n : ℕ) :
    openingJacobiOnCore v n = openingJacobi v n :=
  opening.coreJacobi_apply v n

theorem openingJacobiOnCore_maps_core (v : openingJacobiOnCore.domain) :
    openingJacobiOnCore v ∈ openingJacobiOnCore.domain := by
  use opening.coreSupport v + 1
  intro n hn
  rw [openingJacobiOnCore_apply, openingJacobi_support (opening.coreSupport_zero v) _ hn]

private theorem opening.cutoff_eq_core (v : openingJacobiOnCore.domain) (c : ℕ)
    (hc : opening.coreSupport v + 1 ≤ c) :
    openingJacobiCutoff c v = openingJacobiOnCore v := by
  ext n
  rw [openingJacobiCutoff_apply_of_supported _ _ (fun i hi => opening.coreSupport_zero v i (by omega)),
    openingJacobiOnCore_apply]
  by_cases h : n ≤ c
  · rw [if_pos h]
  · rw [if_neg h, openingJacobi_support (opening.coreSupport_zero v) _ (by omega)]

/-- The position rule is a symmetric operator on its dense number core. -/
theorem openingJacobiOnCore_symmetric : openingJacobiOnCore.IsFormalAdjoint openingJacobiOnCore := by
  intro v w
  let c := max (opening.coreSupport v) (opening.coreSupport w) + 1
  have hv : opening.coreSupport v + 1 ≤ c := Nat.succ_le_succ (le_max_left _ _)
  have hw : opening.coreSupport w + 1 ≤ c := Nat.succ_le_succ (le_max_right _ _)
  rw [← opening.cutoff_eq_core v c hv, ← opening.cutoff_eq_core w c hw]
  exact (ContinuousLinearMap.eq_adjoint_iff (openingJacobiCutoff c)
    (openingJacobiCutoff c)).1 (openingJacobiCutoff_selfAdjoint c).adjoint_eq.symm v w

/-- The actual position field includes the oscillator frequency and preserves
the finite-number domain. -/
def openingPositionOnCore (ω : ℝ) : OpeningFock →ₗ.[ℂ] OpeningFock where
  domain := openingNumberCore
  toFun := ((Real.sqrt (2 * ω) : ℂ)⁻¹) • openingJacobiOnCore.toFun

theorem openingPositionOnCore_apply (ω : ℝ) (v : (openingPositionOnCore ω).domain) (n : ℕ) :
    openingPositionOnCore ω v n =
      (Real.sqrt (2 * ω) : ℂ)⁻¹ * openingJacobi v n := by
  change (((Real.sqrt (2 * ω) : ℂ)⁻¹) • openingJacobiOnCore v) n = _
  simp [lp.coeFn_smul, openingJacobiOnCore_apply]

theorem openingPositionOnCore_symmetric (ω : ℝ) :
    (openingPositionOnCore ω).IsFormalAdjoint (openingPositionOnCore ω) := by
  intro v w
  change inner ℂ (((Real.sqrt (2 * ω) : ℂ)⁻¹) • openingJacobiOnCore v) (w : OpeningFock) =
    inner ℂ (v : OpeningFock) (((Real.sqrt (2 * ω) : ℂ)⁻¹) • openingJacobiOnCore w)
  rw [inner_smul_left, inner_smul_right, map_inv₀, Complex.conj_ofReal,
    openingJacobiOnCore_symmetric v w]

theorem openingVacuumPower_mem_core (k : ℕ) :
    openingVacuumPower k ∈ openingJacobiOnCore.domain :=
  ⟨k, openingVacuumPowerSeq_support k⟩

theorem openingJacobiOnCore_vacuumPower (k : ℕ) :
    openingJacobiOnCore ⟨openingVacuumPower k, openingVacuumPower_mem_core k⟩ =
      openingVacuumPower (k + 1) := by
  ext n
  rw [openingJacobiOnCore_apply]
  rfl

/-- The actual frequency-scaled iterates of the vacuum, as vectors in
the fixed finite-number domain. -/
def openingPositionVacuumPower (ω : ℝ) (k : ℕ) : (openingPositionOnCore ω).domain :=
  ⟨((Real.sqrt (2 * ω) : ℂ)⁻¹) ^ k • openingVacuumPower k,
    openingNumberCore.smul_mem _ (openingVacuumPower_mem_core k)⟩

theorem openingPositionVacuumPower_zero (ω : ℝ) :
    (openingPositionVacuumPower ω 0 : OpeningFock) = openingNumberState 0 := by
  simp [openingPositionVacuumPower]

theorem openingPositionVacuumPower_succ (ω : ℝ) (k : ℕ) :
    openingPositionOnCore ω (openingPositionVacuumPower ω k) =
      (openingPositionVacuumPower ω (k + 1) : OpeningFock) := by
  change (Real.sqrt (2 * ω) : ℂ)⁻¹ •
    openingJacobiOnCore ((((Real.sqrt (2 * ω) : ℂ)⁻¹) ^ k) •
      ⟨openingVacuumPower k, openingVacuumPower_mem_core k⟩) =
      ((Real.sqrt (2 * ω) : ℂ)⁻¹) ^ (k + 1) • openingVacuumPower (k + 1)
  rw [LinearPMap.map_smul, openingJacobiOnCore_vacuumPower, smul_smul, pow_succ']

/-- The spectral phase on the cut uses the specified real displacement
and the actual position powers. -/
theorem openingPositionVacuumExponential_hasSum (ω ξ : ℝ) :
    HasSum (fun k : ℕ => (((ξ : ℂ) * Complex.I) ^ k / (k ! : ℂ)) •
      (openingPositionVacuumPower ω k : OpeningFock))
      (openingCoherentVector (((ξ / Real.sqrt (2 * ω) : ℝ) : ℂ) * Complex.I)) := by
  rw [← openingVacuumTaylor_on_cut]
  convert openingVacuumTaylor_hasSum (((ξ / Real.sqrt (2 * ω) : ℝ) : ℂ) * Complex.I) using 1
  funext k
  change _ • (((Real.sqrt (2 * ω) : ℂ)⁻¹) ^ k • openingVacuumPower k) =
    _ • openingVacuumPower k
  rw [smul_smul]
  congr 1
  push_cast
  rw [mul_pow, mul_pow, div_pow, inv_pow]
  ring

end UV
