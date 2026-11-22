import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The relativistic energy inequality for finite blocked configurations.
The Hamiltonian form comparison that produces this configuration is a
separate obligation. -/

namespace UV.RevisionPairThreshold

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E]

noncomputable def massiveEnergy (m : ℝ) (k : E) : ℝ :=
  Real.sqrt (‖k‖ ^ 2 + m ^ 2)

theorem blocked_energy_sum {I : Type*} (B : Finset I) (k : I → E) (m : ℝ) :
    Real.sqrt (‖∑ i ∈ B, k i‖ ^ 2 + (m * B.card) ^ 2) ≤
      ∑ i ∈ B, massiveEnergy m (k i) := by
  let v (i : I) : WithLp 2 (E × ℝ) := WithLp.toLp 2 (k i, m)
  have hf : (∑ i ∈ B, v i).fst = ∑ i ∈ B, k i := by
    induction B using Finset.cons_induction with
    | empty => rfl
    | cons i B hi ih =>
      rw [Finset.sum_cons, Finset.sum_cons, WithLp.add_fst, ih]
      rfl
  have hs : (∑ i ∈ B, v i).snd = m * B.card := by
    clear hf
    induction B using Finset.cons_induction with
    | empty => simp
    | cons i B hi ih =>
      rw [Finset.sum_cons, WithLp.add_snd, ih, Finset.card_cons, Nat.cast_add, Nat.cast_one]
      change m + m * (B.card : ℝ) = m * ((B.card : ℝ) + 1)
      ring
  have h := norm_sum_le B v
  rw [WithLp.prod_norm_eq_of_L2, hf, hs, Real.norm_eq_abs, sq_abs] at h
  simpa only [v, massiveEnergy, WithLp.prod_norm_eq_of_L2, WithLp.toLp_fst,
    WithLp.toLp_snd, Real.norm_eq_abs, sq_abs] using h

/-- Two or more blocked slots have a pair threshold with the exact free mass. -/
theorem blocked_pair_threshold {I : Type*} (B : Finset I) (k : I → E) {m : ℝ}
    (hm : 0 ≤ m) (hB : 2 ≤ B.card) :
    Real.sqrt (‖∑ i ∈ B, k i‖ ^ 2 + 4 * m ^ 2) ≤
      ∑ i ∈ B, massiveEnergy m (k i) := by
  refine le_trans (Real.sqrt_le_sqrt ?_) (blocked_energy_sum B k m)
  have hcard : (2 : ℝ) ≤ B.card := by exact_mod_cast hB
  have h := mul_le_mul_of_nonneg_left hcard hm
  have hs := (sq_le_sq₀ (by positivity) (by positivity)).2 h
  nlinarith

/-- Adding free photon momenta and energies preserves the forward-cone bound. -/
theorem add_free_photons_preserves_forward_cone {I : Type*}
    (s : Finset I) (p : I → E) (e : I → ℝ) (P : E) (energy : ℝ)
    (hP : ‖P‖ ≤ energy) (he : ∀ i ∈ s, ‖p i‖ ≤ e i) :
    ‖P + ∑ i ∈ s, p i‖ ≤ energy + ∑ i ∈ s, e i :=
  (norm_add_le _ _).trans (add_le_add hP ((norm_sum_le _ _).trans (Finset.sum_le_sum he)))

end UV.RevisionPairThreshold
