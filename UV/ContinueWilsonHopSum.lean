import UV.ContinueWilsonCirculation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-! A complete nonempty charged circulation at a fixed photon order.
Every allocation of the labeled photons to hops is included. Momentum
transfers may depend arbitrarily on that allocation and the hop number. -/

noncomputable section

open MeasureTheory Set Filter Finset UV.SectorPlane
open scoped Topology Matrix.Norms.L2Operator

namespace UV

variable {ι : Type*} [Fintype ι] {a n : ℕ}

def wilsonAssignedHop (u : Fin a → UnitVector OSFourSpace) (f : Fin a → Fin (n+1))
    (q : Fin (n+1) → OSFourSpace) (j : Fin (n+1)) : WilsonCirculationHop where
  marks := ((Finset.univ.filter (fun i => f i = j)).toList).map u
  transfer := q j

def wilsonAssignedTail (u : Fin a → UnitVector OSFourSpace) (f : Fin a → Fin (n+1))
    (q : Fin (n+1) → OSFourSpace) : List WilsonCirculationHop :=
  List.ofFn (fun j : Fin n => wilsonAssignedHop u f q j.succ)

theorem wilson_assigned_mark_count (u : Fin a → UnitVector OSFourSpace) (f : Fin a → Fin (n+1))
    (q : Fin (n+1) → OSFourSpace) :
    (wilsonAssignedHop u f q 0).marks.length +
      ((wilsonAssignedTail u f q).map (fun h => h.marks.length)).sum = a := by
  have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin a)) Finset.univ f
  simpa [wilsonAssignedTail,wilsonAssignedHop,List.map_ofFn,Function.comp_def,Fin.sum_ofFn,Fin.sum_univ_succ] using h

def wilsonHeadIntegralBudget (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (u : Fin a → UnitVector OSFourSpace) : ℝ :=
  ∑ s : Finset (Fin a), ∫ p, ‖wilsonSpinHopMatrix L T (s.toList.map u) p‖

theorem wilson_head_budget_nonneg (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (u : Fin a → UnitVector OSFourSpace) :
    0 ≤ wilsonHeadIntegralBudget L T u :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _

def wilsonAllocatedTraceIntegral (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (u : Fin a → UnitVector OSFourSpace)
    (f : Fin a → Fin (n+1)) (q : Fin (n+1) → OSFourSpace) : ℝ :=
  ∫ p, ‖(wilsonCirculationWord L T (wilsonAssignedHop u f q 0 :: wilsonAssignedTail u f q) p).trace‖

theorem wilson_allocated_trace_bound {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (u : Fin a → UnitVector OSFourSpace) (f : Fin a → Fin (n+1)) (q : Fin (n+1) → OSFourSpace) :
    wilsonAllocatedTraceIntegral L T u f q ≤
      (4*wilsonHeadIntegralBudget L T u*(max 1 (2*L))^a)*2^n := by
  have hh : (∫ p, ‖wilsonSpinHopMatrix L T (wilsonAssignedHop u f q 0).marks p‖) ≤ wilsonHeadIntegralBudget L T u := by
    apply Finset.single_le_sum (f := fun s : Finset (Fin a) => ∫ p, ‖wilsonSpinHopMatrix L T (s.toList.map u) p‖)
      (fun _ _ => integral_nonneg fun _ => norm_nonneg _) (Finset.mem_univ _)
  have ht := wilson_assigned_mark_count u f q
  let m := ((wilsonAssignedTail u f q).map (fun h => h.marks.length)).sum
  have hm : m ≤ a := by dsimp [m]; omega
  have hk : (2*L)^m ≤ (max 1 (2*L))^a :=
    (pow_le_pow_left₀ (by positivity) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) hm)
  have hbound := (wilson_charged_trace_absolute_bound hL T (wilsonAssignedHop u f q 0) (wilsonAssignedTail u f q)).2
  rw [wilson_circulation_cost,show (wilsonAssignedTail u f q).length = n by simp [wilsonAssignedTail]] at hbound
  apply hbound.trans
  change 4*_*(2^n*(2*L)^m) ≤ _
  have h₁ := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 4)
  have h₂ := mul_le_mul_of_nonneg_left hk (by positivity : (0:ℝ) ≤ 2^n)
  convert mul_le_mul h₁ h₂ (mul_nonneg (by positivity) (pow_nonneg (by positivity) _))
    (mul_nonneg (by norm_num) (wilson_head_budget_nonneg L T u)) using 1
  ring

/-- Summation over all positive hopping lengths and all allocations of
a fixed finite list of photon marks. This includes several photons on
the same hop. The bound is uniform in the carrier momentum shifts. -/
theorem wilson_all_allocations_summable {L lam : ℝ} (hL : 0 < L) (hlam : 0 ≤ lam) (hl : 2*lam < 1)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (u : Fin a → UnitVector OSFourSpace)
    (q : (n : ℕ) → (Fin a → Fin (n+1)) → Fin (n+1) → OSFourSpace) :
    Summable (fun n : ℕ => lam^(n+1)*∑ f : Fin a → Fin (n+1), wilsonAllocatedTraceIntegral L T u f (q n f)) := by
  let D := 4*wilsonHeadIntegralBudget L T u*(max 1 (2*L))^a
  have hn (n : ℕ) (f : Fin a → Fin (n+1)) : 0 ≤ wilsonAllocatedTraceIntegral L T u f (q n f) :=
    integral_nonneg fun _ => norm_nonneg _
  have hs := (wilson_marked_hop_summable a hlam hl).mul_left (lam*D)
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg hlam _) (Finset.sum_nonneg fun f _ => hn n f)) _ hs
  intro n
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin a → Fin (n+1)))) (fun f _ => wilson_allocated_trace_bound hL T u f (q n f))
  apply (mul_le_mul_of_nonneg_left h (pow_nonneg hlam (n+1))).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_pow,Nat.cast_add,Nat.cast_one,mul_pow,pow_succ]
  dsimp [D]
  ring

end UV
