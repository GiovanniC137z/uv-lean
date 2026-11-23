import UV.ContinueAngularMassInfinite
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Order.Compact

/-! Compactness in the coordinate topology gives an actual maximizing angular
state. The summable off-diagonal coefficients control all tails uniformly. -/

noncomputable section
open Finset Set Filter
open scoped Topology
namespace UV

def angularUnitBall : Set (ℕ → ℝ) := {z | ∀ n, angularFiniteNorm n z ≤ 1}

theorem angular_unit_ball_coord_bound {z : ℕ → ℝ} (hz : z ∈ angularUnitBall) (j : ℕ) : |z j| ≤ 1 := by
  have hs := single_le_sum (s := range (j+1)) (f := fun k => (z k)^2)
    (fun k _ => sq_nonneg (z k)) (mem_range.mpr (Nat.lt_succ_self j))
  have h := hs.trans (hz j)
  nlinarith [sq_abs (z j),abs_nonneg (z j)]

theorem angular_unit_ball_compact : IsCompact angularUnitBall := by
  have hc : IsClosed angularUnitBall := by
    change IsClosed {z : ℕ → ℝ | ∀ n, angularFiniteNorm n z ≤ 1}
    rw [setOf_forall]
    apply isClosed_iInter
    intro n
    apply isClosed_le _ continuous_const
    exact continuous_finset_sum _ fun j _ => (continuous_apply j).pow 2
  apply (isCompact_univ_pi (fun _ : ℕ => isCompact_Icc (a := (-1:ℝ)) (b := 1))).of_isClosed_subset hc
  exact fun z hz j _ => abs_le.mp (angular_unit_ball_coord_bound hz j)

theorem angular_edge_summable : Summable (fun j => 2*angularJacobiEdge j) := by
  have h (n : ℕ) : ∑ j ∈ range n, 2*angularJacobiEdge j = 1 - 1/((n:ℝ)+1) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [sum_range_succ,ih]
      simp only [angularJacobiEdge,Nat.cast_succ]
      field_simp
      ring
  apply summable_of_sum_range_le (c := 1) (fun j => by unfold angularJacobiEdge; positivity)
  intro n
  rw [h]
  exact sub_le_self _ (by positivity)

theorem angular_form_continuous_on_ball : ContinuousOn angularInfiniteForm angularUnitBall := by
  apply continuousOn_tsum (u := fun j => 2*angularJacobiEdge j)
  · intro j
    exact ((continuous_const.mul (continuous_apply j)).mul (continuous_apply (j+1))).continuousOn
  · exact angular_edge_summable
  · intro j z hz
    have hd : 0 ≤ 2*angularJacobiEdge j := by unfold angularJacobiEdge; positivity
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg hd]
    calc _ ≤ (2*angularJacobiEdge j)*1*1 := by
           gcongr
           · exact angular_unit_ball_coord_bound hz j
           · exact angular_unit_ball_coord_bound hz (j+1)
         _ = _ := by ring

theorem angular_form_has_maximum :
    ∃ z ∈ angularUnitBall, ∀ y ∈ angularUnitBall, angularInfiniteForm y ≤ angularInfiniteForm z := by
  have h0 : (fun _ : ℕ => (0:ℝ)) ∈ angularUnitBall := by intro n; simp [angularFiniteNorm]
  exact angular_unit_ball_compact.exists_isMaxOn ⟨_,h0⟩ angular_form_continuous_on_ball

end UV
