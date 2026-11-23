import UV.ContinueAngularMassBracket
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic

/-! Absolute convergence and the variational upper estimate on square-summable
angular states, with the rational pivots appearing in the ten-row benchmark. -/

noncomputable section
open Finset Set Filter
open scoped Topology
namespace UV

def angularInfiniteForm (z : ℕ → ℝ) : ℝ := ∑' j, 2*angularJacobiEdge j*z j*z (j+1)

theorem angular_infinite_form_summable {z : ℕ → ℝ} (hz : Summable (fun j => (z j)^2)) :
    Summable (fun j => 2*angularJacobiEdge j*z j*z (j+1)) := by
  have hs : Summable (fun j => (z (j+1))^2) := (summable_nat_add_iff 1).2 hz
  apply (hz.add hs).of_norm_bounded
  intro j
  have hd : 0 ≤ 2*angularJacobiEdge j := by unfold angularJacobiEdge; positivity
  have hu : 2*angularJacobiEdge j ≤ 1 := by
    unfold angularJacobiEdge
    have hj : (0:ℝ) ≤ j := Nat.cast_nonneg _
    field_simp
    nlinarith [sq_nonneg (j:ℝ)]
  rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg hd]
  change _ ≤ (z j)^2 + (z (j+1))^2
  calc _ ≤ 1 * |z j| * |z (j+1)| := by gcongr
       _ ≤ _ := by nlinarith [sq_nonneg (|z j|-|z (j+1)|),sq_abs (z j),sq_abs (z (j+1)),
                               abs_nonneg (z j), mul_nonneg (abs_nonneg (z j)) (abs_nonneg (z (j+1)))]

theorem angular_infinite_rayleigh_upper {z : ℕ → ℝ} (hz : Summable (fun j => (z j)^2)) :
    angularInfiniteForm z ≤ (1:ℝ)/3.789841*(∑' j,(z j)^2) := by
  have hf := (angular_infinite_form_summable hz).hasSum.tendsto_sum_nat
  have hn := hz.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  exact le_of_tendsto_of_tendsto' hf (tendsto_const_nhds.mul hn) (fun n => angular_finite_rayleigh_upper n z)

def angularJacobiPivot (x : ℝ) : ℕ → ℝ
  | 0 => x
  | j+1 => x-(angularJacobiEdge j)^2/angularJacobiPivot x j

set_option maxRecDepth 5000 in
theorem angular_ten_row_certificate :
    angularJacobiPivot (1/3.78985) 4 < 0 ∧
    (∀ j < 10, 0 < angularJacobiPivot (1/3.78984) j) ∧
    0.24 < angularJacobiPivot (1/3.78984) 9 -
      angularJacobiEdge 9^2 / (1/3.78984 - 2*angularJacobiEdge 10) := by
  refine ⟨?_,?_,?_⟩
  · norm_num [angularJacobiPivot,angularJacobiEdge]
  · intro j hj
    interval_cases j <;> norm_num [angularJacobiPivot,angularJacobiEdge]
  · norm_num [angularJacobiPivot,angularJacobiEdge]

end UV
