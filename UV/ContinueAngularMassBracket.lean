import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Intervals

/-! The dimensionless zonal Jacobi matrix on the unit-speed S³ branch.
An exact rational weighted row estimate controls all finite sections at
once. A five-coordinate trial vector gives the opposite strict bound. -/

noncomputable section
open Finset Set
namespace UV

def angularJacobiEdge (j : ℕ) : ℝ := 1 / (2*((j:ℝ)+1)*(j+2))

private def angularRowWeight : ℕ → ℝ
  | 0 => 10000000000
  | 1 => 10554526929
  | 2 => 3419411608
  | 3 => 545109282
  | 4 => 54351249
  | _ => 42813659

private theorem angularRowWeight_pos (j : ℕ) : 0 < angularRowWeight j := by
  by_cases h : j < 5
  · interval_cases j <;> norm_num [angularRowWeight]
  · obtain ⟨k,rfl⟩ : ∃ k, j=k+5 := ⟨j-5,by omega⟩
    unfold angularRowWeight; split <;> norm_num

def angularFiniteNorm (n : ℕ) (z : ℕ → ℝ) : ℝ := ∑ j ∈ range (n+1), (z j)^2

def angularFiniteForm (n : ℕ) (z : ℕ → ℝ) : ℝ := ∑ j ∈ range n, 2*angularJacobiEdge j*z j*z (j+1)

private def angularOut (j : ℕ) := angularJacobiEdge j*angularRowWeight (j+1)/angularRowWeight j
private def angularIn : ℕ → ℝ
  | 0 => 0
  | j+1 => angularJacobiEdge j*angularRowWeight j/angularRowWeight (j+1)

private theorem angular_weighted_edge (j : ℕ) (x y : ℝ) :
    2*angularJacobiEdge j*x*y ≤ angularOut j*x^2+angularIn (j+1)*y^2 := by
  let a := angularRowWeight j
  let b := angularRowWeight (j+1)
  have ha : 0 < a := angularRowWeight_pos _
  have hb : 0 < b := angularRowWeight_pos _
  have hd : 0 ≤ angularJacobiEdge j := by unfold angularJacobiEdge; positivity
  change 2*angularJacobiEdge j*x*y ≤ angularJacobiEdge j*b/a*x^2+angularJacobiEdge j*a/b*y^2
  field_simp
  nlinarith only [mul_nonneg hd (sq_nonneg (b*x-a*y))]

private theorem angular_row_envelope (j : ℕ) : angularIn j+angularOut j ≤ (1:ℝ)/3.789841 := by
  by_cases h : j < 6
  · interval_cases j <;> norm_num [angularIn,angularOut,angularRowWeight,angularJacobiEdge]
  · obtain ⟨k,rfl⟩ : ∃ k, j=k+6 := ⟨j-6,by omega⟩
    simp only [angularIn,angularOut,angularRowWeight,angularJacobiEdge,Nat.cast_add,Nat.cast_ofNat]
    have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
    norm_num
    field_simp
    rw [←sub_nonneg]
    ring_nf
    positivity

/-- The upper bound is uniform in the truncation size and the state. -/
theorem angular_finite_rayleigh_upper (n : ℕ) (z : ℕ → ℝ) :
    angularFiniteForm n z ≤ (1:ℝ)/3.789841*angularFiniteNorm n z := by
  have q := Finset.sum_le_sum (s := range n) (fun j _ => angular_weighted_edge j (z j) (z (j+1)))
  unfold angularFiniteForm angularFiniteNorm
  apply q.trans
  rw [Finset.sum_add_distrib]
  have hs : (∑ j ∈ range (n+1),angularIn j*(z j)^2) = ∑ j ∈ range n,angularIn (j+1)*(z (j+1))^2 := by
    rw [sum_range_succ']; simp [angularIn]
  rw [←hs]
  have hz : 0 ≤ angularOut n*(z n)^2 := by
    exact mul_nonneg (div_nonneg (mul_nonneg (by unfold angularJacobiEdge; positivity) (angularRowWeight_pos _).le) (angularRowWeight_pos _).le) (sq_nonneg _)
  calc
    _ ≤ (∑ j ∈ range (n+1),angularOut j*(z j)^2) + ∑ j ∈ range (n+1),angularIn j*(z j)^2 := by
      rw [sum_range_succ (fun j => angularOut j*(z j)^2)]; linarith
    _ = ∑ j ∈ range (n+1),(angularIn j+angularOut j)*(z j)^2 := by simp_rw [add_mul]; rw [sum_add_distrib,add_comm]
    _ ≤ _ := by rw [Finset.mul_sum]; exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (angular_row_envelope j) (sq_nonneg _)

def angularZonalEdge : ℝ := sSup {r : ℝ | ∃ (n : ℕ) (z : ℕ → ℝ), 0 < angularFiniteNorm n z ∧ r=angularFiniteForm n z/angularFiniteNorm n z}

theorem angular_zonal_mass_bracket : (3.78984:ℝ) < 1/angularZonalEdge ∧ 1/angularZonalEdge < 3.78985 := by
  let R := {r : ℝ | ∃ (n : ℕ) (z : ℕ → ℝ), 0 < angularFiniteNorm n z ∧ r=angularFiniteForm n z/angularFiniteNorm n z}
  let low := angularFiniteForm 4 angularRowWeight/angularFiniteNorm 4 angularRowWeight
  have hn : 0 < angularFiniteNorm 4 angularRowWeight := by norm_num [angularFiniteNorm,sum_range_succ,angularRowWeight]
  have hl : (1:ℝ)/3.78985 < low := by norm_num [low,angularFiniteForm,angularFiniteNorm,sum_range_succ,angularJacobiEdge,angularRowWeight]
  have hmem : low ∈ R := ⟨4,angularRowWeight,hn,rfl⟩
  have hupper (x) (hx : x ∈ R) : x ≤ (1:ℝ)/3.789841 := by
    obtain ⟨n,z,hn,rfl⟩ := hx
    exact (div_le_iff₀ hn).2 (angular_finite_rayleigh_upper n z)
  have hlow : low ≤ sSup R := le_csSup ⟨_,hupper⟩ hmem
  have hhigh : sSup R ≤ (1:ℝ)/3.789841 := csSup_le ⟨_,hmem⟩ hupper
  change 3.78984 < 1/sSup R ∧ 1/sSup R < 3.78985
  have hpos : 0 < sSup R := lt_trans (by norm_num : (0:ℝ)<1/3.78985) (hl.trans_le hlow)
  constructor
  · apply (lt_div_iff₀ hpos).2; linarith
  · apply (div_lt_iff₀ hpos).2; linarith

end UV
