import UV.ContinueNetworkDirectional
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Ordered finite-row precision comparisons for the Schwinger sectors.
All weights are inherited from their original rows. -/

noncomputable section

open scoped BigOperators

namespace UV.ContinueNetworkPrecision

variable {ι V : Type*} [Fintype ι] [LinearOrder ι] [AddCommGroup V] [Module ℝ V]

/-- The precision of a finite row family at the given Schwinger weights. -/
def rowPrecision (rows : ι → V →ₗ[ℝ] ℝ) (w : ι → ℝ) (k : V) : ℝ :=
  ∑ r, w r * (rows r k)^2

/-- Keep the original momentum coordinates and weights of the selected rows. -/
def selectedPrecision (rows : ι → V →ₗ[ℝ] ℝ) (b : Finset ι) (w : ι → ℝ) (k : V) : ℝ :=
  ∑ i ∈ b, w i * (rows i k)^2

/-- The chosen rows available when row `r` is processed. -/
def availableRows (b : Finset ι) (r : ι) : Finset ι := b.filter (· ≤ r)

/-- The exact row expansions which suffice for a comparison on the whole
ordered sector, with no weight-dependent change of coordinates. -/
def hasEarlierExpansion (rows : ι → V →ₗ[ℝ] ℝ) (b : Finset ι) (coefficient : ι → ι → ℝ) : Prop :=
  ∀ r, (∑ i ∈ availableRows b r, coefficient r i • rows i) = rows r

omit [Fintype ι] [LinearOrder ι] in
private theorem selectedPrecision_nonneg (rows : ι → V →ₗ[ℝ] ℝ) (b : Finset ι)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (k : V) : 0 ≤ selectedPrecision rows b w k :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))

/-- The uniform two-sided comparison, keeping the selected weights exactly.
The lower constant is one, and the upper constant depends only on the
fixed expansion coefficients, uniformly for all ordered nonnegative weights. -/
theorem precision_compare_of_earlierExpansion (rows : ι → V →ₗ[ℝ] ℝ) (b : Finset ι)
    (coefficient : ι → ι → ℝ) (h : hasEarlierExpansion rows b coefficient) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (w : ι → ℝ) (k : V), (∀ i, 0 ≤ w i) → Antitone w →
      selectedPrecision rows b w k ≤ rowPrecision rows w k ∧
      rowPrecision rows w k ≤ C * selectedPrecision rows b w k := by
  let D (r : ι) : ℝ := ∑ i ∈ availableRows b r, (coefficient r i)^2
  have hD (r : ι) : 0 ≤ D r := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  let C := 1 + ∑ r, D r
  refine ⟨C, le_add_of_nonneg_right (Finset.sum_nonneg (fun r _ => hD r)),
    fun w k hw horder => ⟨?_, ?_⟩⟩
  · unfold selectedPrecision rowPrecision
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ b)
      (fun i _ _ => mul_nonneg (hw i) (sq_nonneg _))
  have hRow (r : ι) : rows r k = ∑ i ∈ availableRows b r, coefficient r i * rows i k := by
    have he := congrArg (fun f : V →ₗ[ℝ] ℝ => f k) (h r)
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using he.symm
  have hWeight (r : ι) : (∑ i ∈ availableRows b r, w r * (rows i k)^2) ≤
      selectedPrecision rows b w k := by
    apply (Finset.sum_le_sum (fun i hi => ?_)).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => mul_nonneg (hw i) (sq_nonneg _)))
    exact mul_le_mul_of_nonneg_right (horder (Finset.mem_filter.mp hi).2) (sq_nonneg _)
  have hTerm (r : ι) : w r * (rows r k)^2 ≤ D r * selectedPrecision rows b w k := by
    calc
      _ = w r * (∑ i ∈ availableRows b r, coefficient r i * rows i k)^2 := by rw [hRow r]
      _ ≤ w r * (D r * ∑ i ∈ availableRows b r, (rows i k)^2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_mul_sq_le_sq_mul_sq (availableRows b r)
          (coefficient r) (fun i => rows i k)) (hw r)
      _ = D r * (∑ i ∈ availableRows b r, w r * (rows i k)^2) := by rw [← Finset.mul_sum]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hWeight r) (hD r)
  unfold rowPrecision
  calc
    _ ≤ ∑ r, D r * selectedPrecision rows b w k := Finset.sum_le_sum (fun r _ => hTerm r)
    _ = (∑ r, D r) * selectedPrecision rows b w k := (Finset.sum_mul ..).symm
    _ ≤ C * selectedPrecision rows b w k := mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left zero_le_one) (selectedPrecision_nonneg rows b w hw k)

end UV.ContinueNetworkPrecision
