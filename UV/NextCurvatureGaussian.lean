import UV.FurtherCurvatureDeterminant
import UV.RevisionSourceGaussian
import Mathlib.MeasureTheory.Integral.Pi

/-! The literal finite-dimensional Gaussian kinetic integral. On the fixed
sector torus the signed frequency labels represent the two real coordinates
of each nonzero opposite pair. There are two real adjoint fields, each with
the same orthonormal color-coordinate norm. -/

noncomputable section

open MeasureTheory Real
open scoped BigOperators

namespace UV.NextCurvatureGaussian

open UV.FurtherCurvatureShell UV.FurtherCurvatureLine UV.FurtherCurvatureDeterminant
open UV.RevisionCurvatureDeterminant

abbrev KineticSlot (n : ℕ) (modes : Finset TorusMode) := modes × (Fin 2 × Fin n)

def boundaryKinetic (k : TorusMode) : ℝ := latticeFrequency k ^ 2

def transferredKinetic (ℓ : ℝ) (k : TorusMode) : ℝ :=
  boundaryKinetic k * (1 + exp (-2 * ℓ * latticeFrequency k))

def kineticAction {n : ℕ} {modes : Finset TorusMode}
    (a : TorusMode → ℝ) (X : KineticSlot n modes → ℝ) : ℝ :=
  ∑ i, (a i.1 / 2) * X i ^ 2

def kineticPartition (n : ℕ) (modes : Finset TorusMode) (a : TorusMode → ℝ) : ℝ :=
  ∫ X : KineticSlot n modes → ℝ, exp (-kineticAction a X)

private theorem boundaryKinetic_pos {k : TorusMode} (hk : k ≠ 0) :
    0 < boundaryKinetic k := by
  have h := (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (latticeHeight_ne_zero hk))).trans_le
    (latticeHeight_le_latticeFrequency k)
  exact sq_pos_of_pos h

private theorem transferredKinetic_pos (ℓ : ℝ) {k : TorusMode} (hk : k ≠ 0) :
    0 < transferredKinetic ℓ k :=
  mul_pos (boundaryKinetic_pos hk) (by positivity)

theorem kinetic_partition_product (n : ℕ) (modes : Finset TorusMode) (a : TorusMode → ℝ) :
    kineticPartition n modes a = ∏ i : KineticSlot n modes, sqrt (π / (a i.1 / 2)) := by
  unfold kineticPartition
  have hf (X : KineticSlot n modes → ℝ) :
      exp (-kineticAction a X) = ∏ i, exp (-(a i.1 / 2) * X i ^ 2) := by
    unfold kineticAction
    rw [← Finset.sum_neg_distrib, exp_sum]
    simp only [neg_mul]
  simp_rw [hf]
  calc
    _ = ∏ i : KineticSlot n modes, ∫ x : ℝ, exp (-(a i.1 / 2) * x ^ 2) :=
      integral_fintype_prod_volume_eq_prod (fun i : KineticSlot n modes =>
        fun x : ℝ => exp (-(a i.1 / 2) * x ^ 2))
    _ = _ := by simp_rw [integral_gaussian]

private theorem kinetic_partition_pos (n : ℕ) (modes : Finset TorusMode) (a : TorusMode → ℝ)
    (ha : ∀ k ∈ modes, 0 < a k) : 0 < kineticPartition n modes a := by
  rw [kinetic_partition_product]
  exact Finset.prod_pos (fun i _ => sqrt_pos.mpr (div_pos pi_pos (half_pos (ha _ i.1.2))))

private theorem gaussian_sqrt_ratio {a e : ℝ} (ha : 0 < a) (he : 0 < 1 + e) :
    sqrt (π / (a * (1 + e) / 2)) / sqrt (π / (a / 2)) =
      sqrt ((1 + e)⁻¹) := by
  rw [← sqrt_div (by positivity)]
  congr 1
  field_simp [ha.ne', he.ne', pi_ne_zero]

/-- The Gaussian integral of the full copied kinetic form, divided by the
boundary-only integral, gives the exact single relative determinant.
The two independent fields supply the power per signed lattice mode. -/
theorem spherical_kinetic_partition_ratio (n : ℕ) (Λ ℓ : ℝ) :
    0 < kineticPartition n (sphericalModes Λ) boundaryKinetic ∧
    0 < kineticPartition n (sphericalModes Λ) (transferredKinetic ℓ) ∧
    kineticPartition n (sphericalModes Λ) (transferredKinetic ℓ) /
      kineticPartition n (sphericalModes Λ) boundaryKinetic = sphericalDeterminant n Λ ℓ := by
  have hb (k : TorusMode) (hk : k ∈ sphericalModes Λ) : 0 < boundaryKinetic k :=
    boundaryKinetic_pos (mem_sphericalModes.mp hk).1
  have ht (k : TorusMode) (hk : k ∈ sphericalModes Λ) : 0 < transferredKinetic ℓ k :=
    transferredKinetic_pos ℓ (mem_sphericalModes.mp hk).1
  refine ⟨kinetic_partition_pos _ _ _ hb, kinetic_partition_pos _ _ _ ht, ?_⟩
  rw [kinetic_partition_product, kinetic_partition_product, ← Finset.prod_div_distrib]
  have hh (i : KineticSlot n (sphericalModes Λ)) :
      sqrt (π / (transferredKinetic ℓ i.1 / 2)) / sqrt (π / (boundaryKinetic i.1 / 2)) =
        sqrt ((1 + exp (-2*ℓ*latticeFrequency i.1))⁻¹) :=
    gaussian_sqrt_ratio (hb _ i.1.2) (by positivity)
  simp_rw [hh]
  rw [Fintype.prod_prod_type]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  have hpow (i : sphericalModes Λ) :
      sqrt ((1 + exp (-2*ℓ*latticeFrequency i))⁻¹) ^ (2*n) =
        ((1 + exp (-2*ℓ*latticeFrequency i))^n)⁻¹ := by
    rw [pow_mul, sq_sqrt (by positivity), inv_pow]
  simp_rw [hpow]
  rw [Finset.prod_coe_sort (f := fun k : TorusMode => ((1 + exp (-2*ℓ*latticeFrequency k))^n)⁻¹)]
  unfold sphericalDeterminant relativeDeterminant
  rw [Finset.prod_inv_distrib]

end UV.NextCurvatureGaussian
