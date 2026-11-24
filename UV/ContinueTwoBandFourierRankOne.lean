import UV.ContinueTwoBandFourierKernel
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! A trace-class expansion of the actual product of the two gauged
slab blocks. The expansion uses rank-one operators with summable trace
norm costs in any chosen Hilbert basis. -/

noncomputable section
open MeasureTheory Filter
open scoped ComplexInnerProductSpace ENNReal Topology

namespace UV.SectorPlane.SlabKernel

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
variable {ι : Type*} (b : HilbertBasis ι ℂ X)

omit [CompleteSpace X] in
private theorem basis_norm_squares (x : X) :
    HasSum (fun j => ‖⟪b j,x⟫‖^2) (‖x‖^2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,b.repr_apply_apply,LinearIsometryEquiv.norm_map] using
    lp.hasSum_norm (by norm_num : (0:ℝ) < (2:ℝ≥0∞).toReal) (b.repr x)

theorem square_adjoint_columns (A : X →L[ℂ] X) (hA : Summable (fun i => ‖A (b i)‖^2)) :
    Summable (fun i => ‖A.adjoint (b i)‖^2) := by
  let v := fun i j => ‖⟪b i,A (b j)⟫‖^2
  have hi (i : ι) : HasSum (v i) (‖A.adjoint (b i)‖^2) := by
    convert basis_norm_squares b (A.adjoint (b i)) using 1
    funext j
    dsimp [v]
    rw [ContinuousLinearMap.adjoint_inner_right,norm_inner_symm]
  apply summable_of_sum_le (c := ∑' j, ‖A (b j)‖^2) (fun _ => sq_nonneg _)
  intro S
  simp_rw [← (hi _).tsum_eq]
  rw [← Summable.tsum_finsetSum (s := S) (fun i _ => (hi i).summable)]
  exact (summable_sum (fun i _ => (hi i).summable)).tsum_le_tsum
    (fun j => b.orthonormal.sum_inner_products_le (s := S) (A (b j))) hA

/-- A left/right block product is the norm-convergent sum of its
intermediate basis contractions. Each coefficient is an explicit
rank-one operator whose norm equals its trace norm. -/
theorem nuclear_product (A B : X →L[ℂ] X)
    (hA : Summable (fun i => ‖A (b i)‖^2)) (hB : Summable (fun i => ‖B (b i)‖^2)) :
    let V := fun i => B (b i)
    let W := fun i => A.adjoint (b i)
    Summable (fun i => ‖W i‖*‖V i‖) ∧
      HasSum (fun i => (innerSL ℂ (W i)).smulRight (V i)) (B.comp A) := by
  let V := fun i => B (b i)
  let W := fun i => A.adjoint (b i)
  let R := fun i => (innerSL ℂ (W i)).smulRight (V i)
  have hW := square_adjoint_columns b A hA
  have hN : Summable (fun i => ‖W i‖*‖V i‖) := by
    apply ((hW.add hB).mul_left (1/2:ℝ)).of_nonneg_of_le (fun _ => by positivity)
    intro i
    change ‖W i‖*‖V i‖ ≤ (1/2)*(‖W i‖^2+‖V i‖^2)
    nlinarith only [sq_nonneg (‖W i‖-‖V i‖)]
  have hR : Summable R := hN.of_norm_bounded (fun i => by
    simp [R,ContinuousLinearMap.norm_smulRight_apply])
  refine ⟨hN,?_⟩
  suffices he : (∑' i, R i) = B.comp A from he ▸ hR.hasSum
  ext x
  have hleft := (ContinuousLinearMap.apply ℂ X x).hasSum hR.hasSum
  have hright := (b.hasSum_repr (A x)).mapL B
  apply hleft.unique
  convert hright using 1
  funext i
  simp [V,W,R,b.repr_apply_apply,ContinuousLinearMap.adjoint_inner_left]

end UV.SectorPlane.SlabKernel
