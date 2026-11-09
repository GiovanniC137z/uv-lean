import UV.Response
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The pointwise ordered Neumann error for literal finite matrix readouts.
Every norm is the Euclidean operator norm, including rectangular endpoint
maps. All sign and nonnegativity bounds follow from the original norm data. -/

noncomputable section
open scoped Matrix.Norms.L2Operator

namespace UV

variable {n i o : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [Fintype i] [DecidableEq i] [Fintype o]

theorem matrix_observable_neumann_error
    (X Y : Matrix n n ℂ) (U : Matrix o n ℂ) (V : Matrix n i ℂ)
    {B ε Lout Lin : ℝ}
    (hYdet : Y.det ≠ 0) (hB : ‖Y⁻¹‖ ≤ B) (hε : ‖X-Y‖ ≤ ε)
    (hq : B*ε < 1) (hLo : ‖U‖ ≤ Lout) (hLi : ‖V‖ ≤ Lin) :
    ‖U*X⁻¹*V-U*Y⁻¹*V‖ ≤ Lout*Lin*B^2*ε/(1-B*ε) := by
  have hY : IsUnit Y := (Matrix.isUnit_iff_isUnit_det Y).mpr (isUnit_iff_ne_zero.mpr hYdet)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have hLo0 : 0 ≤ Lout := (norm_nonneg _).trans hLo
  have hLi0 : 0 ≤ Lin := (norm_nonneg _).trans hLi
  have hden : 0 < 1-B*ε := sub_pos.mpr hq
  have hdiff : ‖X⁻¹-Y⁻¹‖ ≤ B^2*ε/(1-B*ε) := by
    have h := response_resolvent_error hY
      (by simpa only [Matrix.nonsing_inv_eq_ringInverse] using hB)
      (show ‖Y-X‖ ≤ ε by simpa only [norm_sub_rev] using hε) hq
    have he : Y-(Y-X) = X := by abel
    simpa only [he, Matrix.nonsing_inv_eq_ringInverse] using h
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  calc
    _ ≤ ‖U*(X⁻¹-Y⁻¹)‖*‖V‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖U‖*‖X⁻¹-Y⁻¹‖)*‖V‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (Lout*(B^2*ε/(1-B*ε)))*Lin := by gcongr
    _ = _ := by ring

end UV
