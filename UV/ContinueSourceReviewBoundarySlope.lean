import UV.ContinueSourceReviewBoundaryResidue
import Mathlib.Topology.Instances.Matrix

/-! General finite-dimensional null-block formulation of the charged
residue calculation. The coordinate is centered at the actual pole. -/

noncomputable section
open Filter Set Matrix
open scoped Topology Matrix
namespace UV.BoundaryResidue

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If the effective null block is z A(z) near a pole, its residue is
the inverse of the full limiting slope matrix. This includes a multiple
kernel without assuming an eigenvector for its slope. -/
theorem effective_null_block_residue (D A : ℂ → Matrix n n ℂ)
    (h : ∀ᶠ z : ℂ in 𝓝[≠] 0, D z=z • A z) (hA : ContinuousAt A 0)
    (hd : (A 0).det ≠ 0) :
    Tendsto (fun z : ℂ => z • (D z)⁻¹) (𝓝[≠] 0) (𝓝 (A 0)⁻¹) := by
  have hcont : ContinuousAt Ring.inverse (A 0).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hd
  have hi := ((continuousAt_matrix_inv _ hcont).comp hA).continuousWithinAt (s:=({0}:Set ℂ)ᶜ)
  have hdet := (continuous_id.matrix_det.continuousAt.comp hA).tendsto.eventually_ne hd
  apply hi.congr'
  filter_upwards [h,hdet.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin (s:=({0}:Set ℂ)ᶜ)]
    with z he hdet hz
  have hz₀ : z ≠ 0 := hz
  letI := invertibleOfNonzero hz₀
  dsimp only [Function.comp_apply, id_eq] at *
  rw [he,Matrix.inv_smul _ _ (isUnit_iff_ne_zero.mpr hdet),invOf_eq_inv,smul_smul,mul_inv_cancel₀ hz₀,one_smul]

/-- The inverse slope and the temporal mark cancel at the matrix level
on the whole effective pole space, irrespective of its multiplicity. -/
theorem effective_residue_ward (A : Matrix n n ℂ) (hd : A.det ≠ 0) (q : ℂ) :
    A⁻¹ * (q • A) = q • (1 : Matrix n n ℂ) := by
  rw [Matrix.mul_smul,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd)]

/-- A normalized slope eigenvector recovers the scalar reciprocal-slope
and residue-times-charge formulas; this in particular applies to the
unique direction of any one-dimensional effective null block. -/
theorem effective_residue_eigenchannel (A : Matrix n n ℂ) (hd : A.det ≠ 0)
    (v : n → ℂ) (hn : dotProduct (star v) v = 1) (κ q : ℂ) (hκ : κ ≠ 0)
    (he : A *ᵥ v=κ • v) :
    dotProduct (star v) (A⁻¹ *ᵥ v) = κ⁻¹ ∧
      dotProduct (star v) ((q • A) *ᵥ v) = q*κ ∧
      dotProduct (star v) (A⁻¹ *ᵥ v) * dotProduct (star v) ((q • A) *ᵥ v) = q := by
  have ha := congrArg (fun w : n → ℂ => A⁻¹ *ᵥ w) he
  simp only [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd),
    Matrix.one_mulVec,Matrix.mulVec_smul] at ha
  have hh := congrArg (fun w : n → ℂ => κ⁻¹ • w) ha
  simp only [smul_smul,inv_mul_cancel₀ hκ,one_smul] at hh
  rw [←hh,Matrix.smul_mulVec,he,smul_smul,dotProduct_smul,dotProduct_smul,hn]
  simp only [smul_eq_mul,mul_one]
  refine ⟨trivial,trivial,?_⟩
  field_simp

end UV.BoundaryResidue
