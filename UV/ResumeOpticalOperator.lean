import UV.ContinuationSectorPlane
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Conditional physical unitarity on one fixed sector plane. The
adjoint is that of the positive-norm Hilbert space of wave packets. -/

noncomputable section

namespace UV.SectorPlane

open scoped InnerProductSpace InnerProduct ENNReal

variable {E H : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The physical scattering operator in the (S=1+iT) convention. -/
def Plane.physicalScattering (diamond : Plane E) (T : Plane E → H →L[ℂ] H) :
    H →L[ℂ] H :=
  1 + Complex.I • T diamond

/-- The algebraic consequence of unitarity uses the actual physical
adjoint on the chosen plane. -/
theorem Plane.physical_unitarity_identity (diamond : Plane E)
    (T : Plane E → H →L[ℂ] H)
    (hS : (diamond.physicalScattering T)† * diamond.physicalScattering T = 1) :
    (-Complex.I) • (T diamond - (T diamond)†) = (T diamond)† * T diamond := by
  let A := T diamond
  change (star (1 + Complex.I • A)) * (1 + Complex.I • A) = 1 at hS
  change (-Complex.I) • (A - star A) = star A * A
  have hS' : star (1 + Complex.I • A : H →L[ℂ] H) * (1 + Complex.I • A) =
      1 + Complex.I • (A - star A) + star A * A := by
    rw [star_add, star_one, star_smul, show star Complex.I = -Complex.I from Complex.conj_I, add_mul, one_mul, mul_add, mul_one]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, show (-Complex.I) * Complex.I = 1 by
      rw [neg_mul, ← pow_two, Complex.I_sq, neg_neg], one_smul]
    rw [smul_sub, sub_eq_add_neg, neg_smul]
    abel
  rw [hS'] at hS
  have hA : Complex.I • (A - star A) + star A * A = 0 := by
    exact add_left_cancel (by simpa only [add_assoc, add_zero] using hS)
  rw [neg_smul]
  exact (eq_neg_of_add_eq_zero_right hA).symm

/-- Before any sharp-momentum distribution is factored out, the forward
matrix element on an arbitrary normalizable packet is the transition norm. -/
theorem Plane.physical_optical_packet (diamond : Plane E)
    (T : Plane E → H →L[ℂ] H)
    (hS : (diamond.physicalScattering T)† * diamond.physicalScattering T = 1)
    (i : H) :
    2 * (⟪i, T diamond i⟫_ℂ).im = ‖T diamond i‖ ^ 2 := by
  let A := T diamond
  have he := congrArg (fun x : H →L[ℂ] H => (⟪i, x i⟫_ℂ).re)
    (diamond.physical_unitarity_identity T hS)
  change (⟪i, ((-Complex.I) • (A - A†)) i⟫_ℂ).re = (⟪i, (A† * A) i⟫_ℂ).re at he
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, inner_smul_right,
    inner_sub_right, ContinuousLinearMap.adjoint_inner_right] at he
  have hr : (⟪i, (A† * A) i⟫_ℂ).re = ‖A i‖ ^ 2 := by
    change (⟪i, (A†) (A i)⟫_ℂ).re = _
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (A i)
  rw [hr] at he
  have hconj : ⟪A i, i⟫_ℂ = star ⟪i, A i⟫_ℂ := (inner_conj_symm (A i) i).symm
  have hIm : (⟪A i, i⟫_ℂ).im = -(⟪i, A i⟫_ℂ).im := by
    rw [hconj]
    exact Complex.conj_im _
  simp [Complex.mul_re, hIm] at he
  simpa only [two_mul] using he

/-- An actual complete orthonormal intermediate state resolution gives
the sum of squared transition coefficients, with no omitted basis sector. -/
theorem Plane.physical_optical_basis (diamond : Plane E)
    (T : Plane E → H →L[ℂ] H)
    (hS : (diamond.physicalScattering T)† * diamond.physicalScattering T = 1)
    {ι : Type*} (b : HilbertBasis ι ℂ H) (i : H) :
    HasSum (fun n => ‖⟪b n, T diamond i⟫_ℂ‖ ^ 2)
      (2 * (⟪i, T diamond i⟫_ℂ).im) := by
  have hb : HasSum (fun n => ‖b.repr (T diamond i) n‖ ^ 2) (‖T diamond i‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr.norm_map] using
      lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (b.repr (T diamond i))
  simpa only [b.repr_apply_apply, diamond.physical_optical_packet T hS i] using hb

end UV.SectorPlane
