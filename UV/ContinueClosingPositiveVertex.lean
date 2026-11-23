import UV.ContinuationSectorPlane
import UV.Response
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Signed carrier frequencies, the Schur complement of a charged
boundary channel, and its common temporal insertion. -/

noncomputable section

open Filter ContinuousLinearMap
open scoped Topology InnerProductSpace

namespace UV.SectorPlane

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The imaginary frequency uses the signed component of the real
momentum along the assigned carrier unit. -/
def Plane.closingFrequency (diamond : Plane E) (pGT : E) : ℂ :=
  Complex.I * (inner ℝ (diamond.poleUnit : E) pGT : ℂ)

theorem Plane.closing_frequency_on_carrier (diamond : Plane E) (ω : ℝ) :
    diamond.closingFrequency (ω • (diamond.poleUnit : E)) = Complex.I * (ω : ℂ) := by
  simp [Plane.closingFrequency, Plane.poleUnit, real_inner_smul_right, diamond.inner_carrier_self]

theorem Plane.closing_frequency_im (diamond : Plane E) (ω : ℝ) :
    (diamond.closingFrequency (ω • (diamond.poleUnit : E))).im = ω := by
  rw [diamond.closing_frequency_on_carrier]
  simp

end Geometry

variable {S H : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def closingShift (B : H →L[ℂ] H) (z : ℂ) : H →L[ℂ] H := z • 1 + B

def closingResolvent (B : H →L[ℂ] H) (z : ℂ) : H →L[ℂ] H := Ring.inverse (closingShift B z)

def closingSandwich (T : S →L[ℂ] H) : (H →L[ℂ] H) →L[ℂ] S →L[ℂ] S :=
  ((compL ℂ S H S) T.adjoint).comp ((compL ℂ S H H).flip T)

@[simp] theorem closing_sandwich_apply (T : S →L[ℂ] H) (R : H →L[ℂ] H) (v : S) :
    closingSandwich T R v = T.adjoint (R (T v)) := rfl

def closingInverseSlot (A : S →L[ℂ] S) (T : S →L[ℂ] H)
    (R : H →L[ℂ] H) (z : ℂ) : S →L[ℂ] S :=
  z • 1 + A - closingSandwich T R

def closingTemporalMark (T : S →L[ℂ] H) (q : ℝ)
    (R' R : H →L[ℂ] H) : S →L[ℂ] S :=
  (q : ℂ) • (1 + closingSandwich T (R' * R))

private theorem closing_nonreal_unit_aux {R : Type*} [CStarAlgebra R] [StarModule ℂ R]
    (B : R) (hB : IsSelfAdjoint B) {z : ℂ} (hz : z.im ≠ 0) :
    IsUnit (algebraMap ℂ R z + B) := by
  have hnot : -z ∉ spectrum ℂ B := by
    intro hzspec
    have hi := hB.im_eq_zero_of_mem_spectrum hzspec
    rw [Complex.neg_im] at hi
    exact hz (neg_eq_zero.mp hi)
  have hu : IsUnit (algebraMap ℂ R (-z) - B) := by
    by_contra h
    exact hnot (spectrum.mem_iff.mpr h)
  have hn := hu.neg
  rw [neg_sub, map_neg, sub_neg_eq_add, add_comm] at hn
  exact hn

theorem closing_shift_isUnit_of_nonreal (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    {z : ℂ} (hz : z.im ≠ 0) : IsUnit (closingShift B z) := by
  simpa only [closingShift, Algebra.algebraMap_eq_smul_one] using closing_nonreal_unit_aux B hB hz

omit [CompleteSpace H] in
/-- Ordered resolvent identity for the boundary pencil, at any two
frequencies in its resolvent set. -/
theorem closing_resolvent_diff {B : H →L[ℂ] H} {z z' : ℂ}
    (hz : IsUnit (closingShift B z)) (hz' : IsUnit (closingShift B z')) :
    closingResolvent B z' - closingResolvent B z =
      -(z'-z) • (closingResolvent B z' * closingResolvent B z) := by
  have h := response_resolvent_identity hz' hz
  have hd : closingShift B z - closingShift B z' = -(z'-z) • (1 : H →L[ℂ] H) := by
    unfold closingShift
    module
  simpa [closingResolvent, hd, mul_smul_comm, smul_mul_assoc] using h

/-- The two-frequency identity with the actual ordered boundary resolvents. -/
theorem closing_temporal_ward_of_diff (A : S →L[ℂ] S) (T : S →L[ℂ] H) (q : ℝ)
    (R R' : H →L[ℂ] H) (z z' : ℂ)
    (hR : R' - R = -(z'-z) • (R' * R)) :
    (z'-z) • closingTemporalMark T q R' R =
      (q : ℂ) • (closingInverseSlot A T R' z' - closingInverseSlot A T R z) := by
  have h := congrArg (closingSandwich T) hR
  rw [map_sub, map_smul] at h
  have hd : closingInverseSlot A T R' z' - closingInverseSlot A T R z =
      (z'-z) • 1 - (closingSandwich T R' - closingSandwich T R) := by
    unfold closingInverseSlot
    module
  rw [hd, h]
  unfold closingTemporalMark
  module

theorem closing_temporal_ward (A : S →L[ℂ] S) (T : S →L[ℂ] H) (q : ℝ)
    {B : H →L[ℂ] H} {z z' : ℂ} (hB : IsSelfAdjoint B) (hz : z.im ≠ 0) (hz' : z'.im ≠ 0) :
    (z'-z) • closingTemporalMark T q (closingResolvent B z') (closingResolvent B z) =
      (q : ℂ) • (closingInverseSlot A T (closingResolvent B z') z' -
        closingInverseSlot A T (closingResolvent B z) z) :=
  closing_temporal_ward_of_diff A T q _ _ z z'
    (closing_resolvent_diff (closing_shift_isUnit_of_nonreal B hB hz)
      (closing_shift_isUnit_of_nonreal B hB hz'))

/-- The slope at a point of the boundary resolvent set, including a real
isolated slot pole away from the boundary spectrum. -/
theorem closing_resolvent_hasDerivAt {B : H →L[ℂ] H} {z : ℂ}
    (hu : IsUnit (closingShift B z)) :
    HasDerivAt (closingResolvent B) (-(closingResolvent B z * closingResolvent B z)) z := by
  obtain ⟨u, hU⟩ := hu
  have hZ : HasDerivAt (closingShift B) (1 : H →L[ℂ] H) z := by
    change HasDerivAt (fun w : ℂ => w • (1 : H →L[ℂ] H) + B) _ z
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id z).smul_const (1 : H →L[ℂ] H)).add_const B
  have hF := hasFDerivAt_ringInverse (𝕜 := ℂ) u
  rw [hU] at hF
  simpa [closingResolvent, ← hU, Ring.inverse_unit] using hF.comp_hasDerivAt z hZ

theorem closing_inverse_slot_hasDerivAt (A : S →L[ℂ] S) (T : S →L[ℂ] H)
    {B : H →L[ℂ] H} {z : ℂ} (hu : IsUnit (closingShift B z)) :
    HasDerivAt (fun w => closingInverseSlot A T (closingResolvent B w) w)
      (closingTemporalMark T 1 (closingResolvent B z) (closingResolvent B z)) z := by
  have h₁ := ((hasDerivAt_id z).smul_const (1 : S →L[ℂ] S)).add_const A
  have h₂ := (closingSandwich T).hasFDerivAt.comp_hasDerivAt z (closing_resolvent_hasDerivAt hu)
  simpa [closingInverseSlot, closingTemporalMark, Function.comp_def, sub_neg_eq_add] using h₁.sub h₂

/-- The normalized residue of a unit slot vector is the inverse of one
plus the squared norm of its eliminated boundary component. -/
def closingSlotResidue (T : S →L[ℂ] H) (R : H →L[ℂ] H) (v : S) : ℝ :=
  (1 + ‖R (T v)‖ ^ 2)⁻¹

theorem closing_temporal_mark_quadratic (T : S →L[ℂ] H) (q : ℝ)
    (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (v : S) (hv : ‖v‖ = 1) :
    ⟪v, closingTemporalMark T q R R v⟫_ℂ =
      (q * (1 + ‖R (T v)‖ ^ 2) : ℝ) := by
  have hadj : R.adjoint = R := hR.star_eq
  have hnorm (w : H) : ⟪w, w⟫_ℂ = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_pow] using (inner_self_eq_norm_sq_to_K w)
  simp only [closingTemporalMark, coe_smul', Pi.smul_apply, add_apply, one_apply,
    closing_sandwich_apply, mul_apply, inner_smul_right, inner_add_right, adjoint_inner_right]
  rw [← hadj, adjoint_inner_right, hadj, hnorm, inner_self_eq_norm_sq_to_K, hv]
  norm_num [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_add]

theorem closing_residue_times_temporal_charge (T : S →L[ℂ] H) (q : ℝ)
    (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (v : S) (hv : ‖v‖ = 1) :
    (closingSlotResidue T R v : ℂ) * ⟪v, closingTemporalMark T q R R v⟫_ℂ = (q : ℂ) := by
  rw [closing_temporal_mark_quadratic T q R hR v hv, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  unfold closingSlotResidue
  have hp : 0 < 1 + ‖R (T v)‖ ^ 2 := by positivity
  field_simp

theorem closing_real_resolvent_selfAdjoint (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (a : ℝ) :
    IsSelfAdjoint (closingResolvent B (a : ℂ)) := by
  change star (closingResolvent B (a : ℂ)) = _
  rw [closingResolvent, ← Ring.inverse_star]
  congr 1
  simp [closingShift, star_add, star_smul, hB.star_eq]

/-- The triangular two-frequency insertion couples the same scalar
potential to both channel blocks. Exact elimination produces the
one-mark coefficient before a frequency or amplitude limit. -/
theorem closing_temporal_mixed_elimination (A : S →L[ℂ] S) (T : S →L[ℂ] H) (q : ℝ)
    {B : H →L[ℂ] H} {z z' : ℂ}
    (hz : IsUnit (closingShift B z)) (hz' : IsUnit (closingShift B z'))
    (a : ℂ) (v v' : S) :
    let u := -closingResolvent B z (T v)
    let u' := -closingResolvent B z' (T v' + (a * (q : ℂ)) • u)
    T v + closingShift B z u = 0 ∧
      T v' + (a * (q : ℂ)) • u + closingShift B z' u' = 0 ∧
      closingShift A z' v' + T.adjoint u' + (a * (q : ℂ)) • v =
        closingInverseSlot A T (closingResolvent B z') z' v' +
          a • closingTemporalMark T q (closingResolvent B z') (closingResolvent B z) v := by
  have hR (y : H) : closingShift B z (closingResolvent B z y) = y :=
    congrArg (fun L : H →L[ℂ] H => L y) (Ring.mul_inverse_cancel _ hz)
  have hR' (y : H) : closingShift B z' (closingResolvent B z' y) = y :=
    congrArg (fun L : H →L[ℂ] H => L y) (Ring.mul_inverse_cancel _ hz')
  dsimp only
  refine ⟨by simp [hR], by rw [map_neg, hR']; exact add_neg_cancel _, ?_⟩
  simp only [closingShift, closingInverseSlot, closingTemporalMark, closing_sandwich_apply,
    add_apply, sub_apply, smul_apply, one_apply, mul_apply, map_neg, map_add, map_smul]
  module

theorem closing_pole_residue_charge (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (T : S →L[ℂ] H) (q E₀ : ℝ) (v : S) (hv : ‖v‖ = 1) :
    let R := closingResolvent B (-(E₀ : ℂ))
    (closingSlotResidue T R v : ℂ) * ⟪v, closingTemporalMark T q R R v⟫_ℂ = (q : ℂ) := by
  have hR := closing_real_resolvent_selfAdjoint B hB (-E₀)
  rw [Complex.ofReal_neg] at hR
  exact closing_residue_times_temporal_charge T q _ hR v hv

end UV.SectorPlane
