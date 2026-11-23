import UV.ContinueClosingPositiveSchur
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-! Finite positive atomic signed-energy matrix laws have an actual
isometric Hilbert realization, using the positive square roots of
their matrix weights and coordinatewise real energy multiplication. -/

noncomputable section

open ContinuousLinearMap
open scoped InnerProductSpace CStarAlgebra

namespace UV.SectorPlane

variable {S ι : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S] [Fintype ι]

abbrev ClosingAtomicSpace (ι S : Type*) := PiLp 2 (fun _ : ι => S)

omit [CompleteSpace S] in
def closingAtomicLift (C : ι → S →L[ℂ] S) : S →L[ℂ] ClosingAtomicSpace ι S :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => S)).symm.toContinuousLinearMap.comp (pi C)

omit [CompleteSpace S] in
@[simp] theorem closing_atomic_lift_apply (C : ι → S →L[ℂ] S) (v : S) (i : ι) :
    closingAtomicLift C v i = C i v := rfl

omit [CompleteSpace S] in
def closingAtomicDiag (a : ι → ℂ) :
    ClosingAtomicSpace ι S →L[ℂ] ClosingAtomicSpace ι S :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => S)).symm.toContinuousLinearMap.comp
    (pi fun i => a i • PiLp.proj 2 (β := fun _ : ι => S) i)

omit [CompleteSpace S] in
@[simp] theorem closing_atomic_diag_apply (a : ι → ℂ) (x : ClosingAtomicSpace ι S) (i : ι) :
    closingAtomicDiag a x i = a i • x i := rfl

theorem closing_atomic_energy_selfAdjoint (E : ι → ℝ) :
    IsSelfAdjoint (closingAtomicDiag (S := S) fun i => (E i : ℂ)) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  symm
  apply (eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply, closing_atomic_diag_apply, inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  change star (E i : ℂ) * _ = _
  rw [Complex.star_def, Complex.conj_ofReal]

theorem closing_atomic_compression (C : ι → S →L[ℂ] S) (a : ι → ℂ) :
    (closingAtomicLift C).adjoint.comp ((closingAtomicDiag a).comp (closingAtomicLift C)) =
      ∑ i, a i • ((C i).adjoint.comp (C i)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro u
  simp only [coe_comp', Function.comp_apply, adjoint_inner_right, PiLp.inner_apply,
    closing_atomic_lift_apply, closing_atomic_diag_apply, inner_smul_right, sum_apply,
    smul_apply, inner_sum]

theorem closing_atomic_lift_norm (C : ι → S →L[ℂ] S)
    (hC : (∑ i, (C i).adjoint.comp (C i)) = (1 : S →L[ℂ] S)) (v : S) :
    ‖closingAtomicLift C v‖ = ‖v‖ := by
  have he : closingAtomicDiag (S := S) (fun _ : ι => (1 : ℂ)) = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    ext i
    simp
  have h := closing_atomic_compression C (fun _ : ι => (1 : ℂ))
  rw [he] at h
  simp only [one_smul, hC] at h
  change (closingAtomicLift C).adjoint.comp (closingAtomicLift C) = _ at h
  have hz := (closingAtomicLift C).apply_norm_sq_eq_inner_adjoint_right v
  rw [h, one_apply, inner_self_eq_norm_sq] at hz
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hz

omit [CompleteSpace S] in
theorem closing_atomic_diag_shift_inverse (E : ι → ℝ) (z : ℂ)
    (h : ∀ i, z + (E i : ℂ) ≠ 0) :
    closingResolvent (closingAtomicDiag (S := S) fun i => (E i : ℂ)) z =
      closingAtomicDiag (fun i => (z + (E i : ℂ))⁻¹) := by
  let K : ClosingAtomicSpace ι S →L[ℂ] ClosingAtomicSpace ι S :=
    closingAtomicDiag fun i => (E i : ℂ)
  let R : ClosingAtomicSpace ι S →L[ℂ] ClosingAtomicSpace ι S :=
    closingAtomicDiag fun i => (z + (E i : ℂ))⁻¹
  have hK (x : ClosingAtomicSpace ι S) (i : ι) : closingShift K z x i = (z + (E i : ℂ)) • x i := by
    change (z • x + closingAtomicDiag (fun j => (E j : ℂ)) x) i = _
    simp [add_smul]
  have h₁ : closingShift K z * R = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    ext i
    simp [mul_apply, hK, R, smul_smul, mul_inv_cancel₀ (h i)]
  have h₂ : R * closingShift K z = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    ext i
    simp [mul_apply, hK, R, smul_smul, inv_mul_cancel₀ (h i)]
  let u : (ClosingAtomicSpace ι S →L[ℂ] ClosingAtomicSpace ι S)ˣ :=
    ⟨closingShift K z, R, h₁, h₂⟩
  exact Ring.inverse_unit u

/-- For arbitrary normalized positive finite atomic weights, the
Cauchy transform is the compression of an actual self-adjoint
energy multiplier by a linear isometry. Both signs of E are allowed. -/
theorem closing_finite_atomic_positive_realization (E : ι → ℝ)
    (W : ι → S →L[ℂ] S) (hW : ∀ i, 0 ≤ W i)
    (hI : (∑ i, W i) = (1 : S →L[ℂ] S)) :
    ∃ (J : S →ₗᵢ[ℂ] ClosingAtomicSpace ι S)
      (K : ClosingAtomicSpace ι S →L[ℂ] ClosingAtomicSpace ι S),
      IsSelfAdjoint K ∧
      (∀ z : ℂ, z.im ≠ 0 →
        J.toContinuousLinearMap.adjoint.comp ((closingResolvent K z).comp J.toContinuousLinearMap) =
          ∑ i, (z + (E i : ℂ))⁻¹ • W i) ∧
      J.toContinuousLinearMap.adjoint.comp (K.comp J.toContinuousLinearMap) =
        ∑ i, (E i : ℂ) • W i := by
  let C : ι → S →L[ℂ] S := fun i => CFC.sqrt (W i)
  have hC (i : ι) : (C i).adjoint.comp (C i) = W i := by
    have hs : (C i).adjoint = C i := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq
    rw [hs]
    exact CFC.sqrt_mul_sqrt_self (W i) (hW i)
  have hsum : (∑ i, (C i).adjoint.comp (C i)) = (1 : S →L[ℂ] S) := by
    simp only [hC, hI]
  let J : S →ₗᵢ[ℂ] ClosingAtomicSpace ι S :=
    { toLinearMap := (closingAtomicLift C).toLinearMap
      norm_map' := closing_atomic_lift_norm C hsum }
  let K : ClosingAtomicSpace ι S →L[ℂ] ClosingAtomicSpace ι S :=
    closingAtomicDiag fun i => (E i : ℂ)
  refine ⟨J, K, closing_atomic_energy_selfAdjoint E, ?_, ?_⟩
  · intro z hz
    have hne (i : ι) : z + (E i : ℂ) ≠ 0 := by
      intro h
      apply hz
      simpa only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.zero_im] using
        congrArg Complex.im h
    change (closingAtomicLift C).adjoint.comp ((closingResolvent K z).comp (closingAtomicLift C)) = _
    rw [closing_atomic_diag_shift_inverse E z hne, closing_atomic_compression]
    simp only [hC]
  · change (closingAtomicLift C).adjoint.comp ((closingAtomicDiag _).comp (closingAtomicLift C)) = _
    rw [closing_atomic_compression]
    simp only [hC]

end UV.SectorPlane
