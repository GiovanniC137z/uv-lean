import UV.Carrier
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Tactic

/-! Momentum dependence of a commuting local charge on one locked sector
plane. The sector and its carrier displacement are held fixed throughout.
The physical adjoint is the matrix conjugate transpose on the slots. -/

noncomputable section
open Filter Set Matrix
open scoped Topology Matrix

namespace UV

abbrev ChargeSpatialMomentum := EuclideanSpace ℝ (Fin 3)
abbrev ChargePlane (Sector : Type*) := Sector × ℝ

variable {Sector : Type*} {d : ℕ}

/-- An inclusive positive temporal matrix evaluated on a single plane. -/
def chargeGram (K : ChargePlane Sector → ChargeSpatialMomentum → ChargeSpatialMomentum →
    Matrix (Fin d) (Fin d) ℂ) (plane : ChargePlane Sector) (p k : ChargeSpatialMomentum) :
    Matrix (Fin d) (Fin d) ℂ := (K plane p k)ᴴ * K plane p k

theorem chargeGram_hermitian (K : ChargePlane Sector → ChargeSpatialMomentum →
    ChargeSpatialMomentum → Matrix (Fin d) (Fin d) ℂ)
    (plane : ChargePlane Sector) (p k : ChargeSpatialMomentum) :
    (chargeGram K plane p k).IsHermitian :=
  by simp [chargeGram, Matrix.IsHermitian, conjTranspose_mul]

/-- The matrix transport identity follows from the shifted multiplication
laws for the two commuting charge modes and their reverse marks. -/
theorem chargeGram_transport (K : ChargePlane Sector → ChargeSpatialMomentum →
    ChargeSpatialMomentum → Matrix (Fin d) (Fin d) ℂ) (plane : ChargePlane Sector)
    (hadj : ∀ p k, K plane (-p) (k + p) = (K plane p k)ᴴ)
    (hcomm : ∀ p h k, K plane h (k + p) * K plane p k =
      K plane p (k + h) * K plane h k) (p h k : ChargeSpatialMomentum) :
    chargeGram K plane p (k + h) * K plane h k =
      K plane h k * chargeGram K plane p k := by
  unfold chargeGram
  rw [← hadj, ← hadj, mul_assoc, ← hcomm p h k]
  rw [← mul_assoc, add_right_comm k h p, ← hcomm (-p) h (k + p)]
  simp [mul_assoc]

private theorem charge_charpoly_of_transport {A B U : Matrix (Fin d) (Fin d) ℂ}
    (hu : IsUnit U.det) (h : A * U = U * B) : A.charpoly = B.charpoly := by
  let V : (Matrix (Fin d) (Fin d) ℂ)ˣ := ((isUnit_iff_isUnit_det U).mpr hu).unit
  have hV : (V : Matrix (Fin d) (Fin d) ℂ) = U :=
    ((isUnit_iff_isUnit_det U).mpr hu).unit_spec
  have hh : A = (V : Matrix (Fin d) (Fin d) ℂ) * B *
      ((V⁻¹ : (Matrix (Fin d) (Fin d) ℂ)ˣ) : Matrix (Fin d) (Fin d) ℂ) := by
    rw [hV, ← h, ← hV, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  rw [hh]
  exact Matrix.charpoly_units_conj V B

/-- All ordered eigenvalues of the inclusive charge Gram matrix are
constant in carrier momentum. Positivity of the charge at zero transfer
implies local invertibility of the transport matrices. -/
theorem commuting_local_charge_eigenvalues (K : ChargePlane Sector → ChargeSpatialMomentum →
    ChargeSpatialMomentum → Matrix (Fin d) (Fin d) ℂ) (plane : ChargePlane Sector)
    (hcont : Continuous (Function.uncurry (K plane))) {q : ℝ} (hq : q ≠ 0)
    (hzero : ∀ k, K plane 0 k = (q : ℂ) • 1)
    (hadj : ∀ p k, K plane (-p) (k + p) = (K plane p k)ᴴ)
    (hcomm : ∀ p h k, K plane h (k + p) * K plane p k = K plane p (k + h) * K plane h k)
    (p k k' : ChargeSpatialMomentum) :
    (chargeGram_hermitian K plane p k).eigenvalues =
      (chargeGram_hermitian K plane p k').eigenvalues := by
  have hlocal : IsLocallyConstant (fun k => (chargeGram K plane p k).charpoly) := by
    apply (IsLocallyConstant.iff_eventually_eq _).2
    intro x
    have hct : Continuous (fun y => (K plane (y - x) x).det) :=
      (hcont.comp ((continuous_id.sub continuous_const).prodMk continuous_const)).matrix_det
    have hn : (K plane (x - x) x).det ≠ 0 := by
      rw [sub_self, hzero, Matrix.det_smul, Matrix.det_one, mul_one]
      exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hq)
    filter_upwards [hct.continuousAt.eventually_ne hn] with y hy
    have ht := chargeGram_transport K plane hadj hcomm p (y - x) x
    rw [show x + (y - x) = y by abel] at ht
    exact charge_charpoly_of_transport (isUnit_iff_ne_zero.mpr hy) ht
  apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).mpr
  exact hlocal.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ k) (mem_univ k')

/-- Sum of squared entries over all incoming and outgoing slots. -/
def chargeInclusiveSquare (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, Complex.normSq (A i j)

theorem chargeInclusiveSquare_eq_trace (A : Matrix (Fin d) (Fin d) ℂ) :
    chargeInclusiveSquare A = (Aᴴ * A).trace.re := by
  unfold chargeInclusiveSquare Matrix.trace
  simp only [Matrix.diag_apply, Complex.re_sum, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp [Complex.normSq_apply, Complex.mul_re]

/-- The full inclusive squared norm is constant in `k` for every `p`, and
strictly positive for a neighborhood of zero transfer in nonzero charge. -/
theorem commuting_local_charge_inclusive_square (K : ChargePlane Sector → ChargeSpatialMomentum →
    ChargeSpatialMomentum → Matrix (Fin d) (Fin d) ℂ) (plane : ChargePlane Sector) (hd : 0 < d)
    (hcont : Continuous (Function.uncurry (K plane))) {q : ℝ} (hq : q ≠ 0)
    (hzero : ∀ k, K plane 0 k = (q : ℂ) • 1)
    (hadj : ∀ p k, K plane (-p) (k + p) = (K plane p k)ᴴ)
    (hcomm : ∀ p h k, K plane h (k + p) * K plane p k = K plane p (k + h) * K plane h k) :
    (∀ p k, chargeInclusiveSquare (K plane p k) = chargeInclusiveSquare (K plane p 0)) ∧
      ∀ᶠ p in 𝓝 (0 : ChargeSpatialMomentum), ∀ k, 0 < chargeInclusiveSquare (K plane p k) := by
  have hc (p k : ChargeSpatialMomentum) :
      chargeInclusiveSquare (K plane p k) = chargeInclusiveSquare (K plane p 0) := by
    rw [chargeInclusiveSquare_eq_trace, chargeInclusiveSquare_eq_trace]
    change (chargeGram K plane p k).trace.re = (chargeGram K plane p 0).trace.re
    rw [(chargeGram_hermitian K plane p k).trace_eq_sum_eigenvalues,
      (chargeGram_hermitian K plane p 0).trace_eq_sum_eigenvalues,
      commuting_local_charge_eigenvalues K plane hcont hq hzero hadj hcomm p k 0]
  have hct : Continuous (fun p => chargeInclusiveSquare (K plane p 0)) := by
    have hk : Continuous (fun p => K plane p 0) := hcont.comp (continuous_id.prodMk continuous_const)
    unfold chargeInclusiveSquare
    exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      Complex.continuous_normSq.comp ((continuous_apply j).comp ((continuous_apply i).comp hk))
  have hz : chargeInclusiveSquare (K plane 0 0) = (d : ℝ) * q ^ 2 := by
    rw [hzero]
    unfold chargeInclusiveSquare
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, mul_ite, mul_one, mul_zero]
    have h (i j : Fin d) : Complex.normSq (if i = j then (q : ℂ) else 0) =
        if i = j then q ^ 2 else 0 := by
      by_cases hij : i = j <;> simp [hij, Complex.normSq_apply, pow_two]
    simp [h]
  refine ⟨hc, ?_⟩
  have hpos : 0 < chargeInclusiveSquare (K plane 0 0) := by
    rw [hz]
    exact mul_pos (Nat.cast_pos.mpr hd) (sq_pos_of_ne_zero hq)
  have ht : ContinuousAt (fun p => chargeInclusiveSquare (K plane p 0)) 0 := hct.continuousAt
  filter_upwards [ht (Ioi_mem_nhds hpos)] with p hp k
  simpa only [hc] using hp

end UV
