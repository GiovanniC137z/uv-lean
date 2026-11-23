import UV.ContinueCompressedModesShell
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! The negative log-modulus determinant of a normalized affine Dirac
pencil has the signed cyclic trace coefficients at every positive
electric order. This algebraic identification is made on arbitrary
finite sets of Fourier-spin states. -/

noncomputable section

open Matrix Filter Polynomial
open scoped Topology Matrix.Norms.L2Operator Polynomial

namespace UV

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def compressedPencil (A : Matrix κ κ ℂ) (t : ℝ) := 1 + (t:ℂ) • A

def compressedPencilLog (A : Matrix κ κ ℂ) (t : ℝ) : ℝ := -Real.log ‖(compressedPencil A t).det‖

def compressedPencilResponse (A : Matrix κ κ ℂ) (t : ℝ) := Ring.inverse (compressedPencil A t) * A

private theorem compressed_det_origin (A : Matrix κ κ ℂ) :
    HasDerivAt (fun z : ℂ => (1+z • A).det) A.trace 0 := by
  let P := (1+(X : ℂ[X]) • A.map C).det
  have hp : ∀ z, P.eval z = (1+z • A).det := by
    intro z
    simp [P,eval_det,←smul_eq_mul_diagonal]
  have hd := P.hasDerivAt (0:ℂ)
  rw [show P.derivative.eval 0 = _ from Matrix.derivative_det_one_add_X_smul A] at hd
  simpa only [←hp] using hd

private theorem compressed_pencil_log_deriv (A : Matrix κ κ ℂ) {t : ℝ}
    (ht : (compressedPencil A t).det ∈ Complex.slitPlane) :
    HasDerivAt (compressedPencilLog A) (-(compressedPencilResponse A t).trace.re) t := by
  let B := compressedPencil A t
  have hu : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr (Complex.slitPlane_ne_zero ht))
  let M := compressedPencilResponse A t
  have hc (z : ℂ) : (1+z • A).det = B.det*(1+(z-(t:ℂ)) • M).det := by
    rw [←Matrix.det_mul,mul_add,mul_one,Matrix.mul_smul,show B*M=A by
      change B*(Ring.inverse B*A) = A
      rw [←mul_assoc,Ring.mul_inverse_cancel _ hu,one_mul]]
    congr 1
    change 1+z • A = (1+(t:ℂ) • A)+(z-(t:ℂ)) • A
    rw [sub_smul]
    abel
  have hdet : HasDerivAt (fun z : ℂ => (1+z • A).det) (B.det*M.trace) (t:ℂ) := by
    simp_rw [hc]
    exact ((by simpa only [sub_self] using compressed_det_origin M : HasDerivAt _ M.trace ((t:ℂ)-(t:ℂ))).comp_sub_const _ _).const_mul _
  have hz : B.det ≠ 0 := Complex.slitPlane_ne_zero ht
  have hc' := hdet.clog ht
  change HasDerivAt _ ((B.det*M.trace)/B.det) (t:ℂ) at hc'
  rw [mul_div_cancel_left₀ _ hz] at hc'
  simpa only [compressedPencilLog,compressedPencil,Complex.log_re,Pi.neg_def] using hc'.real_of_complex.neg

private theorem compressed_response_deriv (A : Matrix κ κ ℂ) {t : ℝ} (hu : IsUnit (compressedPencil A t)) :
    HasDerivAt (compressedPencilResponse A) (-(compressedPencilResponse A t)^2) t := by
  let B := compressedPencil A t
  have hi : HasFDerivAt Ring.inverse _ B := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
  have hp : HasDerivAt (compressedPencil A) A t := by
    change HasDerivAt (fun t : ℝ => 1+(t:ℂ) • A) A t
    apply HasDerivAt.const_add
    simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,one_smul] using (Complex.ofRealCLM.hasDerivAt (x := t)).smul_const A
  have h := ((hi.comp_hasDerivAt t hp).mul_const A)
  simpa [compressedPencilResponse,B,←Ring.inverse_unit hu.unit,hu.unit_spec,sq,mul_assoc] using h

private theorem compressed_response_power (A : Matrix κ κ ℂ) {t : ℝ} (hu : IsUnit (compressedPencil A t)) (n : ℕ) :
    HasDerivAt (fun s => compressedPencilResponse A s ^ n)
      (-(n : ℝ) • (compressedPencilResponse A t)^(n+1)) t := by
  induction n with
  | zero => simpa using hasDerivAt_const t (1:Matrix κ κ ℂ)
  | succ n ih =>
    simp only [pow_succ _ (n+1)]
    have h := ih.mul (compressed_response_deriv A hu)
    convert h using 1
    let M := compressedPencilResponse A t
    change -((n+1:ℕ):ℝ) • (M^(n+1)*M) = (-(n:ℝ) • M^(n+1))*M + M^n * (-M^2)
    rw [mul_neg,smul_mul_assoc,←pow_add,←pow_succ]
    simp only [Nat.cast_add,Nat.cast_one,neg_add,add_smul,neg_smul,one_smul]

private theorem compressed_trace_power_deriv (A : Matrix κ κ ℂ) {t : ℝ} (hu : IsUnit (compressedPencil A t)) (n : ℕ) :
    HasDerivAt (fun s => ((compressedPencilResponse A s)^n).trace.re)
      (-(n:ℝ)*((compressedPencilResponse A t)^(n+1)).trace.re) t := by
  let φ := (Matrix.traceLinearMap κ ℝ ℂ).toContinuousLinearMap
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (φ.hasFDerivAt.comp_hasDerivAt t (compressed_response_power A hu n))
  simpa [φ,Matrix.trace_smul] using h

theorem compressed_logdet_cyclic_coefficient (A : Matrix κ κ ℂ) (n : ℕ) :
    iteratedDeriv (n+1) (compressedPencilLog A) 0 / (n+1).factorial =
      (-1:ℝ)^(n+1)*((A^(n+1)).trace.re)/(n+1) := by
  have hc : Continuous (fun t => (compressedPencil A t).det) := by
    apply Continuous.matrix_det
    exact continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
  have hh : ∀ᶠ t : ℝ in 𝓝 0, (compressedPencil A t).det ∈ Complex.slitPlane :=
    hc.continuousAt.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds (by simp [compressedPencil]))
  have he (j : ℕ) : iteratedDeriv (j+1) (compressedPencilLog A) =ᶠ[𝓝 (0:ℝ)]
      fun t => (-1:ℝ)^(j+1)*j.factorial*((compressedPencilResponse A t)^(j+1)).trace.re := by
    induction j with
    | zero =>
      filter_upwards [hh] with t ht
      simpa [iteratedDeriv_succ] using (compressed_pencil_log_deriv A ht).deriv
    | succ j ih =>
      rw [iteratedDeriv_succ]
      filter_upwards [ih.deriv,hh] with t ht hu
      rw [ht]
      have hd := compressed_trace_power_deriv A ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (Complex.slitPlane_ne_zero hu))) (j+1)
      rw [(hd.const_mul _).deriv,Nat.factorial_succ,pow_succ (-1:ℝ) (j+1)]
      push_cast
      ring
  rw [(he n).eq_of_nhds]
  simp only [compressedPencilResponse,compressedPencil,Complex.ofReal_zero,zero_smul,add_zero,Ring.inverse_one,one_mul,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  field_simp

end UV
