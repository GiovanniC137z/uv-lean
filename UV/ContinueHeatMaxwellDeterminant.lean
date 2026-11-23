import UV.ContinueHeatMaxwellNativeTrace
import UV.ContinueCompressedModesDeterminant
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! The mixed two-source variation of a normalized finite Fourier-spin
determinant. The Hessian at zero uses only its specified first marks
and its direct mixed mark. -/

noncomputable section
namespace UV.HeatMaxwell
open Filter Matrix
open scoped Topology Matrix.Norms.L2Operator RealInnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private abbrev Mat (ι : Type*) := Matrix ι ι ℂ

def heatTwoSourceMatrix (A B C : Mat ι) (s t : ℝ) : Mat ι :=
  compressedPencil A s + (t:ℂ) • (B+(s:ℂ) • C)

def heatTwoSourceLog (A B C : Mat ι) (s t : ℝ) : ℝ :=
  -Real.log ‖(heatTwoSourceMatrix A B C s t).det‖

private theorem heat_pencil_deriv (A : Mat ι) (t : ℝ) : HasDerivAt (compressedPencil A) A t := by
  apply HasDerivAt.const_add
  simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,one_smul] using
    (Complex.ofRealCLM.hasDerivAt (x:=t)).smul_const A

private theorem heat_pencil_unit_near_zero (A : Mat ι) : ∀ᶠ t : ℝ in 𝓝 0, IsUnit (compressedPencil A t) := by
  have hc : Continuous (fun t => (compressedPencil A t).det) := by
    apply Continuous.matrix_det
    exact continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
  have hh : ∀ᶠ t : ℝ in 𝓝 0, (compressedPencil A t).det ∈ Complex.slitPlane :=
    hc.continuousAt.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds (by simp [compressedPencil]))
  exact hh.mono fun t ht => (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (Complex.slitPlane_ne_zero ht))

private theorem heat_mixed_inner (A B C : Mat ι) (s : ℝ) (hs : IsUnit (compressedPencil A s)) :
    deriv (heatTwoSourceLog A B C s) 0 = -((Ring.inverse (compressedPencil A s))*(B+(s:ℂ) • C)).trace.re := by
  let D := compressedPencil A s
  let K := Ring.inverse D*(B+(s:ℂ) • C)
  have hfac (t : ℝ) : heatTwoSourceMatrix A B C s t = D*compressedPencil K t := by
    change D+(t:ℂ) • (B+(s:ℂ) • C)=D*(1+(t:ℂ) • (Ring.inverse D*(B+(s:ℂ) • C)))
    rw [mul_add,mul_one,mul_smul_comm,←mul_assoc,Ring.mul_inverse_cancel D hs,one_mul]
  have he : heatTwoSourceLog A B C s =ᶠ[𝓝 0] (fun t => -Real.log ‖D.det‖+compressedPencilLog K t) := by
    filter_upwards [heat_pencil_unit_near_zero K] with t ht
    have h1 : D.det≠0 := (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hs))
    have h2 : (compressedPencil K t).det≠0 := (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp ht))
    simp only [heatTwoSourceLog,hfac,Matrix.det_mul,norm_mul,Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2),
      neg_add,compressedPencilLog]
  rw [he.deriv_eq,deriv_const_add]
  simpa only [Nat.zero_add,iteratedDeriv_one,Nat.factorial_one,Nat.cast_one,Nat.cast_zero,div_one,pow_one,zero_add,neg_one_mul]
    using compressed_logdet_cyclic_coefficient K 0

/-- The bubble enters with a plus and its direct contact with a minus
in the Hessian of the charged negative log-modulus determinant. -/
theorem heat_two_source_mixed_hessian (A B C : Mat ι) :
    deriv (fun s => deriv (heatTwoSourceLog A B C s) 0) 0 = ((A*B).trace-C.trace).re := by
  have he := (heat_pencil_unit_near_zero A).mono (fun t ht => heat_mixed_inner A B C t ht)
  have hi : HasFDerivAt Ring.inverse _ (1:Mat ι) := hasFDerivAt_ringInverse (𝕜:=ℝ) (1:(Mat ι)ˣ)
  have hA : HasDerivAt (fun t => Ring.inverse (compressedPencil A t)) (-A) 0 := by
    have h0 : compressedPencil A 0=1 := by simp [compressedPencil]
    have hp : HasFDerivAt Ring.inverse _ (compressedPencil A 0) := h0.symm ▸ hi
    simpa using hp.comp_hasDerivAt 0 (heat_pencil_deriv A 0)
  have hc : HasDerivAt (fun t : ℝ => B+(t:ℂ) • C) C 0 := by
    apply HasDerivAt.const_add
    simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,one_smul] using (Complex.ofRealCLM.hasDerivAt (x:=(0:ℝ))).smul_const C
  let τ := (Matrix.traceLinearMap ι ℝ ℂ).toContinuousLinearMap
  have H := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (τ.hasFDerivAt.comp_hasDerivAt 0 (hA.mul hc))).neg
  rw [Filter.EventuallyEq.deriv_eq he]
  convert H.deriv using 1
  simp [τ,compressedPencil]
  ring

omit [DecidableEq ι] in
private theorem heat_trace_blocks {j : Type*} [Fintype j] (A : Mat ι) (B : Matrix ι j ℂ) (C : Matrix j ι ℂ) (D : Mat j) :
    (Matrix.fromBlocks A B C D).trace=A.trace+D.trace := by
  simp only [Matrix.trace,Matrix.diag,Fintype.sum_sum_type,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₂₂]

abbrev HeatSpinSlots := (Fin 4 ⊕ Fin 4) ⊕ Fin 4
def heatFirstBlock (U : DiracMatrix) : Mat HeatSpinSlots :=
  Matrix.fromBlocks (Matrix.fromBlocks 0 U 0 0) 0 0 0
def heatReturnBlock (V : DiracMatrix) : Mat HeatSpinSlots :=
  Matrix.fromBlocks (Matrix.fromBlocks 0 0 V 0) 0 0 0
def heatContactBlock (W : DiracMatrix) : Mat HeatSpinSlots :=
  Matrix.fromBlocks 0 0 0 W

/-- The forward and return transfers and the zero-transfer contact
occupy the actual normalized Fourier spin blocks of the two-mark variation. -/
theorem heat_native_determinant_hessian
    (U : UV.SectorPlane.EuclideanPlaneMomentum ≃ₗᵢ[ℝ] DiracMomentum)
    (m : ℝ) (k : UV.SectorPlane.EuclideanPlaneMomentum) (t : ℝ) :
    let p := U (heatSymbol (k+(-t/2) • UV.RelativeSoft.softLongitudinal.val))
    let q := U (heatSymbol (k+(t/2) • UV.RelativeSoft.softLongitudinal.val))
    let h := U (heatSymbol k)
    let v := Complex.I • diracSlash (U (heatFirstChord k t))
    let w := Complex.I • diracSlash (U (heatContactChord k t))
    deriv (fun s => deriv (heatTwoSourceLog
      (heatFirstBlock (freeDiracPropagator m p*v)) (heatReturnBlock (freeDiracPropagator m q*v))
      (heatContactBlock (freeDiracPropagator m h*w)) s) 0) 0 = 4*heatNativeResponse m k t := by
  dsimp only
  rw [heat_two_source_mixed_hessian]
  simp only [heatFirstBlock,heatReturnBlock,heatContactBlock,Matrix.fromBlocks_multiply,
    heat_trace_blocks,Matrix.zero_mul,Matrix.mul_zero,zero_add,add_zero,Matrix.trace_zero]
  exact heat_native_response_trace U m k t

end UV.HeatMaxwell
