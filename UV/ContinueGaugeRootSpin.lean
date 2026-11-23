import UV.ContinueGaugeRootHessian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-! Charged-root spin matrix of the five-component adjoint one-form.
The two circular polarization vectors are normalized, and the normal
component is one of the three unshifted directions. -/

noncomputable section
open Matrix
open scoped Matrix ComplexConjugate

namespace UV.RootMagnetic

private def rootUnitScale : ℂ := (Real.sqrt (1/2) : ℝ)

private theorem rootUnitScale_sq : rootUnitScale^2 = (1/2 : ℂ) := by
  unfold rootUnitScale
  rw [←Complex.ofReal_pow,Real.sq_sqrt (by norm_num)]
  norm_num

private theorem rootUnitScale_conj : conj rootUnitScale = rootUnitScale := Complex.conj_ofReal _

private theorem rootUnitScale_star : star rootUnitScale = rootUnitScale := Complex.conj_ofReal _

/-- Two magnetic coordinates and three unshifted coordinates. The third
unshifted coordinate is the normal polarization. -/
abbrev RootPolarization := Fin 2 ⊕ Fin 3

private def circularPair : Matrix (Fin 2) (Fin 2) ℂ :=
  !![rootUnitScale,rootUnitScale; Complex.I*rootUnitScale,-Complex.I*rootUnitScale]

private def spinPair (b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0,-2*Complex.I*b;2*Complex.I*b,0]

def rootCircularBasis : Matrix RootPolarization RootPolarization ℂ := Matrix.fromBlocks circularPair 0 0 1
def rootCartanSpin (b : ℝ) : Matrix RootPolarization RootPolarization ℂ := Matrix.fromBlocks (spinPair b) 0 0 0
def rootSpinShifts (b : ℝ) : RootPolarization → ℂ := Sum.elim ![2*(b:ℂ),-2*(b:ℂ)] (fun _ => 0)

private theorem circularPair_unitary :
    circularPair.conjTranspose*circularPair = 1 ∧ circularPair*circularPair.conjTranspose = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [circularPair,Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply,rootUnitScale_star,rootUnitScale_conj,Matrix.one_apply] <;>
    ring_nf <;> norm_num [Complex.I_sq,rootUnitScale_sq,rootUnitScale_conj]

theorem rootCircularBasis_unitary :
    rootCircularBasis.conjTranspose * rootCircularBasis = 1 ∧
      rootCircularBasis * rootCircularBasis.conjTranspose = 1 := by
  have h1 : (Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 (1 : Matrix (Fin 3) (Fin 3) ℂ)) = 1 := by
    ext (i|i) (j|j) <;> simp [Matrix.one_apply,Matrix.fromBlocks]
  simp [rootCircularBasis,Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply,
    circularPair_unitary.1,circularPair_unitary.2,h1]

private theorem spinPair_eigenframe (b : ℝ) : spinPair b*circularPair =
    circularPair*Matrix.diagonal ![2*(b:ℂ),-2*(b:ℂ)] := by
  ext i j
  rw [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> norm_num [spinPair,circularPair,Matrix.mul_apply,Fin.sum_univ_two] <;>
    ring_nf <;> norm_num [Complex.I_sq]

theorem rootCartanSpin_eigenframe (b : ℝ) : rootCartanSpin b * rootCircularBasis =
    rootCircularBasis * Matrix.diagonal (rootSpinShifts b) := by
  have h : Matrix.diagonal (rootSpinShifts b) = Matrix.fromBlocks (Matrix.diagonal ![2*(b:ℂ),-2*(b:ℂ)])
      0 0 (0 : Matrix (Fin 3) (Fin 3) ℂ) := by
    ext (i|i) (j|j) <;> simp [rootSpinShifts,Matrix.fromBlocks,Matrix.diagonal_apply]
  simp [h,rootCartanSpin,rootCircularBasis,Matrix.fromBlocks_multiply,spinPair_eigenframe]

private def rootBasisUnit : (Matrix RootPolarization RootPolarization ℂ)ˣ :=
  ⟨rootCircularBasis,rootCircularBasis.conjTranspose,rootCircularBasis_unitary.2,rootCircularBasis_unitary.1⟩

theorem rootCartanSpin_heat_trace (b t : ℝ) :
    Matrix.trace (NormedSpace.exp ℂ ((-(t:ℂ)) • rootCartanSpin b)) =
      Complex.exp (-2*(b:ℂ)*t) + Complex.exp (2*(b:ℂ)*t) + 3 := by
  have he : rootCircularBasis * Matrix.diagonal (rootSpinShifts b) * rootCircularBasis.conjTranspose = rootCartanSpin b := by
    rw [←rootCartanSpin_eigenframe,Matrix.mul_assoc,rootCircularBasis_unitary.2,mul_one]
  have hconj : (-(t:ℂ)) • rootCartanSpin b = (rootBasisUnit : Matrix RootPolarization RootPolarization ℂ) *
      Matrix.diagonal (fun i => -(t:ℂ)*rootSpinShifts b i) * (↑rootBasisUnit⁻¹ : Matrix RootPolarization RootPolarization ℂ) := by
    rw [←he,←Matrix.smul_mul,←Matrix.mul_smul,←Matrix.diagonal_smul]
    rfl
  rw [hconj,Matrix.exp_units_conj,Matrix.trace_units_conj,Matrix.exp_diagonal]
  simp only [Matrix.trace_diagonal,Fintype.sum_sum_type,Fin.sum_univ_two,Fin.sum_univ_three,Pi.coe_exp,
    ←Complex.exp_eq_exp_ℂ,rootSpinShifts]
  simp
  ring_nf

end UV.RootMagnetic
