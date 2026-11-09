import UV.MatrixPole
import UV.CertifiedRectifiableResidue
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Literal finite-matrix contour residues. The analytic numerator is built
from the actual adjugate and endpoint products, and the observable is the
actual nonsingular matrix inverse. Matrix norms throughout this file are
the Euclidean operator norms, including rectangular readout matrices. -/

noncomputable section
open Set Filter Metric Complex
open scoped Topology Matrix.Norms.L2Operator NNReal

namespace UV

section MatrixAnalytic

variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
  [DecidableEq m] [DecidableEq n] [DecidableEq l]

def matrixContourEntry (i : m) (j : n) : Matrix m n ℂ →L[ℂ] ℂ where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (continuous_apply j).comp (continuous_apply i)

omit [DecidableEq m] in
theorem matrixContour_entry_analyticOnNhd {F : ℂ → Matrix m n ℂ} {U : Set ℂ}
    (hF : AnalyticOnNhd ℂ F U) (i : m) (j : n) :
    AnalyticOnNhd ℂ (fun z => F z i j) U := by
  intro z hz
  exact ((matrixContourEntry i j).analyticAt (F z)).comp (hF z hz)

theorem matrixContour_analyticOnNhd_of_entries {F : ℂ → Matrix m n ℂ} {U : Set ℂ}
    (hF : ∀ i j, AnalyticOnNhd ℂ (fun z => F z i j) U) :
    AnalyticOnNhd ℂ F U := by
  have he : F = fun z => ∑ i : m, ∑ j : n, (F z i j) • Matrix.single i j (1:ℂ) := by
    funext z
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using Matrix.matrix_eq_sum_single (F z)
  rw [he]
  intro z hz
  apply Finset.analyticAt_fun_sum
  intro i _
  apply Finset.analyticAt_fun_sum
  intro j _
  exact (hF i j z hz).smul analyticAt_const

theorem matrixContour_mul_analyticOnNhd
    {F : ℂ → Matrix m n ℂ} {G : ℂ → Matrix n l ℂ} {U : Set ℂ}
    (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U) :
    AnalyticOnNhd ℂ (fun z => F z * G z) U := by
  apply matrixContour_analyticOnNhd_of_entries
  intro i j z hz
  simp only [Matrix.mul_apply]
  apply Finset.analyticAt_fun_sum
  intro k _
  exact (matrixContour_entry_analyticOnNhd hF i k z hz).mul
    (matrixContour_entry_analyticOnNhd hG k j z hz)

theorem matrixContour_det_analyticOnNhd {F : ℂ → Matrix n n ℂ} {U : Set ℂ}
    (hF : AnalyticOnNhd ℂ F U) : AnalyticOnNhd ℂ (fun z => (F z).det) U := by
  intro z hz
  apply matrix_det_analyticAt
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  exact matrixContour_entry_analyticOnNhd hF i j z hz

theorem matrixContour_adjugate_analyticOnNhd {F : ℂ → Matrix n n ℂ} {U : Set ℂ}
    (hF : AnalyticOnNhd ℂ F U) : AnalyticOnNhd ℂ (fun z => (F z).adjugate) U := by
  apply matrixContour_analyticOnNhd_of_entries
  intro i j z hz
  have hOld := matrix_adjugate_analyticAt (K:=F) (p:=z)
    (AnalyticAt.pi fun a => AnalyticAt.pi fun b => matrixContour_entry_analyticOnNhd hF a b z hz)
  exact analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hOld i) j

end MatrixAnalytic

variable {n i o : Type*} [Fintype n] [DecidableEq n]
  [Fintype i] [DecidableEq i] [Fintype o] [DecidableEq o]

theorem matrixContour_numerator_analyticOnNhd
    {K : ℂ → Matrix n n ℂ} {Lout : ℂ → Matrix o n ℂ} {Lin : ℂ → Matrix n i ℂ}
    {U : Set ℂ} (hK : AnalyticOnNhd ℂ K U)
    (hLout : AnalyticOnNhd ℂ Lout U) (hLin : AnalyticOnNhd ℂ Lin U) :
    AnalyticOnNhd ℂ (matrixObservableAdjugateNumerator K Lout Lin) U :=
  matrixContour_mul_analyticOnNhd
    (matrixContour_mul_analyticOnNhd hLout (matrixContour_adjugate_analyticOnNhd hK)) hLin

/-- The actual finite-matrix inverse observable has its actual residue on a
certified positive-winding Lipschitz contour. Its numerator is constructed
from the determinant and adjugate, and no residue formula is a premise. -/
theorem simplyConnectedContour_matrix_observable_residue
    {a p : ℂ} {κ : ℝ≥0} {U : Set ℂ} [SimplyConnectedSpace U]
    {K : ℂ → Matrix n n ℂ} {Lout : ℂ → Matrix o n ℂ} {Lin : ℂ → Matrix n i ℂ}
    (γ : Path a a) (hLip : LipschitzWith κ γ.extend) (hU : IsOpen U)
    (hmap : MapsTo γ.extend (Icc (0:ℝ) 1) U)
    (havoid : ∀ t ∈ Icc (0:ℝ) 1, γ.extend t ≠ p)
    (hpos : lipschitzContourWinding γ havoid = 1) (hp : p ∈ U)
    (hK : AnalyticOnNhd ℂ K U) (hLout : AnalyticOnNhd ℂ Lout U)
    (hLin : AnalyticOnNhd ℂ Lin U)
    (hzero : (K p).det = 0) (hderiv : deriv (fun z => (K z).det) p ≠ 0)
    (honly : ∀ z ∈ U, z ≠ p → (K z).det ≠ 0) :
    (2*Real.pi*Complex.I:ℂ)⁻¹ • parametrizedContourIntegral (matrixInverseObservable K Lout Lin) γ =
      simplePoleResidue (matrixInverseObservable K Lout Lin) p := by
  have he : matrixInverseObservable K Lout Lin =
      fun z => ((K z).det)⁻¹ • matrixObservableAdjugateNumerator K Lout Lin z :=
    funext (matrix_observable_adjugate_quotient K Lout Lin)
  rw [he]
  exact simplyConnectedContour_simple_denominator_residue γ hLip hU hmap havoid hpos hp
    (matrixContour_det_analyticOnNhd hK) (matrixContour_numerator_analyticOnNhd hK hLout hLin)
    hzero hderiv honly

end UV
