import UV.PoleCertificates
import UV.MatrixAdjugate
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Actual finite-matrix inverse and observable simple-pole coefficients.
Local pole numerators are constructed from the determinant's divided
slope and the analytic adjugate, rather than supplied as residue data. -/

noncomputable section
open Complex Filter Set Metric
open scoped Topology Matrix.Norms.Elementwise

namespace UV

/-- A nonzero scalar derivative constructs a disk with no other denominator
zero; analyticity constructs the holomorphic numerator on that same disk. -/
theorem local_simple_denominator_pole {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℂ Z] [CompleteSpace Z] {k : ℂ → ℂ} {n : ℂ → Z} {p d : ℂ}
    (hk : AnalyticAt ℂ k p) (hn : AnalyticAt ℂ n p)
    (hkzero : k p=0) (hd : HasDerivAt k d p) (hdne : d≠0) :
    ∃ r : ℝ, 0<r ∧
      DifferentiableOn ℂ k (closedBall p r) ∧
      DifferentiableOn ℂ n (closedBall p r) ∧
      (∀ z ∈ closedBall p r, z≠p → k z≠0) ∧
      DifferentiableOn ℂ (fun z => (dslope k p z)⁻¹ • n z) (closedBall p r) ∧
      (∀ z ∈ closedBall p r, z≠p →
        (k z)⁻¹ • n z = (z-p)⁻¹ • ((dslope k p z)⁻¹ • n z)) ∧
      simplePoleResidue (fun z => (k z)⁻¹ • n z) p = d⁻¹ • n p := by
  have hOnly : ∀ᶠ z in 𝓝 p, z≠p → k z≠0 := by
    simpa only [mem_compl_iff, mem_singleton_iff] using
      (eventually_nhdsWithin_iff.mp (hd.eventually_ne hdne : ∀ᶠ z in 𝓝[≠] p, k z≠0))
  have hke : ∀ᶠ z in 𝓝 p, AnalyticAt ℂ k z := (isOpen_analyticAt ℂ k).mem_nhds hk
  have hne : ∀ᶠ z in 𝓝 p, AnalyticAt ℂ n z := (isOpen_analyticAt ℂ n).mem_nhds hn
  obtain ⟨R,hR,hball⟩ := Metric.eventually_nhds_iff.mp (hke.and (hne.and hOnly))
  have hhalf : 0<R/2 := by positivity
  have hdata (z : ℂ) (hz : z∈closedBall p (R/2)) :=
    hball (lt_of_le_of_lt hz (by linarith : R/2<R))
  have hkD : DifferentiableOn ℂ k (closedBall p (R/2)) :=
    fun z hz => (hdata z hz).1.differentiableAt.differentiableWithinAt
  have hnD : DifferentiableOn ℂ n (closedBall p (R/2)) :=
    fun z hz => (hdata z hz).2.1.differentiableAt.differentiableWithinAt
  have hOnlyD : ∀ z∈closedBall p (R/2), z≠p → k z≠0 :=
    fun z hz => (hdata z hz).2.2
  have hdp : deriv k p≠0 := by rw [hd.deriv]; exact hdne
  have hp : p∈ball p (R/2) := mem_ball_self hhalf
  obtain ⟨hG,hf⟩ := simple_denominator_pole_numerator hp hkD hnD hkzero hdp hOnlyD
  refine ⟨R/2,hhalf,hkD,hnD,hOnlyD,hG,hf,?_⟩
  simpa only [hd.deriv] using simple_denominator_residue hp hkD hnD hkzero hdp hOnlyD

variable {n i o : Type*} [Fintype n] [DecidableEq n] [Fintype i] [Fintype o]

/-- The numerator of the literal finite-channel observable. -/
def matrixObservableAdjugateNumerator (K : ℂ → Matrix n n ℂ)
    (Lout : ℂ → Matrix o n ℂ) (Lin : ℂ → Matrix n i ℂ) (z : ℂ) : Matrix o i ℂ :=
  Lout z * (K z).adjugate * Lin z

/-- The actual observable evaluated using the finite matrix inverse. -/
def matrixInverseObservable (K : ℂ → Matrix n n ℂ)
    (Lout : ℂ → Matrix o n ℂ) (Lin : ℂ → Matrix n i ℂ) (z : ℂ) : Matrix o i ℂ :=
  Lout z * (K z)⁻¹ * Lin z

/-- The matrix inverse is the actual adjugate quotient, including its
library-defined value at singular matrices; residues use punctured limits. -/
theorem matrix_inverse_adjugate_quotient (K : ℂ → Matrix n n ℂ) (z : ℂ) :
    (K z)⁻¹ = ((K z).det)⁻¹ • (K z).adjugate := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv]

omit [Fintype i] [Fintype o] in
/-- Scalar determinant division commutes with both actual endpoint products. -/
theorem matrix_observable_adjugate_quotient (K : ℂ → Matrix n n ℂ)
    (Lout : ℂ → Matrix o n ℂ) (Lin : ℂ → Matrix n i ℂ) (z : ℂ) :
    matrixInverseObservable K Lout Lin z =
      ((K z).det)⁻¹ • matrixObservableAdjugateNumerator K Lout Lin z := by
  unfold matrixInverseObservable matrixObservableAdjugateNumerator
  rw [matrix_inverse_adjugate_quotient, Matrix.mul_smul, Matrix.smul_mul]

/-- A simple determinant zero constructs a local holomorphic matrix-pole
numerator and identifies the actual inverse residue. -/
theorem matrix_inverse_simple_pole {K : ℂ → Matrix n n ℂ} {p d : ℂ}
    (hK : AnalyticAt ℂ K p) (hzero : (K p).det=0)
    (hd : HasDerivAt (fun z => (K z).det) d p) (hdne : d≠0) :
    ∃ r : ℝ, 0<r ∧
      DifferentiableOn ℂ
        (fun z => (dslope (fun w => (K w).det) p z)⁻¹ • (K z).adjugate)
        (closedBall p r) ∧
      (∀ z∈closedBall p r, z≠p → (K z)⁻¹ = (z-p)⁻¹ •
        ((dslope (fun w => (K w).det) p z)⁻¹ • (K z).adjugate)) ∧
      simplePoleResidue (fun z => (K z)⁻¹) p = d⁻¹ • (K p).adjugate := by
  obtain ⟨r,hr,_,_,_,hG,hf,hres⟩ := local_simple_denominator_pole
    (matrix_det_analyticAt hK) (matrix_adjugate_analyticAt hK) hzero hd hdne
  refine ⟨r,hr,hG,?_,?_⟩
  · intro z hz hzp
    rw [matrix_inverse_adjugate_quotient]
    exact hf z hz hzp
  · have he : (fun z => (K z)⁻¹) = fun z => ((K z).det)⁻¹ • (K z).adjugate :=
      funext (matrix_inverse_adjugate_quotient K)
    rw [he]
    exact hres

/-- Observable endpoints may annihilate the matrix-pole coefficient. The
formula derives the actual residue without requiring it to be nonzero. -/
theorem matrix_observable_simple_pole {K : ℂ → Matrix n n ℂ}
    {Lout : ℂ → Matrix o n ℂ} {Lin : ℂ → Matrix n i ℂ} {p d : ℂ}
    (hK : AnalyticAt ℂ K p) (hLout : AnalyticAt ℂ Lout p) (hLin : AnalyticAt ℂ Lin p)
    (hzero : (K p).det=0) (hd : HasDerivAt (fun z => (K z).det) d p) (hdne : d≠0) :
    ∃ r : ℝ, 0<r ∧
      DifferentiableOn ℂ
        (fun z => (dslope (fun w => (K w).det) p z)⁻¹ •
          matrixObservableAdjugateNumerator K Lout Lin z) (closedBall p r) ∧
      (∀ z∈closedBall p r, z≠p → matrixInverseObservable K Lout Lin z =
        (z-p)⁻¹ • ((dslope (fun w => (K w).det) p z)⁻¹ •
          matrixObservableAdjugateNumerator K Lout Lin z)) ∧
      simplePoleResidue (matrixInverseObservable K Lout Lin) p =
        d⁻¹ • (Lout p * (K p).adjugate * Lin p) ∧
      (2*Real.pi*Complex.I:ℂ)⁻¹ • circleIntegral (matrixInverseObservable K Lout Lin) p r =
        d⁻¹ • (Lout p * (K p).adjugate * Lin p) := by
  have hn : AnalyticAt ℂ (matrixObservableAdjugateNumerator K Lout Lin) p :=
    matrix_mul_analyticAt (matrix_mul_analyticAt hLout (matrix_adjugate_analyticAt hK)) hLin
  obtain ⟨r,hr,_,_,_,hG,hf,hres⟩ := local_simple_denominator_pole
    (matrix_det_analyticAt hK) hn hzero hd hdne
  have he : matrixInverseObservable K Lout Lin = fun z =>
      ((K z).det)⁻¹ • matrixObservableAdjugateNumerator K Lout Lin z :=
    funext (matrix_observable_adjugate_quotient K Lout Lin)
  have hres' : simplePoleResidue (matrixInverseObservable K Lout Lin) p =
      d⁻¹ • (Lout p * (K p).adjugate * Lin p) := by
    rw [he]
    exact hres
  have hf' : ∀ z∈closedBall p r, z≠p → matrixInverseObservable K Lout Lin z =
      (z-p)⁻¹ • ((dslope (fun w => (K w).det) p z)⁻¹ •
        matrixObservableAdjugateNumerator K Lout Lin z) := by
    intro z hz hzp
    rw [he]
    exact hf z hz hzp
  refine ⟨r,hr,hG,hf',hres',?_⟩
  rw [simplePole_circle_integral (mem_ball_self hr) hG hf', hres']

/-- A vanishing endpoint contraction gives a vanishing actual observable
residue even when the internal determinant has a simple zero. -/
theorem matrix_observable_residue_zero_of_contraction_zero {K : ℂ → Matrix n n ℂ}
    {Lout : ℂ → Matrix o n ℂ} {Lin : ℂ → Matrix n i ℂ} {p d : ℂ}
    (hK : AnalyticAt ℂ K p) (hLout : AnalyticAt ℂ Lout p) (hLin : AnalyticAt ℂ Lin p)
    (hzero : (K p).det=0) (hd : HasDerivAt (fun z => (K z).det) d p) (hdne : d≠0)
    (hcontract : Lout p * (K p).adjugate * Lin p = 0) :
    simplePoleResidue (matrixInverseObservable K Lout Lin) p = 0 := by
  obtain ⟨_,_,_,_,hres,_⟩ := matrix_observable_simple_pole hK hLout hLin hzero hd hdne
  rw [hres,hcontract,smul_zero]

/-- The inverse-pole coefficient lies in the right and left null spaces of
the singular kinetic matrix. No null-vector normalization is presumed. -/
theorem matrix_inverse_residue_annihilated {K : ℂ → Matrix n n ℂ} {p d : ℂ}
    (hK : AnalyticAt ℂ K p) (hzero : (K p).det=0)
    (hd : HasDerivAt (fun z => (K z).det) d p) (hdne : d≠0) :
    K p * simplePoleResidue (fun z => (K z)⁻¹) p = 0 ∧
      simplePoleResidue (fun z => (K z)⁻¹) p * K p = 0 := by
  obtain ⟨_,_,_,_,hres⟩ := matrix_inverse_simple_pole hK hzero hd hdne
  rw [hres, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_adjugate, Matrix.adjugate_mul,
    hzero,zero_smul,smul_zero]
  exact ⟨rfl,rfl⟩

end UV
