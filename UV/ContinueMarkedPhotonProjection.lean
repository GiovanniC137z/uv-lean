import UV.MarkedPhotonMonomial
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Transport the marked-source trace to an arbitrary finite covariance
matrix and a literal multilinear interaction on its physical test fields.
The test vectors may already include matter and boundary integrations. -/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators Matrix RealInnerProductSpace

namespace UV.MarkedPhoton

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [AddCommGroup F] [Module ℝ F]

private def slotMultiplicity {r : ℕ} (a : Fin r → ι) (i : ι) : ℕ := (Finset.univ.filter (fun j => a j=i)).card

private theorem slotMultiplicity_sum {r : ℕ} (a : Fin r → ι) : ∑ i, slotMultiplicity a i = r := by
  have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin r)) Finset.univ a
  simpa [slotMultiplicity] using h

private theorem slot_product {r : ℕ} (a : Fin r → ι) (x : ι → ℝ) :
    ∏ j, x (a j) = monomial (slotMultiplicity a) x := by
  have h := Finset.prod_fiberwise' (Finset.univ : Finset (Fin r)) a x
  simpa [monomial,slotMultiplicity] using h.symm

/-- Expand a multilinear common source in the actual finite test vectors.
No basis, rank, independence or positivity is required of the field
insertion vectors. -/
theorem multilinear_test_polynomial {r : ℕ} (L : MultilinearMap ℝ (fun _ : Fin r => F) ℝ)
    (v : ι → F) (x : ι → ℝ) :
    L (fun _ => ∑ i, x i • v i) = photonPolynomial Finset.univ (fun a : Fin r → ι => L (fun j => v (a j))) slotMultiplicity x := by
  rw [L.map_sum (fun (_ : Fin r) i => x i • v i)]
  unfold photonPolynomial
  apply Finset.sum_congr rfl
  intro a _
  rw [L.map_smul_univ (fun j => x (a j)) (fun j => v (a j)),smul_eq_mul,slot_product,mul_comm]

private theorem projection_coordinate_trace {r : ℕ} (L : MultilinearMap ℝ (fun _ : Fin r => F) ℝ)
    (v : ι → F) (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) :
    let V := fun x : ι → ℝ => L (fun _ => ∑ i, x i • v i)
    (Matrix.diagonal d * measuredHessian d V).trace = r * ∫ x, V x ∂coordinateLaw d := by
  have he := funext (multilinear_test_polynomial L v)
  dsimp only
  rw [he]
  apply marked_polynomial_trace d hd _ _ _ r
  exact fun a _ => slotMultiplicity_sum a

/-- Raw coordinates in the physical finite test chart from the eigenmode
coordinates of a prescribed positive semidefinite covariance matrix. -/
def photonProjectionLaw (D : Matrix ι ι ℝ) (hD : D.PosSemidef) : Measure (ι → ℝ) :=
  (coordinateLaw hD.1.eigenvalues).map (Matrix.mulVec (hD.1.eigenvectorUnitary : Matrix ι ι ℝ))

def physicalProjectedSource {r : ℕ} (L : MultilinearMap ℝ (fun _ : Fin r => F) ℝ) (v : ι → F)
    (x : ι → ℝ) := L (fun _ => ∑ i, x i • v i)

omit [DecidableEq ι] in
private theorem projected_source_change {r : ℕ} (L : MultilinearMap ℝ (fun _ : Fin r => F) ℝ) (v : ι → F)
    (U : Matrix ι ι ℝ) (x : ι → ℝ) :
    physicalProjectedSource L v (U *ᵥ x) = physicalProjectedSource L (fun j => ∑ i, U i j • v i) x := by
  unfold physicalProjectedSource
  congr 1
  funext _
  simp only [Matrix.mulVec,dotProduct,Finset.sum_smul,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  simp [mul_comm]

private theorem projected_source_measurable {r : ℕ} (L : MultilinearMap ℝ (fun _ : Fin r => F) ℝ)
    (v : ι → F) : Measurable (physicalProjectedSource L v) := by
  have he := funext (multilinear_test_polynomial L v)
  change Measurable (fun x : ι → ℝ => L (fun _ : Fin r => ∑ i, x i • v i))
  rw [he]
  unfold photonPolynomial monomial
  fun_prop

/-- The finite measured Hessian in the physical test basis. Its entries
in the covariance eigenframe are obtained by taking two literal coordinate
derivatives of the source with both external probes shifted before
averaging. Orthogonal conjugation returns this bilinear form to the
original physical coordinates. -/
def physicalProjectedHessian (D : Matrix ι ι ℝ) (hD : D.PosSemidef) (V : (ι → ℝ) → ℝ) : Matrix ι ι ℝ :=
  let U : Matrix ι ι ℝ := hD.1.eigenvectorUnitary
  U * measuredHessian hD.1.eigenvalues (fun x => V (U *ᵥ x)) * star U

theorem marked_physical_projection_trace {r : ℕ} (D : Matrix ι ι ℝ) (hD : D.PosSemidef)
    (L : MultilinearMap ℝ (fun _ : Fin r => F) ℝ) (v : ι → F) :
    (D * physicalProjectedHessian D hD (physicalProjectedSource L v)).trace =
      r * ∫ y, physicalProjectedSource L v y ∂photonProjectionLaw D hD := by
  let U : Matrix ι ι ℝ := hD.1.eigenvectorUnitary
  let d := hD.1.eigenvalues
  let H := measuredHessian d (fun x => physicalProjectedSource L v (U *ᵥ x))
  have hspec : D = U * Matrix.diagonal d * star U := hD.1.spectral_theorem
  have hU : star U * U = 1 := unitary.coe_star_mul_self _
  change (D*(U*H*star U)).trace = _
  nth_rw 1 [hspec]
  have he : (U*Matrix.diagonal d*star U)*(U*H*star U) = U*(Matrix.diagonal d*H)*star U := by
    calc
      _ = U * Matrix.diagonal d * (star U*U) * H * star U := by noncomm_ring
      _ = _ := by rw [hU,mul_one]; noncomm_ring
  rw [he,Matrix.trace_mul_cycle, hU,one_mul]
  unfold photonProjectionLaw
  rw [integral_map (by fun_prop : AEMeasurable (Matrix.mulVec U) (coordinateLaw d))
    (projected_source_measurable L v).aestronglyMeasurable]
  dsimp only [H]
  simp_rw [projected_source_change]
  exact projection_coordinate_trace L _ d hD.eigenvalues_nonneg

end UV.MarkedPhoton
