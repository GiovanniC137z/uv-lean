import UV.ContinueCompressedModesDeterminant
import Mathlib.Data.Matrix.Composition
import Mathlib.Logic.Equiv.Fin.Rotate
import UV.ContinueCompressedOpen

/-! Expand the finite transverse Fourier-spin pencil in its original
three-compression entries. The carrier transfer of each insertion is the
difference of its two adjacent charged carrier momenta. -/

noncomputable section

open Matrix Filter UV.SectorPlane
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

namespace UV

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]

/-- A word with fixed end states and n unrestricted intermediate states. -/
def compressedArc (A : Matrix κ κ DiracMatrix) {n : ℕ} (i j : κ) (z : Fin n → κ) :=
  normalOrderedWord (fun b : Fin (n+1) => A (Fin.cons (α := fun _ => κ) i z b) (Fin.snoc (α := fun _ => κ) z j b))

omit [Fintype κ] [DecidableEq κ] in
theorem compressed_arc_succ (A : Matrix κ κ DiracMatrix) {n : ℕ} (i j x : κ) (z : Fin n → κ) :
    compressedArc A i j (Fin.cons x z) = A i x * compressedArc A x j z := by
  simp only [compressedArc,normalOrderedWord,List.ofFn_succ,List.prod_cons,←Fin.cons_snoc_eq_snoc_cons,
    Fin.cons_zero,Fin.cons_succ]

theorem compressed_block_power (A : Matrix κ κ DiracMatrix) (n : ℕ) (i j : κ) :
    (A^(n+1)) i j = ∑ z : Fin n → κ, compressedArc A i j z := by
  induction n generalizing i with
  | zero =>
    simp [compressedArc,normalOrderedWord,Fin.snoc_zero]
  | succ n ih =>
    rw [pow_succ',Matrix.mul_apply]
    let e := Fin.consEquiv (fun _ : Fin (n+1) => κ)
    rw [←e.sum_comp,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    rw [ih,Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => (compressed_arc_succ A i j x z).symm

def compressedFlatten := Matrix.compAlgEquiv κ (Fin 4) ℂ ℂ

theorem compressed_flat_trace (A : Matrix κ κ DiracMatrix) :
    (compressedFlatten A).trace = ∑ i, (A i i).trace := by
  simp [compressedFlatten,Matrix.trace,Fintype.sum_prod_type,Matrix.compAlgEquiv_apply]

/-- For one source spectrum at a fixed normal mode, W carries its
scalar Fourier amplitude, with both signed transfers allowed. -/
def compressedBlockVertex (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (p : κ → OSFourSpace) (u : κ → κ → UnitVector OSFourSpace) (W : κ → κ → ℂ) : Matrix κ κ DiracMatrix :=
  fun i j => (W i j * (normalLegForm L T 0 (p i-p j):ℂ) * Complex.I *
    normalLegForm L T ξ (p i) * normalLegForm L T ξ (p j)) • diracSlash (u i j).val

def compressedBlockSymbol (m ξ : ℝ) (p : κ → OSFourSpace) : Matrix κ κ DiracMatrix :=
  Matrix.diagonal (fun i => normalDiracSymbol m (p i) ξ)

def compressedBlockFree (m ξ : ℝ) (p : κ → OSFourSpace) : Matrix κ κ DiracMatrix :=
  Matrix.diagonal (fun i => normalDiracFrequency m (p i) ξ)

theorem compressed_block_free_inverse {m : ℝ} (hm : 0 < m) (ξ : ℝ) (p : κ → OSFourSpace) :
    compressedBlockSymbol m ξ p * compressedBlockFree m ξ p = 1 ∧
    compressedBlockFree m ξ p * compressedBlockSymbol m ξ p = 1 := by
  constructor
  · simp only [compressedBlockSymbol,compressedBlockFree,Matrix.diagonal_mul_diagonal,
      (normal_dirac_two_sided_inverse hm _ _).1,Matrix.diagonal_one]
  · simp only [compressedBlockSymbol,compressedBlockFree,Matrix.diagonal_mul_diagonal,
      (normal_dirac_two_sided_inverse hm _ _).2,Matrix.diagonal_one]

def compressedRelativeLog (D V : Matrix κ κ DiracMatrix) (t : ℝ) : ℝ :=
  -Real.log ‖(compressedFlatten (D+(t:ℂ) • V)).det/(compressedFlatten D).det‖

theorem compressed_block_logdet_paths {m : ℝ} (hm : 0 < m) (ξ : ℝ) (p : κ → OSFourSpace)
    (V : Matrix κ κ DiracMatrix) (n : ℕ) :
    let D := compressedBlockSymbol m ξ p
    let A := compressedBlockFree m ξ p * V
    iteratedDeriv (n+1) (compressedRelativeLog D V) 0 / (n+1).factorial =
      (-1:ℝ)^(n+1)*(∑ i, ∑ z : Fin n → κ, (compressedArc A i i z).trace).re/(n+1) := by
  let D := compressedBlockSymbol m ξ p
  let S := compressedBlockFree m ξ p
  let A := S*V
  have hDS := (compressed_block_free_inverse hm ξ p).1
  have hmul : compressedFlatten D * compressedFlatten S = 1 := by rw [←map_mul,hDS,map_one]
  have hdet : (compressedFlatten D).det ≠ 0 := by
    have h := congrArg Matrix.det hmul
    rw [Matrix.det_mul,Matrix.det_one] at h
    exact left_ne_zero_of_mul_eq_one h
  have hlog : compressedRelativeLog D V = compressedPencilLog (compressedFlatten A) := by
    funext t
    have hb : D+(t:ℂ) • V = D*(1+(t:ℂ) • A) := by
      simp only [A,mul_add,mul_one,Matrix.mul_smul]
      rw [←mul_assoc,hDS,one_mul]
    simp only [compressedRelativeLog,hb,map_mul,map_add,map_one,map_smul,Matrix.det_mul,
      mul_div_cancel_left₀ _ hdet,compressedPencilLog,compressedPencil]
  change iteratedDeriv _ (compressedRelativeLog D V) _ / _ = _
  rw [hlog,compressed_logdet_cyclic_coefficient,←map_pow,compressed_flat_trace]
  simp_rw [compressed_block_power A n,Matrix.trace_sum]
  rfl

/-- The convergent inverse series of the normalized affine operator with
the final free endpoint factor, including its order-zero open path. -/
theorem compressed_inverse_open_series (D S V : Matrix κ κ ℂ) (hDS : D*S = 1) (hSD : S*D = 1)
    (t : ℝ) (ht : ‖(t:ℂ) • (S*V)‖ < 1) :
    HasSum (fun n : ℕ => ((-(t:ℂ))^n) • ((S*V)^n*S)) (D+(t:ℂ) • V)⁻¹ := by
  let A := S*V
  let x := -(t:ℂ) • A
  have hx : ‖x‖ < 1 := by simpa [x,A] using ht
  have hgeo := (hasSum_geom_series_inverse x hx).mul_right S
  have hB : D+(t:ℂ) • V = D*(1-x) := by
    simp only [x,A,neg_smul,sub_neg_eq_add,mul_add,mul_one,Matrix.mul_smul,←mul_assoc,hDS,one_mul]
  have hI : Ring.inverse (1-x)*S = (D+(t:ℂ) • V)⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    rw [hB,mul_assoc,←mul_assoc S,hSD,one_mul]
    exact Ring.inverse_mul_cancel (1-x) (Units.oneSub x hx).isUnit
  rw [←hI]
  convert hgeo using 1
  funext n
  simp only [x,smul_pow,smul_mul_assoc,A]

end UV
