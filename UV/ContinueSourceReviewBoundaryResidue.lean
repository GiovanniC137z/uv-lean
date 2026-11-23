import UV.ContinueClosingPositiveVertex
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The residue paragraph following the positive charged-boundary realization
(lines 10348–10353). For a first-order matrix pole with a multiple zero
eigenvalue, the residue along a general normalized null vector need not
be the reciprocal of that vector's diagonal derivative. -/

noncomputable section
open Filter Set Matrix
open scoped Topology ComplexOrder Matrix

namespace UV.BoundaryResidue

abbrev Slot := Fin 2
abbrev Boundary := Fin 1
abbrev SlotMatrix := Matrix Slot Slot ℂ

def A : SlotMatrix := Matrix.diagonal ![0,1]
def T : Matrix Boundary Slot ℂ := fun _ => ![0,1]
def B : Matrix Boundary Boundary ℂ := 1

/-- The Schur matrix for the very same Hermitian block data, with
the scalar boundary resolvent at z. -/
def D (z : ℂ) : SlotMatrix := z • 1 + A - Tᴴ * ((z+1)⁻¹ • B) * T

def W₀ : SlotMatrix := Matrix.diagonal ![1,1/2]
def W₂ : SlotMatrix := Matrix.diagonal ![0,1/2]
def G (z : ℂ) : SlotMatrix := z⁻¹ • W₀ + (z+2)⁻¹ • W₂

theorem positive_normalized : W₀.PosSemidef ∧ W₂.PosSemidef ∧ W₀+W₂=1 := by
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num [Complex.le_def]
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num [Complex.le_def]
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [W₀,W₂,Matrix.one_apply,Matrix.diagonal]

theorem schur_inverse {z : ℂ} (h₀ : z ≠ 0) (h₁ : z+1 ≠ 0) (h₂ : z+2 ≠ 0) :
    D z * G z = 1 ∧ G z * D z = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [D,G,W₀,W₂,A,T,B,Matrix.diagonal,Matrix.mul_apply,Matrix.one_apply,
      Fin.sum_univ_two] <;> field_simp <;> ring

/-- Entrywise complex residue on the punctured neighbourhood, including
the two independent nonzero diagonal residues at the common simple pole. -/
theorem measured_simple_pole (i j : Slot) :
    Tendsto (fun z : ℂ => z * G z i j) (𝓝[≠] 0) (𝓝 (W₀ i j)) := by
  have hc : ContinuousAt (fun z : ℂ => W₀ i j+(z/(z+2))*W₂ i j) 0 := by
    fun_prop (disch := norm_num)
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0}:Set ℂ)ᶜ))
  convert h.congr' ?_ using 1
  · simp
  · filter_upwards [self_mem_nhdsWithin (s:=({0}:Set ℂ)ᶜ)] with z hz
    have hz' : z ≠ 0 := hz
    dsimp only [G,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
    rw [mul_add,←mul_assoc,mul_inv_cancel₀ hz',one_mul]
    ring

/-- The vector has equal component probabilities 1/2. Its global phase
allows the two components to be written with rational real and imaginary
parts. The source temporal mark is I+T*B⁻²T at E₀=0. -/
def v : EuclideanSpace ℂ Slot := WithLp.toLp 2 fun _ => (1+Complex.I)/2

def tested (M : SlotMatrix) : ℂ := dotProduct (star (fun i => v i)) (M.mulVec (fun i => v i))

theorem degenerate_pole_obstruction :
    ‖v‖ = 1 ∧ D 0 = 0 ∧ tested W₀ = 3/4 ∧ tested (1+Tᴴ*B*B*T) = 3/2 ∧
    tested W₀ ≠ (tested (1+Tᴴ*B*B*T))⁻¹ := by
  have hnorm : ‖v‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
    change ‖(1+Complex.I)/2‖^2+‖(1+Complex.I)/2‖^2=1
    simp only [Complex.sq_norm,Complex.normSq_apply]
    norm_num [Complex.div_re,Complex.div_im,Complex.normSq_apply]
  have hres : tested W₀ = 3/4 := by
    simp [tested,v,W₀,Matrix.diagonal,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    ring_nf
    norm_num [Complex.I_sq]
  have hder : tested (1+Tᴴ*B*B*T) = 3/2 := by
    simp [tested,v,T,B,Matrix.mul_apply,Matrix.one_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    ring_nf
    norm_num [Complex.I_sq]
  refine ⟨by nlinarith [norm_nonneg v],?_,hres,hder,?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [D,T,B,A,Matrix.mul_apply,Matrix.diagonal,Matrix.one_apply,Fin.sum_univ_two]
  · rw [hres,hder]
    norm_num

def testedOn (x : EuclideanSpace ℂ Slot) (M : SlotMatrix) : ℂ :=
  dotProduct (star (fun i => x i)) (M.mulVec (fun i => x i))

/-- The actual diagonal Laurent coefficient along each vector is obtained
by taking the punctured limit of that vector's own measured resolvent. -/
theorem measured_vector_residue (x : EuclideanSpace ℂ Slot) :
    Tendsto (fun z : ℂ => z*testedOn x (G z)) (𝓝[≠] 0) (𝓝 (testedOn x W₀)) := by
  have h : Tendsto (fun z : ℂ => ∑ i, star (x i) * (∑ j, (z*G z i j)*x j))
      (𝓝[≠] 0) (𝓝 (testedOn x W₀)) := by
    unfold testedOn dotProduct Matrix.mulVec
    apply tendsto_finset_sum
    intro i _
    apply Tendsto.const_mul
    apply tendsto_finset_sum
    intro j _
    exact (measured_simple_pole i j).mul_const _
  apply h.congr
  intro z
  simp [testedOn,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  ring

private theorem tested_diag (x : EuclideanSpace ℂ Slot) (a b : ℂ) :
    testedOn x (Matrix.diagonal ![a,b]) =
      a*(Complex.normSq (x 0):ℂ)+b*(Complex.normSq (x 1):ℂ) := by
  simp [testedOn,Matrix.mulVec,dotProduct,Matrix.diagonal,Fin.sum_univ_two,
    Complex.normSq_eq_conj_mul_self]
  ring

theorem actual_charge_discrepancy (q : ℝ) :
    tested W₀ * ((q:ℂ)*tested (1+Tᴴ*B*B*T)) = (9/8:ℂ)*q ∧
      (tested W₀*((q:ℂ)*tested (1+Tᴴ*B*B*T)) = q ↔ q = 0) := by
  obtain ⟨_,_,hw,ht,_⟩ := degenerate_pole_obstruction
  rw [hw,ht]
  constructor
  · ring
  · constructor
    · intro h
      apply Complex.ofReal_injective
      push_cast
      linear_combination (norm:=ring) 8*h
    · rintro rfl
      norm_num

/-- Exact directional residue and temporal vertex throughout the entire
two-dimensional nullspace. Their product for unit charge equals one
exactly on the two eigendirections of the compressed temporal vertex. -/
theorem arbitrary_null_vector_charge (x : EuclideanSpace ℂ Slot) (hx : ‖x‖ = 1) :
    let p := Complex.normSq (x 1)
    testedOn x W₀ = ((1-p/2:ℝ):ℂ) ∧
      testedOn x (1+Tᴴ*B*B*T) = ((1+p:ℝ):ℂ) ∧
      testedOn x W₀ * testedOn x (1+Tᴴ*B*B*T) = ((1+p*(1-p)/2:ℝ):ℂ) ∧
      (testedOn x W₀ * testedOn x (1+Tᴴ*B*B*T) = 1 ↔ x 0=0 ∨ x 1=0) := by
  let p := Complex.normSq (x 1)
  have hsum : Complex.normSq (x 0) + p = 1 := by
    have h := EuclideanSpace.norm_sq_eq x
    rw [hx,one_pow, Fin.sum_univ_two] at h
    simpa only [Complex.sq_norm] using h.symm
  have h₀ : Complex.normSq (x 0) = 1-p := by linarith
  have hw : testedOn x W₀ = ((1-p/2:ℝ):ℂ) := by
    rw [W₀,tested_diag,h₀]
    change 1*(↑(1-p):ℂ)+(1/2)*(p:ℂ)=_
    push_cast; ring
  have hdiag : 1+Tᴴ*B*B*T = Matrix.diagonal (![1,2] : Slot → ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [T,B,Matrix.mul_apply,Matrix.diagonal,Matrix.one_apply,Fin.sum_univ_two]
  have hd : testedOn x (1+Tᴴ*B*B*T) = ((1+p:ℝ):ℂ) := by
    rw [hdiag,tested_diag,h₀]
    change 1*(↑(1-p):ℂ)+2*(p:ℂ)=_
    push_cast; ring
  refine ⟨hw,hd,?_,?_⟩
  · rw [hw,hd,←Complex.ofReal_mul]
    congr 1; ring
  · rw [hw,hd,←Complex.ofReal_mul,←Complex.ofReal_one,Complex.ofReal_inj]
    constructor
    · intro he
      have hprod : (1-p)*p=0 := by nlinarith
      rcases mul_eq_zero.mp hprod with hl|hr
      · exact Or.inl (Complex.normSq_eq_zero.mp (h₀.trans hl))
      · exact Or.inr (Complex.normSq_eq_zero.mp hr)
    · rintro (hl|hr)
      · have he := Complex.normSq_eq_zero.mpr hl
        rw [show p=1 by linarith]
        norm_num
      · rw [show p=0 from Complex.normSq_eq_zero.mpr hr]
        norm_num

end UV.BoundaryResidue
