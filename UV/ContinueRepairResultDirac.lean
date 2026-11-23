import UV.FurtherOpticalProjector
import UV.ContinueNormalFrequency

/-! The free Fourier symbol of the repaired kinetic square and Gaussian
pair hop on the locked spatial three-plane. The four entries of the
Clifford vector are Hamiltonian coefficients. The temporal Fourier
frequency is an independent real variable. -/

noncomputable section
open Matrix UV.FurtherOptical
open scoped Matrix Matrix.Norms.L2Operator

namespace UV

def repairCliffordCoefficients (m τ g : ℝ) (k : ChargeSpatialMomentum) : DiracMomentum :=
  WithLp.toLp 2 (Fin.cons (diagonal m τ k) (fun i : Fin 3 => (g * attenuation τ k) * k i))

def repairHamiltonian (m τ g : ℝ) (k : ChargeSpatialMomentum) : DiracMatrix :=
  diracSlash (repairCliffordCoefficients m τ g k)

theorem repair_diagonal_lower {m τ : ℝ} (hm : 0 < m) (hτ : 0 ≤ τ) (k : ChargeSpatialMomentum) :
    m ≤ diagonal m τ k := by
  have h0 : 0 ≤ attenuation τ k := (Real.exp_pos _).le
  have h1 : attenuation τ k ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hτ) (sq_nonneg _))
  have hs := pow_le_pow_left₀ h0 h1 2
  have hd := diagonal_sq (m := m) hτ k
  rw [energy_sq] at hd
  have hn : 0 ≤ diagonal m τ k := Real.sqrt_nonneg _
  nlinarith [mul_nonneg (sq_nonneg ‖k‖) (sub_nonneg.mpr hs)]

theorem repair_clifford_norm_sq (m τ g : ℝ) (k : ChargeSpatialMomentum) :
    ‖repairCliffordCoefficients m τ g k‖^2 =
      diagonal m τ k^2 + (g*attenuation τ k)^2*‖k‖^2 := by
  rw [EuclideanSpace.norm_sq_eq,Fin.sum_univ_succ,EuclideanSpace.norm_sq_eq,Finset.mul_sum]
  simp only [Real.norm_eq_abs,sq_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change ((g*attenuation τ k)*k i)^2 = _
  ring

theorem repair_hamiltonian_shell {m τ : ℝ} (hτ : 0 ≤ τ) (k : ChargeSpatialMomentum) :
    repairHamiltonian m τ 1 k * repairHamiltonian m τ 1 k = ((energy m k^2:ℝ):ℂ) • 1 := by
  rw [repairHamiltonian,diracSlash_sq,repair_clifford_norm_sq,one_mul,diagonal_sq hτ]
  congr 2
  ring

/-- The two-sided temporal Fourier inverse is massive for every real
pair hopping, including zero, on the translation-invariant free sector. -/
theorem repair_free_inverse {m τ : ℝ} (hm : 0 < m) (hτ : 0 ≤ τ) (g ν : ℝ) (k : ChargeSpatialMomentum) :
    let H := repairHamiltonian m τ g k
    let D := ν^2+‖repairCliffordCoefficients m τ g k‖^2
    let S := (Complex.I*(ν:ℂ)) • (1:DiracMatrix) + H
    let G := ((D:ℂ)⁻¹) • ((-Complex.I*(ν:ℂ)) • (1:DiracMatrix) + H)
    S*G=1 ∧ G*S=1 ∧ ‖G‖ = (Real.sqrt D)⁻¹ ∧ ‖G‖ ≤ m⁻¹ := by
  let h := repairCliffordCoefficients m τ g k
  let H := diracSlash h
  let D := ν^2+‖h‖^2
  let S := (Complex.I*(ν:ℂ)) • (1:DiracMatrix) + H
  let N := (-Complex.I*(ν:ℂ)) • (1:DiracMatrix) + H
  have hd : m^2 ≤ D := by
    dsimp only [D,h]
    rw [repair_clifford_norm_sq]
    nlinarith [sq_nonneg ν, pow_le_pow_left₀ hm.le (repair_diagonal_lower hm hτ k) 2,
      mul_nonneg (sq_nonneg (g*attenuation τ k)) (sq_nonneg ‖k‖)]
  have hdpos : 0 < D := lt_of_lt_of_le (sq_pos_of_pos hm) hd
  have hdc : (D:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hdpos.ne'
  have hprod : S*N = (D:ℂ) • (1:DiracMatrix) ∧ N*S = (D:ℂ) • (1:DiracMatrix) := by
    constructor <;> simp only [S,N,H,D,add_mul,mul_add,mul_smul_comm,smul_mul_assoc,
      mul_one,one_mul,diracSlash_sq,Complex.ofReal_add,Complex.ofReal_pow]
    all_goals
      match_scalars
      all_goals ring_nf
      all_goals rw [Complex.I_sq]
      all_goals ring
  have hAdj : Nᴴ = S := by simp [S,N,H,Matrix.conjTranspose_smul,FurtherOptical.slash_adjoint]
  have hnorm := Matrix.l2_opNorm_conjTranspose_mul_self N
  rw [hAdj,hprod.1,norm_smul,norm_one,mul_one,Complex.norm_real,Real.norm_of_nonneg hdpos.le] at hnorm
  have hroot := Real.sq_sqrt hdpos.le
  have hN : ‖N‖ = Real.sqrt D := by nlinarith [norm_nonneg N,Real.sqrt_nonneg D]
  have hG : ‖(D:ℂ)⁻¹ • N‖ = (Real.sqrt D)⁻¹ := by
    rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hdpos.le,hN]
    field_simp [hdpos.ne',(Real.sqrt_pos.mpr hdpos).ne']
    nlinarith
  change S*((D:ℂ)⁻¹ • N)=1 ∧ ((D:ℂ)⁻¹ • N)*S=1 ∧ ‖(D:ℂ)⁻¹ • N‖=(Real.sqrt D)⁻¹ ∧ _
  refine ⟨?_,?_,hG,?_⟩
  · rw [mul_smul_comm,hprod.1,smul_smul,inv_mul_cancel₀ hdc,one_smul]
  · rw [smul_mul_assoc,hprod.2,smul_smul,inv_mul_cancel₀ hdc,one_smul]
  · change ‖(D:ℂ)⁻¹ • N‖ ≤ m⁻¹
    rw [hG]
    exact inv_anti₀ hm ((Real.le_sqrt hm.le hdpos.le).mpr hd)

end UV
