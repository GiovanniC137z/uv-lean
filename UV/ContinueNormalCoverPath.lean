import UV.ContinueWilsonSpinRotation
import UV.ContinueWilsonSpinNorm
import UV.ContinueSpectrumFourier
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Data.Real.Sign

/-! The oriented massive Dirac kernel on the real cover of the normal
circle. Open charged chains integrate their unconstrained increments
and sum every integer winding, including coincident normal endpoints. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter UV.SectorPlane
open scoped Matrix.Norms.L2Operator

namespace UV

def normalCoverEnergy (m : ℝ) (p : OSFourSpace) : ℝ := Real.sqrt (m^2+‖p‖^2)

theorem normal_cover_energy_bounds {m : ℝ} (hm : 0 < m) (p : OSFourSpace) :
    m ≤ normalCoverEnergy m p ∧ ‖p‖ ≤ normalCoverEnergy m p := by
  have h := Real.sq_sqrt (show 0 ≤ m^2+‖p‖^2 by positivity)
  have h0 := Real.sqrt_nonneg (m^2+‖p‖^2)
  unfold normalCoverEnergy
  constructor <;> nlinarith [sq_nonneg m,sq_nonneg ‖p‖,norm_nonneg p]

/-- The normal chirality can be either orientation, with its Euclidean
Clifford normalization. The coefficient of the signed normal jump is
kept separate from the four-dimensional carrier numerator. -/
def normalDiracCover (J : DiracMatrix) (m : ℝ) (p : OSFourSpace) (d : ℝ) : DiracMatrix :=
  (Real.exp (-(normalCoverEnergy m p)*|d|) : ℂ) •
    ((1/(2*(normalCoverEnergy m p : ℂ))) • freeDiracNumerator m p + ((Real.sign d/2 : ℝ) : ℂ) • J)

theorem normal_dirac_cover_bound (J : DiracMatrix) (hJ : ‖J‖ = 1) {m : ℝ} (hm : 0 < m) (p : OSFourSpace) (d : ℝ) :
    ‖normalDiracCover J m p d‖ ≤ 2*Real.exp (-normalCoverEnergy m p*|d|) := by
  let E := normalCoverEnergy m p
  have he := normal_cover_energy_bounds hm p
  have hE : 0 < E := hm.trans_le he.1
  have hN : ‖freeDiracNumerator m p‖ ≤ ‖p‖+m := by
    apply (norm_add_le ((-Complex.I) • diracSlash p) ((m:ℂ) • (1:DiracMatrix))).trans_eq
    rw [norm_smul,norm_neg,Complex.norm_I,one_mul,wilson_slash_opnorm,norm_smul,Complex.norm_real,
      Real.norm_of_nonneg hm.le,norm_one,mul_one]
  have hn : ‖(1/(2*(E : ℂ))) • freeDiracNumerator m p‖ ≤ 1 := by
    rw [norm_smul,norm_div,norm_mul,norm_one,Complex.norm_real,Real.norm_of_nonneg hE.le,Complex.norm_ofNat]
    calc (1/(2*E))*‖freeDiracNumerator m p‖ ≤ (1/(2*E))*(‖p‖+m) := mul_le_mul_of_nonneg_left hN (by positivity)
         _ ≤ 1 := by rw [one_div,←div_eq_inv_mul]; apply (div_le_one (by positivity)).mpr; linarith [he.1,he.2]
  have hs : |Real.sign d| ≤ 1 := by
    rcases lt_trichotomy d 0 with h|h|h
    · simp [Real.sign_of_neg h]
    · simp [h]
    · simp [Real.sign_of_pos h]
  have hj : ‖((Real.sign d/2 : ℝ) : ℂ) • J‖ ≤ 1 := by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_div,hJ,mul_one]
    norm_num
    linarith
  have hb := (norm_add_le ((1/(2*(E:ℂ))) • freeDiracNumerator m p) (((Real.sign d/2 : ℝ):ℂ) • J)).trans (add_le_add hn hj)
  rw [normalDiracCover,norm_smul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le,mul_comm (2:ℝ)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact hb.trans_eq (by norm_num)

def normalOpenIncrements {r : ℕ} (D : ℝ) (x : Fin r → ℝ) : Fin (r+1) → ℝ := Fin.cons (D-∑ j,x j) x

theorem normal_open_increments_sum {r : ℕ} (D : ℝ) (x : Fin r → ℝ) : ∑ j, normalOpenIncrements D x j = D := by
  simp [normalOpenIncrements,Fin.sum_univ_succ]

theorem normal_open_increment_envelope {r : ℕ} {m : ℝ} (hm : 0 < m) (D : ℝ) (x : Fin r → ℝ) :
    Real.exp (-m*∑ j, |normalOpenIncrements D x j|) ≤
      Real.exp (-(m/2)*|D|) * ∏ j, Real.exp (-(m/2)*|x j|) := by
  have hD : |D| ≤ ∑ j, |normalOpenIncrements D x j| := by
    calc |D| = |∑ j, normalOpenIncrements D x j| := congrArg abs (normal_open_increments_sum D x).symm
         _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
  have hx : ∑ j, |x j| ≤ ∑ j, |normalOpenIncrements D x j| := by
    rw [Fin.sum_univ_succ]; exact le_add_of_nonneg_left (abs_nonneg _)
  rw [←Real.exp_sum,←Real.exp_add,←Finset.mul_sum,Real.exp_le_exp]
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add hD hx) hm.le]

theorem normal_open_laplace_mass {m : ℝ} (hm : 0 < m) :
    Integrable (fun t : ℝ => Real.exp (-(m/2)*|t|)) ∧ (∫ t : ℝ, Real.exp (-(m/2)*|t|)) = 4/m := by
  have h : 0 < m/(4*Real.pi) := by positivity
  have he : 2*Real.pi*(m/(4*Real.pi)) = m/2 := by field_simp; ring
  have hi := (RevisionSpectrum.continueLaplaceFunction_integrable h).norm
  simp only [RevisionSpectrum.continueLaplaceFunction,he,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le] at hi
  refine ⟨hi,?_⟩
  rw [integral_comp_abs (f := fun y => Real.exp (-(m/2)*y)),integral_exp_mul_Ioi (show -(m/2)<0 by linarith) 0]
  simp only [mul_zero,Real.exp_zero]
  field_simp
  ring

theorem normal_winding_majorant {m L : ℝ} (hm : 0 < m) (hL : 0 < L) :
    let g := fun w : ℤ => Real.exp (m*L/2) * Real.exp (-(m*L/2)*|(w:ℝ)|)
    Summable g ∧ ∀ δ : ℝ, |δ| ≤ L → ∀ w : ℤ, Real.exp (-(m/2)*|δ+(w:ℝ)*L|) ≤ g w := by
  have ha : 0 < m*L/2 := by positivity
  have h := summable_geometric_of_lt_one (Real.exp_pos (-(m*L/2))).le (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha))
  have hn : Summable (fun n : ℕ => Real.exp (-(m*L/2)*(n:ℝ))) := by
    simpa only [Real.exp_nat_mul,mul_comm (-(m*L/2))] using h
  have hz : Summable (fun w : ℤ => Real.exp (-(m*L/2)*|(w:ℝ)|)) := by
    apply summable_int_iff_summable_nat_and_neg.mpr
    constructor <;> simpa using hn
  refine ⟨hz.mul_left _,?_⟩
  intro δ hδ w
  have htri := abs_add_le (δ+(w:ℝ)*L) (-δ)
  have hlen : |(w:ℝ)| * L ≤ |δ+(w:ℝ)*L|+L := by
    rw [show δ+(w:ℝ)*L+-δ=(w:ℝ)*L by ring,abs_mul,abs_of_pos hL,abs_neg] at htri
    linarith
  dsimp only
  rw [←Real.exp_add,Real.exp_le_exp]
  nlinarith [mul_le_mul_of_nonneg_left hlen hm.le]

end UV
