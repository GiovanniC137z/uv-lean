import UV.ContinueRepairResultDirac
import UV.ContinueWilsonSpinRotation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The exact finite-slab homogeneous transfer at arbitrary fixed hopping.
The negative onsite endpoint block is an invertible scalar on the hole
slot. The boundary condition here is the particle-hole vacuum condition,
with the complex Euclidean frequency separate from the sector pole unit. -/

noncomputable section
open Matrix UV.FurtherOptical
open scoped Matrix Matrix.Norms.L2Operator RealInnerProductSpace

namespace UV

def repairSlotEnergy (m τ g : ℝ) (k : ChargeSpatialMomentum) := ‖repairCliffordCoefficients m τ g k‖

theorem repair_slot_energy_lower {m τ : ℝ} (hm : 0 < m) (hτ : 0 ≤ τ) (g : ℝ) (k : ChargeSpatialMomentum) :
    m ≤ repairSlotEnergy m τ g k := by
  have h := repair_clifford_norm_sq m τ g k
  change m ≤ ‖repairCliffordCoefficients m τ g k‖
  exact (sq_le_sq₀ hm.le (norm_nonneg _)).mp (by
    nlinarith [pow_le_pow_left₀ hm.le (repair_diagonal_lower hm hτ k) 2,
      mul_nonneg (sq_nonneg (g*attenuation τ k)) (sq_nonneg ‖k‖)])

def repairSlabTransfer (m τ g : ℝ) (k : ChargeSpatialMomentum) (t : ℝ) : DiracMatrix :=
  let r := repairSlotEnergy m τ g k
  ((Real.cosh (r*t):ℝ):ℂ) • (1:DiracMatrix) -
    (((Real.sinh (r*t)/r):ℝ):ℂ) • repairHamiltonian m τ g k

@[simp] theorem repair_slab_transfer_zero (m τ g : ℝ) (k : ChargeSpatialMomentum) :
    repairSlabTransfer m τ g k 0 = 1 := by simp [repairSlabTransfer]

theorem repair_slab_transfer_equation {m τ : ℝ} (hm : 0 < m) (hτ : 0 ≤ τ) (g : ℝ) (k : ChargeSpatialMomentum) (t : ℝ) :
    HasDerivAt (repairSlabTransfer m τ g k) (-(repairHamiltonian m τ g k * repairSlabTransfer m τ g k t)) t := by
  let r := repairSlotEnergy m τ g k
  let H := repairHamiltonian m τ g k
  have hr : 0 < r := hm.trans_le (repair_slot_energy_lower hm hτ g k)
  have hs : H*H = ((r^2:ℝ):ℂ) • (1:DiracMatrix) := diracSlash_sq _
  have hd := (hasDerivAt_id t).const_mul r
  have h₀ := (hd.cosh.ofReal_comp.smul_const (1:DiracMatrix)).sub
    ((hd.sinh.div_const r).ofReal_comp.smul_const H)
  convert h₀ using 1
  change -(H*(((Real.cosh (r*t):ℝ):ℂ) • (1:DiracMatrix) - (((Real.sinh (r*t)/r):ℝ):ℂ) • H)) = _
  rw [mul_sub,mul_smul_comm,mul_smul_comm,mul_one,hs,smul_smul]
  push_cast
  match_scalars <;> field_simp [hr.ne'] <;> rfl

private theorem repair_slot_compression (m τ g : ℝ) (k : ChargeSpatialMomentum) :
    let P := projector massAxis
    P*repairHamiltonian m τ g k*P = (-((diagonal m τ k:ℝ):ℂ)) • P := by
  let B := diracSlash massAxis
  let H := repairHamiltonian m τ g k
  have hb : B*B = 1 := by simpa [B,massAxis] using diracSlash_sq massAxis
  have hInner : ⟪massAxis,repairCliffordCoefficients m τ g k⟫ = diagonal m τ k := by
    simp [massAxis,repairCliffordCoefficients,PiLp.inner_apply]
  have hAnti : B*H + H*B = ((2*diagonal m τ k:ℝ):ℂ) • 1 := by
    simpa only [B,H,repairHamiltonian,hInner] using wilson_slash_anticommutator massAxis (repairCliffordCoefficients m τ g k)
  have hBHB : B*H*B = ((2*diagonal m τ k:ℝ):ℂ) • B - H := by
    have h := congrArg (fun X : DiracMatrix => X*B) hAnti
    dsimp only at h
    rwa [add_mul,mul_assoc H B B,hb,mul_one,smul_mul_assoc,one_mul,←eq_sub_iff_add_eq] at h
  change ((1/2:ℂ) • (1-B))*H*((1/2:ℂ) • (1-B)) = _ • ((1/2:ℂ) • (1-B))
  simp only [smul_mul_assoc,mul_smul_comm,sub_mul,mul_sub,one_mul,mul_one,smul_smul]
  have hHB : H*B = ((2*diagonal m τ k:ℝ):ℂ) • 1 - B*H := by rw [←hAnti]; abel
  rw [hBHB,hHB]
  push_cast
  module

/-- The hole-endpoint compression for propagation from time zero to T.
For m>0, τ≥0 and T≥0 the scalar response is at least one, at all real
hoppings. This rules out singular endpoint shooting matrices per mode. -/
theorem repair_slab_hole_endpoint {m τ T : ℝ} (hm : 0 < m) (hτ : 0 ≤ τ) (hT : 0 ≤ T)
    (g : ℝ) (k : ChargeSpatialMomentum) :
    let P := projector massAxis
    let r := repairSlotEnergy m τ g k
    let c := Real.cosh (r*T) + (Real.sinh (r*T)/r)*diagonal m τ k
    P*repairSlabTransfer m τ g k T*P = (c:ℂ) • P ∧ 1 ≤ c := by
  let r := repairSlotEnergy m τ g k
  have hr := hm.trans_le (repair_slot_energy_lower hm hτ g k)
  have hP := projector_idempotent massAxis (by simp [massAxis])
  constructor
  · simp only [repairSlabTransfer,mul_sub,mul_smul_comm,mul_one,sub_mul,smul_mul_assoc,hP,
      repair_slot_compression,smul_smul,Complex.ofReal_add,Complex.ofReal_mul]
    module
  · exact (Real.one_le_cosh _).trans (le_add_of_nonneg_right
      (mul_nonneg (div_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg hr.le hT)) hr.le)
        (hm.trans_le (repair_diagonal_lower hm hτ k)).le))

end UV
