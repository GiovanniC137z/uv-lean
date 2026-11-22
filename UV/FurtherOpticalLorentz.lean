import UV.FurtherOpticalProjector
import UV.ContinuationSectorPlane

/-! Positive timelike current tensors in carrier-adapted coordinates on
one locked diamond. Slot zero is the intrinsic time coordinate along
the fixed pole unit of the diamond. Spatial rotations leave it fixed. -/

noncomputable section
open Matrix
open scoped Matrix ComplexOrder

namespace UV.FurtherOptical

def restLorentzMetric : DiracMatrix := Matrix.diagonal (![1,-1,-1,-1] : Fin 4 → ℂ)

def restQuarter12 : DiracMatrix := fun i j =>
  if Equiv.swap (1 : Fin 4) 2 i = j then (if i = 1 then -1 else 1) else 0

def restQuarter13 : DiracMatrix := fun i j =>
  if Equiv.swap (1 : Fin 4) 3 i = j then (if i = 1 then -1 else 1) else 0

def restMomentum (s : ℝ) : Fin 4 → ℂ := Pi.single 0 (Real.sqrt s : ℂ)

private theorem sum_fin_four (f : Fin 4 → ℂ) :
    ∑ i, f i = f 0 + (f 1 + (f 2 + f 3)) := by
  simp [Fin.sum_univ_succ]

set_option maxHeartbeats 1000000 in
theorem restQuarter12_preserves_metric :
    restQuarter12 * restLorentzMetric * restQuarter12ᵀ = restLorentzMetric := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Matrix.transpose_apply, sum_fin_four] <;>
    norm_num [restQuarter12, restLorentzMetric, Matrix.diagonal_apply, Equiv.swap_apply_def, Fin.ext_iff] <;> rfl

set_option maxHeartbeats 1000000 in
theorem restQuarter13_preserves_metric :
    restQuarter13 * restLorentzMetric * restQuarter13ᵀ = restLorentzMetric := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Matrix.transpose_apply, sum_fin_four] <;>
    norm_num [restQuarter13, restLorentzMetric, Matrix.diagonal_apply, Equiv.swap_apply_def, Fin.ext_iff] <;> rfl

private theorem rest_time_row {s : ℝ} (hs : 0 < s) {A : DiracMatrix}
    (hcons : restMomentum s ᵥ* A = 0) (j : Fin 4) :
    A 0 j = 0 := by
  rw [restMomentum, Matrix.single_vecMul] at hcons
  have h : (Real.sqrt s : ℂ) * A 0 j = 0 := congrFun hcons j
  exact (mul_eq_zero.mp h).resolve_left
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hs).ne')

set_option maxHeartbeats 1500000 in
private theorem rotation_entries {A : DiracMatrix}
    (h12 : restQuarter12 * A * restQuarter12ᵀ = A)
    (h13 : restQuarter13 * A * restQuarter13ᵀ = A) :
    A 2 2 = A 1 1 ∧ A 3 3 = A 1 1 ∧
    A 1 2 = 0 ∧ A 1 3 = 0 ∧ A 2 1 = 0 ∧ A 2 3 = 0 ∧ A 3 1 = 0 ∧ A 3 2 = 0 := by
  have h22 := congrArg (fun T : DiracMatrix => T 2 2) h12
  have h33 := congrArg (fun T : DiracMatrix => T 3 3) h13
  have h23 := congrArg (fun T : DiracMatrix => T 2 3) h12
  have h13' := congrArg (fun T : DiracMatrix => T 1 3) h12
  have h32 := congrArg (fun T : DiracMatrix => T 3 2) h12
  have h31 := congrArg (fun T : DiracMatrix => T 3 1) h12
  have h12' := congrArg (fun T : DiracMatrix => T 1 2) h13
  have h21 := congrArg (fun T : DiracMatrix => T 2 1) h13
  simp only [Matrix.mul_apply, Matrix.transpose_apply, sum_fin_four] at h22 h33 h23 h13' h32 h31 h12' h21
  norm_num [restQuarter12, restQuarter13, Equiv.swap_apply_def, Fin.ext_iff] at h22 h33 h23 h13' h32 h31 h12' h21
  have z13 : A 1 3 = 0 := by linear_combination -(h13'-h23)/2
  have z23 : A 2 3 = 0 := by rw [← h23, z13]
  have z31 : A 3 1 = 0 := by linear_combination -(h31-h32)/2
  have z32 : A 3 2 = 0 := by rw [← h32, z31]
  refine ⟨h22.symm,h33.symm,?_,z13,?_,z23,z31,z32⟩
  · rw [← h12', z32, neg_zero]
  · rw [← h21, z23, neg_zero]

set_option maxHeartbeats 2000000 in
/-- Conservation kills the positive-energy rest time row, positivity
kills its adjoint column, and invariance under the spatial quarter turns
forces a common nonnegative spatial coefficient. -/
theorem conserved_rest_tensor {s : ℝ} (hs : 0 < s) (A : DiracMatrix)
    (hA : A.PosSemidef) (hcons : restMomentum s ᵥ* A = 0)
    (h12 : restQuarter12 * A * restQuarter12ᵀ = A)
    (h13 : restQuarter13 * A * restQuarter13ᵀ = A) :
    ∃ c : ℝ, 0 ≤ c ∧ A = ((c/s : ℝ) : ℂ) • (vecMulVec (restMomentum s) (restMomentum s) -
      (s : ℂ) • restLorentzMetric) := by
  have row := rest_time_row hs hcons
  have col (i : Fin 4) : A i 0 = 0 := by
    have h := congrArg (fun T : DiracMatrix => T i 0) hA.isHermitian
    simpa only [Matrix.conjTranspose_apply, row, star_zero] using h.symm
  obtain ⟨h22,h33,h12',h13',h21,h23,h31,h32⟩ := rotation_entries h12 h13
  have hdiag := hA.2 (Pi.single (1:Fin 4) (1:ℂ))
  have hd : 0 ≤ A 1 1 := by
    simpa only [Matrix.mulVec_single_one, ← Pi.single_star, star_one,
      single_dotProduct, one_mul, col_apply] using hdiag
  obtain ⟨hdRe, hdIm⟩ := Complex.nonneg_iff.mp hd
  have hcoef : A 1 1 = ((A 1 1).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hdIm.symm
  refine ⟨(A 1 1).re, hdRe, ?_⟩
  have hs' : (s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hroot : (↑(Real.sqrt s):ℂ) * (↑(Real.sqrt s):ℂ) = (s:ℂ) := by
    rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt hs.le]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [vecMulVec_apply, restMomentum, restLorentzMetric, Matrix.diagonal_apply,
      smul_eq_mul, hroot, row, col, h22, h33, h12', h13', h21, h23, h31, h32, ← hcoef,
      Complex.ofReal_div, hs']
  all_goals first | exact h22 | exact h33 | exact h12' | exact h13' | exact h21 | exact h23 | exact h31 | exact h32

/-- Lorentz congruence transports the positive rest tensor to the
transverse spectral tensor on the same locked diamond. The boost
preserves the Lorentz metric and transports the actual rest momentum. -/
theorem lorentz_tensor_from_rest {E : Type*} [Norm E] (diamond : SectorPlane.Plane E)
    (A B T : SectorPlane.Plane E → DiracMatrix)
    {s : ℝ} (hs : 0 < s) (p : Fin 4 → ℂ)
    (hA : (A diamond).PosSemidef) (hcons : restMomentum s ᵥ* A diamond = 0)
    (h12 : restQuarter12 * A diamond * restQuarter12ᵀ = A diamond)
    (h13 : restQuarter13 * A diamond * restQuarter13ᵀ = A diamond)
    (hB : B diamond * restLorentzMetric * (B diamond)ᵀ = restLorentzMetric)
    (hp : B diamond *ᵥ restMomentum s = p) (hT : T diamond = B diamond * A diamond * (B diamond)ᵀ) :
    ∃ c : ℝ, 0 ≤ c ∧ T diamond = (c : ℂ) • (vecMulVec p p - (s:ℂ) • restLorentzMetric) := by
  obtain ⟨c,hc,hR⟩ := conserved_rest_tensor hs (A diamond) hA hcons h12 h13
  refine ⟨c/s, div_nonneg hc hs.le, ?_⟩
  have hright : restMomentum s ᵥ* (B diamond)ᵀ = p := by
    rw [← hp, Matrix.vecMul_transpose]
  rw [hT, hR, Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hp, hright,
    Matrix.mul_smul, Matrix.smul_mul, hB]

/-- Future-shell momentum with intrinsic time entry in the fixed carrier unit. -/
def shellMomentum (s : ℝ) (p : ChargeSpatialMomentum) : Fin 4 → ℂ :=
  Fin.cons (↑(Real.sqrt (‖p‖ ^ 2 + s))) (fun i => (p i : ℂ))

/-- Dividing the tensor's time-time component by the positive mass-shell
Jacobian factor gives the equal-time spectral integrand. -/
theorem lorentz_tensor_time_weight (s c : ℝ) (hs : 0 ≤ s)
    (p : ChargeSpatialMomentum) (T : DiracMatrix)
    (hT : T = (c : ℂ) • (vecMulVec (shellMomentum s p) (shellMomentum s p) -
      (s : ℂ) • restLorentzMetric)) :
    (T 0 0).re / (2 * Real.sqrt (‖p‖ ^ 2 + s)) =
      c * (‖p‖ ^ 2 / (2 * Real.sqrt (‖p‖ ^ 2 + s))) := by
  have hrad : 0 ≤ ‖p‖ ^ 2 + s := add_nonneg (sq_nonneg _) hs
  have hroot : ((Real.sqrt (‖p‖ ^ 2 + s) : ℝ) : ℂ) *
      ↑(Real.sqrt (‖p‖ ^ 2 + s)) = ((‖p‖ ^ 2 + s : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt hrad]
  have h00 : T 0 0 = (c : ℂ) * (‖p‖ ^ 2 : ℝ) := by
    rw [hT]
    change (c : ℂ) * (↑(Real.sqrt (‖p‖ ^ 2 + s)) *
      ↑(Real.sqrt (‖p‖ ^ 2 + s)) - (s : ℂ) * 1) = _
    rw [hroot]
    push_cast
    ring
  rw [h00, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_div_assoc]

/-- A boost along the first spatial direction in the fixed carrier coordinates. -/
def axialBoost (s r : ℝ) : DiracMatrix :=
  let γ : ℂ := (Real.sqrt (r^2+s) / Real.sqrt s : ℝ)
  let κ : ℂ := (r / Real.sqrt s : ℝ)
  !![γ,κ,0,0; κ,γ,0,0; 0,0,1,0; 0,0,0,1]

set_option maxHeartbeats 1400000 in
theorem axialBoost_preserves_metric {s : ℝ} (hs : 0 < s) (r : ℝ) :
    axialBoost s r * restLorentzMetric * (axialBoost s r)ᵀ = restLorentzMetric := by
  let f := Real.sqrt (r^2+s)
  let m := Real.sqrt s
  have hm : 0 < m := Real.sqrt_pos.mpr hs
  have hγ : ((f/m : ℝ) : ℂ) ^ 2 - ((r/m : ℝ) : ℂ) ^ 2 = 1 := by
    norm_cast
    have hf₂ : f^2 = r^2+s := Real.sq_sqrt (add_nonneg (sq_nonneg _) hs.le)
    have hm₂ : m^2 = s := Real.sq_sqrt hs.le
    rw [div_pow, div_pow, ← sub_div, hf₂, hm₂]
    field_simp
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [axialBoost, restLorentzMetric, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal_apply]
  all_goals first
    | simpa [f, m, pow_two] using hγ
    | simpa [f, m, pow_two, neg_sub] using congrArg Neg.neg hγ
    | simp only [mul_comm, ← sub_eq_add_neg, sub_self]

set_option maxHeartbeats 600000 in
theorem axialBoost_restMomentum {s : ℝ} (hs : 0 < s) (r : ℝ) :
    axialBoost s r *ᵥ restMomentum s = shellMomentum s (EuclideanSpace.single 0 r) := by
  have hr : ‖EuclideanSpace.single (𝕜 := ℝ) (0 : Fin 3) r‖ ^ 2 = r^2 := by
    rw [EuclideanSpace.norm_single, Real.norm_eq_abs, sq_abs]
  have hm : (↑(Real.sqrt s) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hs).ne'
  rw [restMomentum, Matrix.mulVec_single]
  ext i
  simp only [Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, col_apply]
  fin_cases i
  · change ((Real.sqrt (r^2+s)/Real.sqrt s : ℝ) : ℂ) * (Real.sqrt s : ℂ) =
      (Real.sqrt (‖EuclideanSpace.single (𝕜 := ℝ) (0:Fin 3) r‖^2+s) : ℂ)
    rw [hr, Complex.ofReal_div, div_mul_cancel₀ _ hm]
  · change ((r/Real.sqrt s : ℝ) : ℂ) * (Real.sqrt s : ℂ) = (r : ℂ)
    rw [Complex.ofReal_div, div_mul_cancel₀ _ hm]
  · change (0:ℂ) * (Real.sqrt s : ℂ) = 0
    exact zero_mul _
  · change (0:ℂ) * (Real.sqrt s : ℂ) = 0
    exact zero_mul _

end UV.FurtherOptical
