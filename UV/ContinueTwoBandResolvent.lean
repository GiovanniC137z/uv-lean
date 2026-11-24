import UV.ContinuationSectorPlane
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The two-slot inverse of the translation-invariant comparison source.
The real variable `ω` is the Euclidean Fourier coordinate along the locked
plane's unit carrier. The two internal slots are independent of its sector. -/

noncomputable section
open Matrix MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator

namespace UV.SectorPlane

abbrev TwoBandMatrix := Matrix (Fin 2) (Fin 2) ℂ

def twoBandInversionFactor (m v ω : ℝ) : ℝ := ω^2 + m^2 + v^2

def twoBandSymbol (m v ω : ℝ) : TwoBandMatrix :=
  !![Complex.I*(ω:ℂ) + m, v; v, Complex.I*(ω:ℂ) - m]

def twoBandNumerator (m v ω : ℝ) : TwoBandMatrix :=
  !![-Complex.I*(ω:ℂ) + m, v; v, -Complex.I*(ω:ℂ) - m]

def twoBandResolvent (m v ω : ℝ) : TwoBandMatrix :=
  ((twoBandInversionFactor m v ω : ℂ)⁻¹) • twoBandNumerator m v ω

def twoBandMix : TwoBandMatrix := !![0, 1; 1, 0]

def twoBandFrequencyBound (m ω : ℝ) : ℝ := (Real.sqrt (ω^2 + m^2))⁻¹

private theorem twoBand_factor_pos {m : ℝ} (hm : 0 < m) (v ω : ℝ) :
    0 < twoBandInversionFactor m v ω := by
  unfold twoBandInversionFactor
  positivity

private theorem twoBand_numerator_adjoint (m v ω : ℝ) :
    (twoBandNumerator m v ω)ᴴ = twoBandSymbol m v ω := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoBandNumerator, twoBandSymbol, Matrix.conjTranspose_apply]

private theorem twoBand_scale_products (m v ω : ℝ) :
    let S := twoBandSymbol m v ω
    let N := twoBandNumerator m v ω
    let D := twoBandInversionFactor m v ω
    S*N = (D:ℂ) • 1 ∧ N*S = (D:ℂ) • 1 := by
  dsimp only
  constructor
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;> simp [twoBandSymbol, twoBandNumerator, twoBandInversionFactor,
      Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring_nf
    all_goals rw [Complex.I_sq]
    all_goals ring

theorem twoBand_resolvent_inverse {m : ℝ} (hm : 0 < m) (v ω : ℝ) :
    twoBandSymbol m v ω * twoBandResolvent m v ω = 1 ∧
      twoBandResolvent m v ω * twoBandSymbol m v ω = 1 := by
  have hD : (twoBandInversionFactor m v ω : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (twoBand_factor_pos hm v ω).ne'
  obtain ⟨hLeft, hRight⟩ := twoBand_scale_products m v ω
  unfold twoBandResolvent
  constructor
  · rw [mul_smul_comm, hLeft, smul_smul, inv_mul_cancel₀ hD, one_smul]
  · rw [smul_mul_assoc, hRight, smul_smul, inv_mul_cancel₀ hD, one_smul]

theorem twoBand_resolvent_norm {m : ℝ} (hm : 0 < m) (v ω : ℝ) :
    ‖twoBandResolvent m v ω‖ = (Real.sqrt (twoBandInversionFactor m v ω))⁻¹ := by
  let D := twoBandInversionFactor m v ω
  let N := twoBandNumerator m v ω
  have hD : 0 < D := twoBand_factor_pos hm v ω
  have hN := Matrix.l2_opNorm_conjTranspose_mul_self N
  rw [twoBand_numerator_adjoint, (twoBand_scale_products m v ω).1, norm_smul,
    norm_one, mul_one, Complex.norm_real, Real.norm_of_nonneg hD.le] at hN
  have hRoot : ‖N‖ = Real.sqrt D := by
    nlinarith [norm_nonneg N, Real.sqrt_nonneg D, Real.sq_sqrt hD.le]
  change ‖((D:ℂ)⁻¹) • N‖ = (Real.sqrt D)⁻¹
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hD.le, hRoot]
  field_simp [hD.ne', (Real.sqrt_pos.mpr hD).ne']
  nlinarith [Real.sq_sqrt hD.le]

theorem twoBand_resolvent_bound {m : ℝ} (hm : 0 < m) (v ω : ℝ) :
    ‖twoBandResolvent m v ω‖ ≤ twoBandFrequencyBound m ω ∧ twoBandFrequencyBound m ω ≤ m⁻¹ := by
  unfold twoBandFrequencyBound
  have hD : 0 < ω^2 + m^2 := by positivity
  rw [twoBand_resolvent_norm hm]
  constructor
  · exact inv_anti₀ (Real.sqrt_pos.mpr hD) (Real.sqrt_le_sqrt (by
      dsimp [twoBandInversionFactor]
      linarith [sq_nonneg v]))
  · apply inv_anti₀ hm
    exact (Real.le_sqrt hm.le hD.le).mpr (by linarith [sq_nonneg ω])

private theorem twoBand_mix_unitary : twoBandMix ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [twoBandMix, Matrix.mul_apply, Fin.sum_univ_two]

theorem twoBand_mix_norm : ‖twoBandMix‖ = 1 := CStarRing.norm_of_mem_unitary twoBand_mix_unitary

/-- A single shifted inverse difference costs one Gaussian hopping and
two factors at the same frequency, without requiring small hopping. -/
theorem twoBand_resolvent_difference_bound {m : ℝ} (hm : 0 < m) (v w ω : ℝ) :
    ‖twoBandResolvent m v ω - twoBandResolvent m w ω‖ ≤
      |v-w| * (twoBandFrequencyBound m ω)^2 := by
  let R := fun v => twoBandResolvent m v ω
  let S := fun v => twoBandSymbol m v ω
  have hSym : S w - S v = ((w-v:ℝ):ℂ) • twoBandMix := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [S, twoBandSymbol, twoBandMix]
  have he : R v - R w = R v * (S w - S v) * R w := by
    rw [mul_sub, sub_mul, mul_assoc (R v) (S w), (twoBand_resolvent_inverse hm w ω).1,
      (twoBand_resolvent_inverse hm v ω).2, mul_one, one_mul]
  change ‖R v - R w‖ ≤ _
  rw [he, hSym]
  have hNorm : ‖((w-v:ℝ):ℂ) • twoBandMix‖ = |v-w| := by
    rw [norm_smul, twoBand_mix_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  calc
    _ ≤ (‖R v‖ * ‖((w-v:ℝ):ℂ) • twoBandMix‖) * ‖R w‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (twoBandFrequencyBound m ω * |v-w|) * twoBandFrequencyBound m ω := by
      rw [hNorm]
      exact mul_le_mul (mul_le_mul_of_nonneg_right (twoBand_resolvent_bound hm v ω).1 (abs_nonneg _))
        (twoBand_resolvent_bound hm w ω).1 (norm_nonneg _) (by unfold twoBandFrequencyBound; positivity)
    _ = _ := by ring

theorem twoBand_frequency_bound_sq (m ω : ℝ) :
    (twoBandFrequencyBound m ω)^2 = (ω^2 + m^2)⁻¹ := by
  unfold twoBandFrequencyBound
  rw [inv_pow, Real.sq_sqrt (by positivity)]

theorem twoBand_frequency_integral {m : ℝ} (hm : 0 < m) :
    Integrable (fun ω : ℝ => (twoBandFrequencyBound m ω)^2) ∧
      (∫ ω : ℝ, (twoBandFrequencyBound m ω)^2) = Real.pi / m := by
  let F := fun ν : ℝ => (1+ν^2)⁻¹
  have eq (ω : ℝ) : (twoBandFrequencyBound m ω)^2 = (m^2)⁻¹ * F (m⁻¹*ω) := by
    rw [twoBand_frequency_bound_sq]
    dsimp only [F]
    field_simp [hm.ne']
    ring
  have hi := (integrable_comp_mul_left_iff F (inv_ne_zero hm.ne')).2 integrable_inv_one_add_sq
  refine ⟨(hi.const_mul _).congr (Filter.Eventually.of_forall (fun ω => (eq ω).symm)), ?_⟩
  have scale : (∫ ω : ℝ, F (m⁻¹*ω)) = m * Real.pi := by
    simpa only [inv_inv, abs_of_pos hm, smul_eq_mul, F, integral_univ_inv_one_add_sq] using
      Measure.integral_comp_mul_left F m⁻¹
  simp only [eq, integral_const_mul, scale]
  field_simp

theorem twoBand_trace_norm (A : TwoBandMatrix) : ‖A.trace‖ ≤ 2*‖A‖ := by
  have entry (i : Fin 2) : ‖A i i‖ ≤ ‖A‖ := by
    let u := EuclideanSpace.single i (1:ℂ)
    let w := (EuclideanSpace.equiv (Fin 2) ℂ).symm (A *ᵥ u)
    have h := Matrix.l2_opNorm_mulVec A u
    rw [show ‖u‖ = 1 by simp [u], mul_one] at h
    have hi : w i = A i i := by
      change (A *ᵥ (Pi.single i 1)) i = _
      rw [Matrix.mulVec_single_one]
      rfl
    rw [← hi]
    exact (PiLp.norm_apply_le w i).trans h
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun i _ => entry i)).trans_eq (by simp))

end UV.SectorPlane
