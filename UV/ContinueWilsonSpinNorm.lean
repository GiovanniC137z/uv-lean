import UV.ContinueWilsonMarkedHop
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Operator-norm estimates in the four-component Euclidean spinor
space for the actual spin weight and marked momentum-space hop. -/

noncomputable section

open MeasureTheory Set Filter Metric UV.SectorPlane
open scoped Topology RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace UV

theorem wilson_slash_hermitian (d : OSFourSpace) : (diracSlash d)ᴴ = diracSlash d := by
  simp [diracSlash,Matrix.conjTranspose_sum,Matrix.conjTranspose_smul,
    show ∀ k : Fin 4, (euclideanGamma k)ᴴ = euclideanGamma k from euclideanGamma_isHermitian]

theorem wilson_slash_opnorm (d : OSFourSpace) : ‖diracSlash d‖ = ‖d‖ := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (diracSlash d)
  rw [wilson_slash_hermitian,diracSlash_sq,norm_smul,norm_one,mul_one,Complex.norm_real,
    Real.norm_of_nonneg (sq_nonneg _)] at h
  nlinarith [norm_nonneg (diracSlash d), norm_nonneg d]

theorem wilson_spin_weight_opnorm {L : ℝ} (hL : 0 < L) {d : OSFourSpace} (hd : ‖d‖ ≤ 2*L) :
    ‖wilsonSpinWeight L d‖ ≤ 2 := by
  unfold wilsonSpinWeight
  apply (norm_sub_le _ _).trans
  rw [norm_one,norm_smul,wilson_slash_opnorm,norm_div,norm_one,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg hL.le]
  norm_num
  have h := (div_le_one (by positivity : 0 < 2*L)).mpr hd
  rw [show L⁻¹*(1/2)*‖d‖ = ‖d‖/(2*L) by simp only [div_eq_mul_inv,mul_inv_rev]; ring]
  linarith

theorem wilson_matrix_entry_le_opnorm (A : DiracMatrix) (i j : Fin 4) : ‖A i j‖ ≤ ‖A‖ := by
  let v := EuclideanSpace.single j (1:ℂ)
  have h := Matrix.l2_opNorm_mulVec A v
  have he : ‖v‖ = 1 := by simp [v]
  rw [he,mul_one] at h
  let w := (EuclideanSpace.equiv (Fin 4) ℂ).symm (A *ᵥ v)
  have hv : (v : Fin 4 → ℂ) = Pi.single j 1 := rfl
  have hi : w i = A i j := by
    change (A *ᵥ (v : Fin 4 → ℂ)) i = _
    rw [hv,Matrix.mulVec_single_one]
    rfl
  rw [←hi]
  exact (PiLp.norm_apply_le w i).trans h

theorem wilson_trace_le_opnorm (A : DiracMatrix) : ‖A.trace‖ ≤ 4*‖A‖ := by
  apply (norm_sum_le _ _).trans
  calc
    (∑ i : Fin 4, ‖A i i‖) ≤ ∑ _ : Fin 4, ‖A‖ := Finset.sum_le_sum (fun i _ => wilson_matrix_entry_le_opnorm A i i)
    _ = _ := by simp

theorem wilson_direction_weight_bound (us : WilsonDirections) (d : OSFourSpace) :
    ‖wilsonDirectionWeight us d‖ ≤ ‖d‖^us.length := by
  induction us with
  | nil => simp [wilsonDirectionWeight]
  | cons u us ih =>
    have h := abs_real_inner_le_norm u.val d
    rw [u.property,one_mul] at h
    simp only [wilsonDirectionWeight,norm_mul,Complex.norm_real,Real.norm_eq_abs,List.length_cons,pow_succ]
    rw [mul_comm (‖d‖^us.length)]
    exact mul_le_mul h ih (norm_nonneg _) (norm_nonneg _)

def wilsonSpinHopMatrix (L : ℝ) {ι : Type*} [Fintype ι] (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (us : WilsonDirections) (p : OSFourSpace) : DiracMatrix :=
  ∫ d, (thinPlaneWave p d * wilsonDirectionWeight us d) • wilsonSpinWeight L d ∂wilsonDisplacementMeasure L T

theorem wilson_spin_weight_continuous (L : ℝ) : Continuous (wilsonSpinWeight L) := by
  unfold wilsonSpinWeight diracSlash
  apply continuous_const.sub
  apply continuous_const.smul
  apply continuous_finset_sum
  intro k _
  exact (Complex.continuous_ofReal.comp (EuclideanSpace.proj k).continuous).smul continuous_const

variable {ι : Type*} [Fintype ι]

theorem wilson_spin_matrix_integrand {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (us : WilsonDirections) (p : OSFourSpace) :
    Integrable (fun d => (thinPlaneWave p d*wilsonDirectionWeight us d) • wilsonSpinWeight L d) (wilsonDisplacementMeasure L T) := by
  have hc := ((show Continuous (thinPlaneWave p) by unfold thinPlaneWave; fun_prop).mul
    (wilson_direction_weight_continuous us)).smul (wilson_spin_weight_continuous L)
  have hs : ∀ᵐ d ∂wilsonDisplacementMeasure L T, d ∈ closedBall 0 (2*L) := by
    simpa only [mem_closedBall,dist_zero_right] using wilson_displacement_band hL.le T
  have hi := hc.continuousOn.integrableOn_compact (μ := wilsonDisplacementMeasure L T) (isCompact_closedBall 0 (2*L))
  rwa [IntegrableOn,Measure.restrict_eq_self_of_ae_mem hs] at hi

theorem wilson_spin_hop_entry {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (us : WilsonDirections) (p : OSFourSpace) (i j : Fin 4) :
    wilsonSpinHopMatrix L T us p i j = wilsonMarkedSpinHop L T us i j p := by
  let e : DiracMatrix →ₗ[ℂ] ℂ := { toFun := fun A => A i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have he := e.toContinuousLinearMap.integral_comp_comm (wilson_spin_matrix_integrand hL T us p)
  exact he.symm

theorem wilson_spin_hop_opnorm {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (us : WilsonDirections) (p : OSFourSpace) : ‖wilsonSpinHopMatrix L T us p‖ ≤ 2*(2*L)^us.length := by
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (integrable_const (2*(2*L)^us.length)) ?_).trans_eq (by simp)
  filter_upwards [wilson_displacement_band hL.le T] with d hd
  rw [norm_smul,norm_mul,wilson_wave_norm,one_mul,mul_comm (2:ℝ)]
  exact mul_le_mul ((wilson_direction_weight_bound us d).trans (pow_le_pow_left₀ (norm_nonneg _) hd _))
    (wilson_spin_weight_opnorm hL hd) (norm_nonneg _) (by positivity)

end UV
