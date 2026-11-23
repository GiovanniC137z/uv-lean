import UV.ContinueRelativeSoftContactTrace
import UV.ContinueRelativeChargeRadial

/-! Integration by parts for the traced Hessian of the actual constant-field density. -/

noncomputable section

namespace UV.RelativeSoft

open UV.SectorPlane MeasureTheory Set Real Filter
open scoped Topology

local instance : MeasurableSpace EuclideanPlaneMomentum := borel _
local instance : BorelSpace EuclideanPlaneMomentum := ⟨rfl⟩

private def contactAtRadius (m σ r : ℝ) : ℝ :=
  (4/(m^2+r^2))*r^2*(4*σ^4*r^2-12*σ^2)*exp (-(σ^2*r^2))

private def differenceAtRadius (m σ r : ℝ) : ℝ :=
  softLinearTraceAtRadius m σ r + contactAtRadius m σ r

private def contactDifference (x y : ℝ) : ℝ :=
  chordLinearIntegrand x y + chordContactTraceIntegrand x y

private theorem contact_difference_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (contactDifference x) (Ioi 0) :=
  (chord_linear_integrable hx).add (chord_contact_trace_integrable hx)

private theorem contact_difference_zero {x : ℝ} (hx : 0 < x) :
    (∫ y in Ioi (0:ℝ), contactDifference x y) = 0 := by
  unfold contactDifference
  rw [integral_add (chord_linear_integrable hx) (chord_contact_trace_integrable hx),
    chord_contact_trace_integral hx,← chord_b_eq_integral_linear hx,add_neg_cancel]

private theorem contact_difference_density (m : ℝ) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    r^3 * differenceAtRadius m σ r =
      (2/σ^2) * (|2*σ^2*r| • contactDifference ((m*σ)^2) (σ^2*r^2)) := by
  have hd : m^2+r^2 ≠ 0 := by positivity
  have hh : (m*σ)^2+σ^2*r^2 ≠ 0 := by positivity
  rw [abs_of_pos (by positivity),smul_eq_mul]
  unfold differenceAtRadius softLinearTraceAtRadius tangentialChord radialChord contactAtRadius
    contactDifference chordLinearIntegrand chordContactTraceIntegrand
  field_simp
  ring

private theorem contact_difference_radial_integrable {m σ : ℝ} (hm : m ≠ 0) (hσ : 0 < σ) :
    IntegrableOn (fun r => r^3 * differenceAtRadius m σ r) (Ioi 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun r _ => (squared_radius_derivative σ r).hasDerivWithinAt)
    (squared_radius_injective hσ) (contactDifference ((m*σ)^2))
  rw [squared_radius_image hσ] at h
  have ht : 0 < (m*σ)^2 := sq_pos_of_ne_zero (mul_ne_zero hm hσ.ne')
  refine ((h.mp (contact_difference_integrable ht)).const_mul (2/σ^2)).congr ?_
  exact (ae_restrict_mem measurableSet_Ioi).mono fun _ hr => (contact_difference_density m hσ hr).symm

private theorem contact_difference_radial_integral {m σ : ℝ} (hm : m ≠ 0) (hσ : 0 < σ) :
    (∫ k : EuclideanPlaneMomentum, differenceAtRadius m σ ‖k‖) = 0 := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun r _ => (squared_radius_derivative σ r).hasDerivWithinAt)
    (squared_radius_injective hσ) (contactDifference ((m*σ)^2))
  rw [squared_radius_image hσ,contact_difference_zero (sq_pos_of_ne_zero (mul_ne_zero hm hσ.ne'))] at h
  rw [soft_four_volume_radial]
  have he : (∫ r in Ioi (0:ℝ), r^3 * differenceAtRadius m σ r) =
      (2/σ^2) * ∫ r in Ioi (0:ℝ), |2*σ^2*r| • contactDifference ((m*σ)^2) (σ^2*r^2) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun _ hr => contact_difference_density m hσ hr
  rw [he,← h,mul_zero,mul_zero]

private theorem combined_cartesian_trace_ae (m σ : ℝ) :
    (fun k : EuclideanPlaneMomentum => LinearMap.trace ℝ EuclideanPlaneMomentum
        ((softLogHessian m k).toLinearMap*((softChordDifferential σ k).toLinearMap)^2) +
        contactAtRadius m σ ‖k‖)
    =ᵐ[(volume : Measure EuclideanPlaneMomentum)]
      (fun k => softCartesianTrace m σ k + differenceAtRadius m σ ‖k‖) := by
  have h : ∀ᵐ k ∂(volume : Measure EuclideanPlaneMomentum), k ≠ 0 :=
    ae_iff.mpr (by simpa only [not_ne_iff, setOf_eq_eq_singleton] using
      (measure_singleton (μ := (volume : Measure EuclideanPlaneMomentum)) (0 : EuclideanPlaneMomentum)))
  filter_upwards [h] with k hk
  rw [differenceAtRadius,← soft_cartesian_linear_eq_radial m σ hk,softCartesianTrace,
    mul_sub,map_sub,softCartesianLinearTrace]
  ring

/-- The actual four directional second derivatives integrate to the soft
response. The radial proof accounts for the complete signed contact term. -/
theorem constant_field_trace_response
    (b : OrthonormalBasis (Fin 4) ℝ EuclideanPlaneMomentum)
    (e : ℝ) {m σ : ℝ} (hm : m ≠ 0) (hσ : 0 < σ) :
    (∫ k : EuclideanPlaneMomentum,
      ∑ i, deriv (deriv (constantFieldDensity e m σ k (softBasisDirection b i))) 0)
      / (4*(2*π)^4) = relativeSoftResponse e m σ := by
  simp_rw [constant_field_full_trace b e σ hm]
  change (∫ k : EuclideanPlaneMomentum, e^2 * (LinearMap.trace ℝ EuclideanPlaneMomentum
    ((softLogHessian m k).toLinearMap*((softChordDifferential σ k).toLinearMap)^2) +
    contactAtRadius m σ ‖k‖)) / (4*(2*π)^4) = _
  rw [integral_const_mul,integral_congr_ae (combined_cartesian_trace_ae m σ)]
  have hI : Integrable (fun k : EuclideanPlaneMomentum => differenceAtRadius m σ ‖k‖) := by
    apply (integrable_fun_norm_addHaar volume).mpr
    simpa only [soft_momentum_finrank,show (4:ℕ)-1=3 by decide,smul_eq_mul] using
      contact_difference_radial_integrable hm hσ
  rw [integral_add (soft_cartesian_trace_integrable m hσ) hI,contact_difference_radial_integral hm hσ,add_zero,
    ← soft_cartesian_response_eq e m hσ]
  ring

def sharedConstantFieldTrace {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (σ : α → ℝ) (b : OrthonormalBasis (Fin 4) ℝ EuclideanPlaneMomentum) (e m : ℝ) : ℝ :=
  ∫ r, (∫ k : EuclideanPlaneMomentum,
    ∑ i, deriv (deriv (constantFieldDensity e m (σ r) k (softBasisDirection b i))) 0)
    / (4*(2*π)^4) ∂μ

theorem shared_constant_field_trace_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {σ : α → ℝ}
    (hσ : ∀ᵐ r ∂μ, 0 < σ r) (b : OrthonormalBasis (Fin 4) ℝ EuclideanPlaneMomentum)
    (e : ℝ) {m : ℝ} (hm : m ≠ 0) :
    sharedConstantFieldTrace μ σ b e m = sharedSoftResponse μ σ e m :=
  integral_congr_ae (hσ.mono fun _ hr => constant_field_trace_response b e hm hr)

/-- Both constants in the corrected display for the shared, integrated constant-field trace. -/
theorem shared_constant_field_trace_limits {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {σ : α → ℝ} (hσ : Measurable σ)
    (hpos : ∀ᵐ r ∂μ, 0 < σ r) (h₄ : Integrable (fun r => (σ r ^ 4)⁻¹) μ)
    (b : OrthonormalBasis (Fin 4) ℝ EuclideanPlaneMomentum) (e : ℝ) :
    Tendsto (sharedConstantFieldTrace μ σ b e) (𝓝[>] 0)
      (𝓝 ((-3*e^2/(16*π^2)) * ∫ r, (σ r ^ 2)⁻¹ ∂μ)) ∧
    Tendsto (fun m : ℝ => m^2 * sharedConstantFieldTrace μ σ b e m) atTop
      (𝓝 ((3*e^2/(32*π^2)) * ∫ r, (σ r ^ 4)⁻¹ ∂μ)) := by
  constructor
  · apply (shared_soft_response_zero_right hσ h₄ e).congr'
    filter_upwards [self_mem_nhdsWithin (s := Ioi (0:ℝ))] with m hm
    exact (shared_constant_field_trace_eq hpos b e (ne_of_gt hm)).symm
  · apply (shared_soft_response_mass_atTop hσ hpos h₄ e).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with m hm
    rw [shared_constant_field_trace_eq hpos b e hm.ne']

theorem shared_constant_field_trace_positive_zero {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {σ : α → ℝ} (hσ : Measurable σ)
    (hpos : ∀ᵐ r ∂μ, 0 < σ r) (h₄ : Integrable (fun r => (σ r ^ 4)⁻¹) μ)
    (b : OrthonormalBasis (Fin 4) ℝ EuclideanPlaneMomentum) {e : ℝ} (he : e ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ sharedConstantFieldTrace μ σ b e m = 0 := by
  obtain ⟨m,hm,hzero⟩ := shared_soft_response_positive_zero hσ hpos h₄ he
  rw [← shared_constant_field_trace_eq hpos b e hm.ne'] at hzero
  exact ⟨m,hm,hzero⟩

end UV.RelativeSoft
