import UV.ContinueRelativeSoftShape
import Mathlib.Topology.Order.IntermediateValue

/-! Fixed-width and shared-depth limits of the radial transverse soft response. -/

noncomputable section

namespace UV.RelativeSoft

open MeasureTheory Filter Set Real
open scoped Topology

/-- The manuscript's scalar radial response with the four-dimensional normalization. -/
def relativeSoftResponse (e m σ : ℝ) : ℝ :=
  (e^2 / (16 * π^2)) * (σ^2)⁻¹ * relativeSoftShape (m*σ)

def sharedSoftResponse {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (σ : α → ℝ) (e m : ℝ) : ℝ :=
  ∫ r, relativeSoftResponse e m (σ r) ∂μ

theorem relative_soft_response_continuous (e σ : ℝ) :
    Continuous (fun m => relativeSoftResponse e m σ) := by
  unfold relativeSoftResponse
  exact continuous_const.mul (relative_soft_shape_continuous.comp (continuous_id.mul continuous_const))

theorem relative_soft_response_zero (e σ : ℝ) :
    relativeSoftResponse e 0 σ = (-3*e^2/(16*π^2)) * (σ^2)⁻¹ := by
  rw [relativeSoftResponse,zero_mul,relative_soft_shape_zero]
  ring

theorem relative_soft_response_mass_weight (e m : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    m^2 * relativeSoftResponse e m σ =
      (e^2 / (16*π^2)) * (σ^4)⁻¹ * ((m*σ)^2 * relativeSoftShape (m*σ)) := by
  unfold relativeSoftResponse
  field_simp [hσ.ne',Real.pi_ne_zero]

theorem relative_soft_response_mass_atTop (e : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun m : ℝ => m^2 * relativeSoftResponse e m σ) atTop
      (𝓝 ((3*e^2/(32*π^2)) * (σ^4)⁻¹)) := by
  have h := (relative_soft_shape_mass_atTop.comp
    ((tendsto_mul_const_atTop_of_pos hσ).mpr tendsto_id)).const_mul
      ((e^2/(16*π^2)) * (σ^4)⁻¹)
  have he : ((e^2/(16*π^2)) * (σ^4)⁻¹) * (3/2) =
      (3*e^2/(32*π^2)) * (σ^4)⁻¹ := by ring
  rw [he] at h
  exact h.congr' (Eventually.of_forall fun m => (relative_soft_response_mass_weight e m hσ).symm)

private theorem inv_square_integrable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {σ : α → ℝ} (hσ : Measurable σ)
    (h₄ : Integrable (fun r => (σ r ^ 4)⁻¹) μ) : Integrable (fun r => (σ r ^ 2)⁻¹) μ := by
  have hm : Measurable (fun r => (σ r ^ 2)⁻¹) := by fun_prop
  refine ((integrable_const (1:ℝ)).add h₄).mono' hm.aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  change ‖(σ r ^ 2)⁻¹‖ ≤ 1 + (σ r ^ 4)⁻¹
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg (σ r)))]
  have h : ((σ r ^ 2)⁻¹)^2 = (σ r ^ 4)⁻¹ := by
    rw [← inv_pow, ← pow_mul]
    norm_num
  rw [← h]
  nlinarith [sq_nonneg ((σ r ^ 2)⁻¹ - 1/2)]

private theorem relative_soft_response_measurable {α : Type*} [MeasurableSpace α]
    {σ : α → ℝ} (hσ : Measurable σ) (e m : ℝ) :
    Measurable (fun r => relativeSoftResponse e m (σ r)) := by
  have hr : Measurable (fun r => relativeSoftShape (m * σ r)) :=
    relative_soft_shape_continuous.measurable.comp (hσ.const_mul m)
  unfold relativeSoftResponse
  fun_prop

theorem shared_soft_response_continuous {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {σ : α → ℝ} (hσ : Measurable σ)
    (h₄ : Integrable (fun r => (σ r ^ 4)⁻¹) μ) (e : ℝ) :
    Continuous (fun m => sharedSoftResponse μ σ e m) := by
  obtain ⟨B,_,_,_,hB⟩ := relative_soft_shape_bounds
  apply continuous_iff_continuousAt.mpr
  intro m
  unfold ContinuousAt sharedSoftResponse
  apply tendsto_integral_filter_of_dominated_convergence
    (fun r => (e^2/(16*π^2)*B) * (σ r ^ 2)⁻¹)
  · exact Eventually.of_forall fun t => (relative_soft_response_measurable hσ e t).aestronglyMeasurable
  · exact Eventually.of_forall fun t => Eventually.of_forall fun r => by
      unfold relativeSoftResponse
      have he : 0 ≤ e^2/(16*π^2) := by positivity
      have hr : 0 ≤ (σ r ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
      rw [norm_mul,Real.norm_of_nonneg (mul_nonneg he hr)]
      calc
        _ ≤ e^2/(16*π^2)*(σ r ^ 2)⁻¹*B :=
          mul_le_mul_of_nonneg_left (hB (t*σ r)).1 (mul_nonneg he hr)
        _ = _ := by ring
  · exact (inv_square_integrable hσ h₄).const_mul _
  · exact Eventually.of_forall fun r => (relative_soft_response_continuous e (σ r)).continuousAt

theorem shared_soft_response_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (σ : α → ℝ) (e : ℝ) :
    sharedSoftResponse μ σ e 0 = (-3*e^2/(16*π^2)) * ∫ r, (σ r ^ 2)⁻¹ ∂μ := by
  simp only [sharedSoftResponse,relative_soft_response_zero,integral_const_mul]

/-- The first equality in the corrected display, with the approach from positive masses. -/
theorem shared_soft_response_zero_right {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {σ : α → ℝ} (hσ : Measurable σ)
    (h₄ : Integrable (fun r => (σ r ^ 4)⁻¹) μ) (e : ℝ) :
    Tendsto (sharedSoftResponse μ σ e) (𝓝[>] 0)
      (𝓝 ((-3*e^2/(16*π^2)) * ∫ r, (σ r ^ 2)⁻¹ ∂μ)) := by
  rw [← shared_soft_response_zero]
  exact (shared_soft_response_continuous hσ h₄ e).continuousAt.continuousWithinAt

/-- The second equality in the corrected display, for the same mass-independent law. -/
theorem shared_soft_response_mass_atTop {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {σ : α → ℝ} (hσ : Measurable σ) (hpos : ∀ᵐ r ∂μ, 0 < σ r)
    (h₄ : Integrable (fun r => (σ r ^ 4)⁻¹) μ) (e : ℝ) :
    Tendsto (fun m : ℝ => m^2 * sharedSoftResponse μ σ e m) atTop
      (𝓝 ((3*e^2/(32*π^2)) * ∫ r, (σ r ^ 4)⁻¹ ∂μ)) := by
  obtain ⟨_,B,_,_,hB⟩ := relative_soft_shape_bounds
  unfold sharedSoftResponse
  simp_rw [← integral_const_mul]
  apply tendsto_integral_filter_of_dominated_convergence
    (fun r => (e^2/(16*π^2)*B) * (σ r ^ 4)⁻¹)
  · exact Eventually.of_forall fun m =>
      ((relative_soft_response_measurable hσ e m).const_mul (m^2)).aestronglyMeasurable
  · exact Eventually.of_forall fun m => hpos.mono fun r hr => by
      rw [relative_soft_response_mass_weight e m hr,norm_mul,
        Real.norm_of_nonneg (by positivity : 0 ≤ e^2/(16*π^2)*(σ r ^ 4)⁻¹)]
      calc
        _ ≤ e^2/(16*π^2)*(σ r ^ 4)⁻¹*B := mul_le_mul_of_nonneg_left (hB (m*σ r)).2 (by positivity)
        _ = _ := by ring
  · exact h₄.const_mul _
  · exact hpos.mono fun _ hr => relative_soft_response_mass_atTop e hr

private theorem inv_moment_pos {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {σ : α → ℝ}
    (hpos : ∀ᵐ r ∂μ, 0 < σ r) {n : ℕ} (hn : Integrable (fun r => (σ r ^ n)⁻¹) μ) :
    0 < ∫ r, (σ r ^ n)⁻¹ ∂μ := by
  have hp : ∀ᵐ r ∂μ, 0 < (σ r ^ n)⁻¹ := hpos.mono fun r hr => inv_pos.mpr (pow_pos hr n)
  have hh : 0 ≤ᵐ[μ] (fun r => (σ r ^ n)⁻¹) := hp.mono fun _ hr => hr.le
  refine lt_of_le_of_ne (integral_nonneg_of_ae hh) fun hz => ?_
  have he := (integral_eq_zero_iff_of_nonneg_ae hh hn).mp hz.symm
  have hf : ∀ᵐ _r ∂μ, False := (hp.and he).mono fun r hr => hr.1.ne' hr.2
  simp at hf
  exact (NeZero.ne μ) hf

/-- Nonzero charge has a positive matching mass for every admissible fixed depth law. -/
theorem shared_soft_response_positive_zero {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {σ : α → ℝ} (hσ : Measurable σ)
    (hpos : ∀ᵐ r ∂μ, 0 < σ r) (h₄ : Integrable (fun r => (σ r ^ 4)⁻¹) μ)
    {e : ℝ} (he : e ≠ 0) : ∃ m : ℝ, 0 < m ∧ sharedSoftResponse μ σ e m = 0 := by
  have he₂ : 0 < e^2 := sq_pos_of_ne_zero he
  have h₂ : 0 < ∫ r, (σ r ^ 2)⁻¹ ∂μ := inv_moment_pos hpos (inv_square_integrable hσ h₄)
  have h₀ : sharedSoftResponse μ σ e 0 < 0 := by
    rw [shared_soft_response_zero]
    apply mul_neg_of_neg_of_pos _ h₂
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  have hm₄ : 0 < ∫ r, (σ r ^ 4)⁻¹ ∂μ := inv_moment_pos hpos h₄
  have hposlimit : 0 < (3*e^2/(32*π^2)) * ∫ r, (σ r ^ 4)⁻¹ ∂μ := by positivity
  obtain ⟨M,hM,hs⟩ := ((eventually_gt_atTop (0:ℝ)).and
    ((shared_soft_response_mass_atTop hσ hpos h₄ e).eventually (eventually_gt_nhds hposlimit))).exists
  have hhi : 0 < sharedSoftResponse μ σ e M :=
    pos_of_mul_pos_right hs (sq_nonneg M)
  have hcont := shared_soft_response_continuous hσ h₄ e
  obtain ⟨m,hm,hmzero⟩ := intermediate_value_Icc hM.le hcont.continuousOn
    (show (0:ℝ) ∈ Icc (sharedSoftResponse μ σ e 0) (sharedSoftResponse μ σ e M) from ⟨h₀.le,hhi.le⟩)
  refine ⟨m,lt_of_le_of_ne hm.1 ?_,hmzero⟩
  intro h
  rw [← h] at hmzero
  exact h₀.ne hmzero

end UV.RelativeSoft
