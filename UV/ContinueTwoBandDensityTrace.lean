import UV.ContinueTwoBandResolvent

/-! Exact scalar and single-contact traces of the same two-band inverse.
The Euclidean frequencies are independent real carrier coordinates. -/

noncomputable section
open Matrix Filter
open scoped Matrix Matrix.Norms.L2Operator Topology

namespace UV.SectorPlane

def twoBandTraceFormula (m v w ξ η : ℝ) : ℝ :=
  2*(m^2 + v*w - ξ*η)/(twoBandInversionFactor m v ξ * twoBandInversionFactor m w η)

theorem twoBand_trace_pair (m v w ξ η : ℝ) :
    (twoBandResolvent m v ξ * twoBandResolvent m w η).trace =
      (twoBandTraceFormula m v w ξ η : ℂ) := by
  have h : (twoBandNumerator m v ξ * twoBandNumerator m w η).trace =
      2*((m:ℂ)^2 + (v:ℂ)*w - (ξ:ℂ)*η) := by
    rw [Matrix.trace, Fin.sum_univ_two]
    simp [twoBandNumerator]
    ring_nf
    rw [Complex.I_sq]
    ring
  unfold twoBandResolvent twoBandTraceFormula
  rw [smul_mul_assoc, mul_smul_comm, Matrix.trace_smul, Matrix.trace_smul, h]
  push_cast
  simp only [smul_eq_mul, div_eq_mul_inv, _root_.mul_inv_rev]
  ring

theorem twoBand_trace_contact (m v ξ : ℝ) :
    (twoBandResolvent m v ξ * twoBandMix).trace =
      ((2*v/twoBandInversionFactor m v ξ : ℝ) : ℂ) := by
  unfold twoBandResolvent
  rw [smul_mul_assoc, Matrix.trace_smul, Matrix.trace, Fin.sum_univ_two]
  simp [twoBandNumerator, twoBandMix]
  simp only [div_eq_mul_inv]
  ring

def twoBandRelativeBubble (m v w ξ η : ℝ) : ℝ :=
  twoBandTraceFormula m v w ξ η - twoBandTraceFormula m 0 0 ξ η

/-- The completed two-density trace has both terms at the same momentum. -/
theorem twoBand_relative_bubble_trace (m v w ξ η : ℝ) :
    (twoBandResolvent m v ξ * twoBandResolvent m w η -
      twoBandResolvent m 0 ξ * twoBandResolvent m 0 η).trace =
      (twoBandRelativeBubble m v w ξ η : ℂ) := by
  rw [Matrix.trace_sub, twoBand_trace_pair, twoBand_trace_pair, twoBandRelativeBubble, Complex.ofReal_sub]

private def twoBandReciprocalScale (m v w η s : ℝ) : ℝ :=
  2*(s*(m^2+v*w)-η)/((1+s^2*(m^2+v^2))*twoBandInversionFactor m w η)

private theorem twoBand_reciprocal_scale {m : ℝ} (hm : 0 < m) (v w η : ℝ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ξ * twoBandTraceFormula m v w ξ η = twoBandReciprocalScale m v w η ξ⁻¹ := by
  have hD : 0 < twoBandInversionFactor m w η := by
    unfold twoBandInversionFactor
    positivity
  have hG : 0 < 1 + (ξ⁻¹)^2*(m^2+v^2) := by positivity
  have hL : 0 < twoBandInversionFactor m v ξ := by
    unfold twoBandInversionFactor
    positivity
  unfold twoBandTraceFormula twoBandReciprocalScale
  field_simp [hD.ne', hG.ne', hL.ne', hξ]
  unfold twoBandInversionFactor
  ring

private theorem twoBand_reciprocal_scale_continuous {m : ℝ} (hm : 0 < m) (v w η : ℝ) :
    Continuous (twoBandReciprocalScale m v w η) := by
  unfold twoBandReciprocalScale
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro s
  unfold twoBandInversionFactor
  positivity

private theorem twoBand_reciprocal_scale_zero {m : ℝ} (hm : 0 < m) (v w η : ℝ) :
    twoBandReciprocalScale m v w η 0 - twoBandReciprocalScale m 0 0 η 0 =
      2*η*w^2/((η^2+m^2)*(η^2+m^2+w^2)) := by
  have hL : 0 < η^2 + m^2 + w^2 := by positivity
  have hL₀ : 0 < η^2+m^2 := by positivity
  simp [twoBandReciprocalScale, twoBandInversionFactor]
  field_simp [hL.ne', hL₀.ne']
  ring

/-- An independently hard Euclidean carrier frequency leaves a nonzero
first-order tail in the relative density word when the other hop is nonzero. -/
theorem twoBand_coulomb_scaled_limit {m : ℝ} (hm : 0 < m) (v w η : ℝ) :
    Tendsto (fun ξ => ξ * twoBandRelativeBubble m v w ξ η) atTop
      (𝓝 (2*η*w^2/((η^2+m^2)*(η^2+m^2+w^2)))) ∧
    Tendsto (fun ξ => ξ * twoBandRelativeBubble m v w ξ η) atBot
      (𝓝 (2*η*w^2/((η^2+m^2)*(η^2+m^2+w^2)))) := by
  let G := fun s => twoBandReciprocalScale m v w η s - twoBandReciprocalScale m 0 0 η s
  have hG : Continuous G := (twoBand_reciprocal_scale_continuous hm v w η).sub
    (twoBand_reciprocal_scale_continuous hm 0 0 η)
  have hZero : G 0 = _ := twoBand_reciprocal_scale_zero hm v w η
  have hSame (ξ : ℝ) (hξ : ξ ≠ 0) : G ξ⁻¹ = ξ * twoBandRelativeBubble m v w ξ η := by
    unfold G twoBandRelativeBubble
    rw [mul_sub, twoBand_reciprocal_scale hm v w η hξ, twoBand_reciprocal_scale hm 0 0 η hξ]
  rw [← hZero]
  constructor
  · apply (hG.continuousAt.tendsto.comp tendsto_inv_atTop_zero).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with ξ hξ
    exact hSame ξ hξ.ne'
  · apply (hG.continuousAt.tendsto.comp tendsto_inv_atBot_zero).congr'
    filter_upwards [eventually_lt_atBot (0:ℝ)] with ξ hξ
    exact hSame ξ hξ.ne

end UV.SectorPlane
