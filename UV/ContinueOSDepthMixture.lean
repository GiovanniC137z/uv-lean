import UV.ContinueOSJointPlane

/-! One pair of source probes detects the obstruction after integration over
a positive depth law. Its real coefficient is chosen after averaging. -/

noncomputable section

open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap ComplexConjugate Topology

namespace UV

theorem osReflectedBlock_measurable {m : ℝ} (hm : 0 < m) (f g : OSProbe) :
    Measurable (fun a => osReflectedBlock m a f g) := by
  have hF : Continuous (𝓕 f) := (SchwartzMap.fourierTransformCLM ℂ f).continuous
  have hG : Continuous (𝓕 g) := (SchwartzMap.fourierTransformCLM ℂ g).continuous
  have h : Continuous (fun p : ℝ × OSFourSpace => conj (𝓕 f (osTimeReflect p.2)) *
      (osCovWeight m p.1 p.2 : ℂ) * 𝓕 g p.2) := by
    have hc : Continuous (fun p : ℝ × OSFourSpace => osCovWeight m p.1 p.2) := by
      unfold osCovWeight osTransferSymbol osMassiveSymbol
      fun_prop (disch := intro x; positivity)
    exact (((Complex.continuous_conj.comp (hF.comp (osTimeReflect_continuous.comp continuous_snd))).mul
      (Complex.continuous_ofReal.comp hc)).mul (hG.comp continuous_snd))
  exact (h.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

theorem osReflectedBlock_norm_bound {m a : ℝ} (hm : 0 < m) (ha : 0 ≤ a) (f g : OSProbe) :
    ‖osReflectedBlock m a f g‖ ≤
      ‖(SchwartzMap.fourierTransformCLM ℂ f).toBoundedContinuousFunction‖ *
        (m ^ 2)⁻¹ * ∫ k, ‖𝓕 g k‖ := by
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let G := SchwartzMap.fourierTransformCLM ℂ g
  rw [← integral_const_mul]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono (osReflectedBlock_integrable hm ha f g).norm
    (G.integrable.norm.const_mul _)
  intro k
  dsimp only
  rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real,
    Real.norm_of_nonneg (osCovWeight_bound hm ha k).1]
  exact mul_le_mul_of_nonneg_right (mul_le_mul
    (F.toBoundedContinuousFunction.norm_coe_le_norm _) (osCovWeight_bound hm ha k).2
      (osCovWeight_bound hm ha k).1 (norm_nonneg _)) (norm_nonneg _)

theorem osReflectedBlock_depth_integrable {m : ℝ} (hm : 0 < m)
    {ρ : Measure ℝ} [IsFiniteMeasure ρ] {a : ℝ → ℝ} (hame : Measurable a)
    (ha : ∀ᵐ r ∂ρ, 0 ≤ a r) (f g : OSProbe) :
    Integrable (fun r => osReflectedBlock m (a r) f g) ρ := by
  apply (integrable_const _).mono' (((osReflectedBlock_measurable hm f g).comp hame).aestronglyMeasurable)
  exact ha.mono fun r hr => osReflectedBlock_norm_bound hm hr f g

theorem os_joint_positive_depth_mixture {m : ℝ} (hm : 0 < m) (ρ : Measure ℝ)
    [IsFiniteMeasure ρ] [NeZero ρ] (hr : ∀ᵐ r ∂ρ, 0 < r) :
    ∃ t : ℝ, (∫ r, osJointReflectedQuadratic m r t (osMassiveLocal m osBumpProbe) osBumpProbe ∂ρ) < 0 := by
  let f := osMassiveLocal m osBumpProbe
  let g := osBumpProbe
  let b := fun r => (osReflectedBlock m r f g).re
  let d := fun r => (osReflectedBlock m (r + r) g g).re
  have hb : Integrable b ρ := (osReflectedBlock_depth_integrable hm measurable_id
    (hr.mono fun _ h => h.le) f g).re
  have hd : Integrable d ρ := (osReflectedBlock_depth_integrable hm (measurable_id.add measurable_id)
    (hr.mono fun _ h => add_nonneg h.le h.le) g g).re
  have hp : ∀ᵐ r ∂ρ, 0 < b r := hr.mono fun _ h => osReflectedBlock_mixed_pos hm h
  have hs : Function.support b =ᵐ[ρ] (univ : Set ℝ) := by
    filter_upwards [hp] with r h
    exact propext (iff_true_intro h.ne')
  have hbpos : 0 < ∫ r, b r ∂ρ :=
    (integral_pos_iff_support_of_nonneg_ae (hp.mono fun _ h => h.le) hb).mpr (by
      rw [measure_congr hs]
      exact Measure.measure_univ_pos.mpr (NeZero.ne _))
  obtain ⟨t, ht⟩ := os_negative_of_zero_diagonal_nonzero_mixed hbpos.ne' (∫ r, d r ∂ρ)
  refine ⟨t, ?_⟩
  have he (r : ℝ) : osJointReflectedQuadratic m r t f g = (2 * t) * b r + d r := by
    have hcross := congrArg Complex.re (osReflectedBlock_hermitian m r f g)
    simp only [Complex.conj_re] at hcross
    simp only [osJointReflectedQuadratic, show osReflectedBlock m 0 f f = 0 from osReflectedBlock_null hm,
      Complex.zero_re, mul_zero, zero_add, ← hcross, b, d]
    ring
  change (∫ r, osJointReflectedQuadratic m r t f g ∂ρ) < 0
  simp only [he, integral_add (hb.const_mul _) hd, integral_const_mul]
  linarith

end UV
