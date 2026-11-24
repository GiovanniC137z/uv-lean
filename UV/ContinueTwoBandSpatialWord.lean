import UV.ContinueTwoBandDensityTrace
import UV.ContinueTwoBandRelativeWord

/-! Mixed scalar and spatial-contact traces on the same two-slot plane.
The geometric Wilson marks give scalar Fourier multipliers outside the
slot trace. The analytic bounds here track those multipliers explicitly. -/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace UV.SectorPlane

theorem twoBand_frequency_product {m : ℝ} (hm : 0 < m) (b c : ℝ) :
    Integrable (fun ξ => twoBandFrequencyBound m (ξ+b)*twoBandFrequencyBound m (ξ+c)) ∧
      (∫ ξ, twoBandFrequencyBound m (ξ+b)*twoBandFrequencyBound m (ξ+c)) ≤ Real.pi / m := by
  let F := twoBandFrequencyBound m
  have hF : Continuous F := by
    unfold F twoBandFrequencyBound
    exact (by fun_prop : Continuous (fun ξ : ℝ => Real.sqrt (ξ^2+m^2))).inv₀
      (fun ξ => (Real.sqrt_pos.mpr (by positivity)).ne')
  have h₁ := measurePreserving_add_right (volume : Measure ℝ) b
  have h₂ := measurePreserving_add_right (volume : Measure ℝ) c
  have ha : Integrable (fun ξ => (F (ξ+b))^2) :=
    h₁.integrable_comp_of_integrable (twoBand_frequency_integral hm).1
  have hb : Integrable (fun ξ => (F (ξ+c))^2) :=
    h₂.integrable_comp_of_integrable (twoBand_frequency_integral hm).1
  have hM : Integrable (fun ξ => ((F (ξ+b))^2+(F (ξ+c))^2)/2) := (ha.add hb).div_const 2
  have hLe (ξ : ℝ) : F (ξ+b)*F (ξ+c) ≤ ((F (ξ+b))^2+(F (ξ+c))^2)/2 := by
    nlinarith [sq_nonneg (F (ξ+b)-F (ξ+c))]
  have hMeas : AEStronglyMeasurable (fun ξ => F (ξ+b)*F (ξ+c)) volume :=
    ((hF.comp (continuous_id.add continuous_const)).mul
      (hF.comp (continuous_id.add continuous_const))).aestronglyMeasurable
  have hI : Integrable (fun ξ => F (ξ+b)*F (ξ+c)) := hM.mono' hMeas (ae_of_all _ (fun ξ => by
    rw [Real.norm_of_nonneg (by unfold F twoBandFrequencyBound; positivity)]
    exact hLe ξ))
  refine ⟨hI, (integral_mono hI hM hLe).trans_eq ?_⟩
  have h₁eq : (∫ ξ, (F (ξ+b))^2) = Real.pi / m :=
    (h₁.integral_comp (Homeomorph.addRight b).measurableEmbedding _).trans (twoBand_frequency_integral hm).2
  have h₂eq : (∫ ξ, (F (ξ+c))^2) = Real.pi / m :=
    (h₂.integral_comp (Homeomorph.addRight c).measurableEmbedding _).trans (twoBand_frequency_integral hm).2
  rw [integral_div, integral_add ha hb, h₁eq, h₂eq]
  ring

theorem twoBand_contact_trace_bound {m : ℝ} (hm : 0 < m) (v ξ : ℝ) :
    ‖(twoBandResolvent m v ξ * twoBandMix).trace‖ ≤ 2 * |v| * (twoBandFrequencyBound m ξ)^2 := by
  have hD : 0 < twoBandInversionFactor m v ξ := by
    unfold twoBandInversionFactor
    positivity
  have hR : 0 < ξ^2+m^2 := by positivity
  have hInv : (twoBandInversionFactor m v ξ)⁻¹ ≤ (ξ^2+m^2)⁻¹ :=
    inv_anti₀ hR (by unfold twoBandInversionFactor; linarith [sq_nonneg v])
  rw [twoBand_trace_contact, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_pos hD, div_eq_mul_inv, twoBand_frequency_bound_sq]
  exact mul_le_mul_of_nonneg_left hInv (by positivity)

theorem twoBand_single_spatial_contact_integrable {m σ C : ℝ} (hm : 0 < m) (hσ : 0 < σ)
    (g b : ℝ) (c : Spatial) (w : Spatial → ℂ) (hw : Measurable w) (hC : ∀ k, ‖w k‖ ≤ C) :
    Integrable (fun p : ℝ × Spatial => w p.2 *
      (twoBandResolvent m (twoBandSpatialHop g σ (p.2+c)) (p.1+b) * twoBandMix).trace) := by
  let T := fun p : ℝ × Spatial =>
    (twoBandResolvent m (twoBandSpatialHop g σ (p.2+c)) (p.1+b) * twoBandMix).trace
  have hFreq : Integrable (fun ξ => (twoBandFrequencyBound m (ξ+b))^2) :=
    (measurePreserving_add_right volume b).integrable_comp_of_integrable (twoBand_frequency_integral hm).1
  have hHop : Integrable (fun k => |twoBandSpatialHop g σ (k+c)|) :=
    (measurePreserving_add_right volume c).integrable_comp_of_integrable (twoBand_spatial_hop_integrable g hσ)
  have hM := (hFreq.mul_prod hHop).const_mul (2*C)
  have hT : Measurable T := by
    have hc : Continuous (fun p : ℝ × Spatial => (twoBandSpatialHop g σ (p.2+c), p.1+b)) := by fun_prop
    have hr := (continuous_twoBandResolvent hm).comp hc
    exact ((hr.matrix_mul continuous_const).matrix_trace).measurable
  apply hM.mono' ((hw.comp measurable_snd).mul hT).aestronglyMeasurable
  filter_upwards with p
  rw [norm_mul]
  have hc : 0 ≤ C := (norm_nonneg _).trans (hC p.2)
  have h := mul_le_mul (hC p.2) (twoBand_contact_trace_bound hm
    (twoBandSpatialHop g σ (p.2+c)) (p.1+b)) (norm_nonneg _) hc
  convert h using 1
  ring

private theorem twoBand_spatial_word_norm {C : ℝ} (hC : 0 ≤ C)
    (A : ℕ → TwoBandMatrix) {F₀ F₁ : ℝ} (h₀ : ‖A 0‖ ≤ F₀) (h₁ : ‖A 1‖ ≤ F₁)
    (hA : ∀ j, ‖A j‖ ≤ C) (r : ℕ) :
    ‖twoBandOrderedProduct A (r+2)‖ ≤ C^r*(F₀*F₁) := by
  have hNonneg : 0 ≤ F₀*F₁ := mul_nonneg ((norm_nonneg _).trans h₀) ((norm_nonneg _).trans h₁)
  induction r with
  | zero =>
    simp only [twoBandOrderedProduct, one_mul, pow_zero]
    exact (norm_mul_le _ _).trans (mul_le_mul h₀ h₁ (norm_nonneg _) ((norm_nonneg _).trans h₀))
  | succ r ih =>
    change ‖twoBandOrderedProduct A (r+2) * A (r+2)‖ ≤ _
    calc
      _ ≤ (C^r*(F₀*F₁))*C := (norm_mul_le _ _).trans (mul_le_mul ih (hA (r+2))
        (norm_nonneg _) (mul_nonneg (pow_nonneg hC r) hNonneg))
      _ = _ := by rw [pow_succ]; ring

set_option maxHeartbeats 800000 in
/-- Two distinct massive resolvents suffice when a spatial mark supplies
an integrable multiplier. Each remaining slot insertion is a contraction.
The majorant is uniform in every affine shift of the propagating word. -/
theorem twoBand_spatial_word_integrable {m : ℝ} (hm : 0 < m) (g σ : ℝ)
    (b : ℕ → ℝ) (c : ℕ → Spatial) (M : ℕ → TwoBandMatrix) (hM : ∀ j, ‖M j‖ ≤ 1)
    (w : Spatial → ℂ) (hw : Integrable w) (r : ℕ) :
    Integrable (fun p : ℝ × Spatial => w p.2 *
      (twoBandOrderedProduct (fun j => twoBandResolvent m (twoBandSpatialHop g σ (p.2+c j))
        (p.1+b j) * M j) (r+2)).trace) := by
  let F := twoBandFrequencyBound m
  let A := fun j (p : ℝ × Spatial) =>
    twoBandResolvent m (twoBandSpatialHop g σ (p.2+c j)) (p.1+b j) * M j
  let Z := fun p => twoBandOrderedProduct (fun j => A j p) (r+2)
  have hA (j : ℕ) (p : ℝ × Spatial) : ‖A j p‖ ≤ F (p.1+b j) := by
    obtain ⟨h₁,_⟩ := twoBand_resolvent_bound hm (twoBandSpatialHop g σ (p.2+c j)) (p.1+b j)
    exact (norm_mul_le _ _).trans ((mul_le_mul h₁ (hM j) (norm_nonneg _) (by
      unfold twoBandFrequencyBound; positivity)).trans_eq (mul_one _))
  have hUniform (p : ℝ × Spatial) : ∀ j, ‖A j p‖ ≤ m⁻¹ := fun j =>
    (hA j p).trans (twoBand_resolvent_bound hm (twoBandSpatialHop g σ (p.2+c j)) (p.1+b j)).2
  have hCont (j : ℕ) : Continuous (A j) := by
    have hc : Continuous (fun p : ℝ × Spatial => (twoBandSpatialHop g σ (p.2+c j), p.1+b j)) := by fun_prop
    have hr := (continuous_twoBandResolvent hm).comp hc
    exact hr.matrix_mul continuous_const
  have hTrace : Continuous (fun p => (Z p).trace) :=
    (continuous_twoBandOrderedProduct _ hCont (r+2)).matrix_trace
  have hW := Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := (volume : Measure Spatial))
  have hMeas := (hw.aestronglyMeasurable.comp_quasiMeasurePreserving hW).mul hTrace.aestronglyMeasurable
  have hFreq := (twoBand_frequency_product hm (b 0) (b 1)).1
  have hDom := (hFreq.mul_prod hw.norm).const_mul (2*(m⁻¹)^r)
  apply hDom.mono' hMeas
  filter_upwards with p
  have hZ := (twoBand_trace_norm (Z p)).trans (mul_le_mul_of_nonneg_left
    (twoBand_spatial_word_norm (inv_nonneg.mpr hm.le) (fun j => A j p) (hA 0 p) (hA 1 p)
      (hUniform p) r) (by norm_num))
  change ‖w p.2*(Z p).trace‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ ‖w p.2‖ * (2*((m⁻¹)^r*(F (p.1+b 0)*F (p.1+b 1)))) :=
      mul_le_mul_of_nonneg_left hZ (norm_nonneg _)
    _ = _ := by ring

end UV.SectorPlane
