import UV.ContinueSpectrumFourier
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Absolutely convergent oscillatory pair integrals used in the layer
Stieltjes transform. The sine formula follows by dominated differentiation. -/

noncomputable section
open MeasureTheory Real Filter Set
open scoped Topology

namespace UV.RevisionSpectrum

def continuePairCos (c w r : ℝ) : ℝ :=
  ∫ k : ℝ in Ioi 0, Real.cos (r*k)*((k^2+c^2)⁻¹*(k^2+w^2)⁻¹)

theorem continuePairCos_integrable {c w : ℝ} (hc : 0<c) (hw : 0<w) (r : ℝ) :
    IntegrableOn (fun k : ℝ => Real.cos (r*k)*((k^2+c^2)⁻¹*(k^2+w^2)⁻¹)) (Ioi 0) := by
  apply (resumeCauchyPair_integrable hc hw).mono'
  · exact (by fun_prop : Measurable (fun k : ℝ => Real.cos (r*k)*((k^2+c^2)⁻¹*(k^2+w^2)⁻¹))).aestronglyMeasurable
  · filter_upwards with k
    rw [norm_mul,Real.norm_eq_abs,Real.norm_of_nonneg (by positivity : 0≤(k^2+c^2)⁻¹*(k^2+w^2)⁻¹)]
    exact mul_le_of_le_one_left (by positivity) (Real.abs_cos_le_one _)

theorem continuePairK_integrable {c w : ℝ} (hc : 0<c) (hw : 0<w) :
    IntegrableOn (fun k : ℝ => k*((k^2+c^2)⁻¹*(k^2+w^2)⁻¹)) (Ioi 0) := by
  apply ((resumeCauchy_integrable w hw).const_mul (1/(2*c))).mono'
  · exact (by fun_prop : Measurable (fun k : ℝ => k*((k^2+c^2)⁻¹*(k^2+w^2)⁻¹))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with k hk
    have hk₀ : 0<k := hk
    rw [Real.norm_of_nonneg (by positivity)]
    have hb : k*(k^2+c^2)⁻¹≤1/(2*c) := by
      rw [← div_eq_mul_inv,div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (k-c)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hb (by positivity : 0≤(k^2+w^2)⁻¹)

theorem continuePairSin_integrable {c w : ℝ} (hc : 0<c) (hw : 0<w) (r : ℝ) :
    IntegrableOn (fun k : ℝ => k*Real.sin (r*k)*((k^2+c^2)⁻¹*(k^2+w^2)⁻¹)) (Ioi 0) := by
  apply (continuePairK_integrable hc hw).mono'
  · exact (by fun_prop : Measurable (fun k : ℝ => k*Real.sin (r*k)*((k^2+c^2)⁻¹*(k^2+w^2)⁻¹))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with k hk
    have hk₀ : 0<k := hk
    simp only [norm_mul,Real.norm_eq_abs,abs_of_pos hk₀,
      abs_of_nonneg (by positivity : 0≤(k^2+c^2)⁻¹),
      abs_of_nonneg (by positivity : 0≤(k^2+w^2)⁻¹)]
    calc
      _ ≤ k*1*((k^2+c^2)⁻¹*(k^2+w^2)⁻¹) := by
        gcongr
        exact Real.abs_sin_le_one _
      _ = _ := by ring

theorem continuePairCos_formula {c w : ℝ} (hc : 0<c) (hw : 0<w) (hcw : c≠w) (r : ℝ) :
    continuePairCos c w r = (Real.pi/2)*
      (Real.exp (-c*|r|)/c-Real.exp (-w*|r|)/w)/(w^2-c^2) := by
  have hd : w^2-c^2≠0 := by
    intro h
    exact hcw ((sq_eq_sq₀ hw.le hc.le).mp (sub_eq_zero.mp h)).symm
  have he (k : ℝ) : Real.cos (r*k)*((k^2+c^2)⁻¹*(k^2+w^2)⁻¹) =
      (w^2-c^2)⁻¹*(Real.cos (r*k)*(k^2+c^2)⁻¹ - Real.cos (r*k)*(k^2+w^2)⁻¹) := by
    have h₁ : k^2+c^2≠0 := by positivity
    have h₂ : k^2+w^2≠0 := by positivity
    field_simp
    ring
  unfold continuePairCos
  simp_rw [he]
  have hic : IntegrableOn (fun k : ℝ => Real.cos (r*k)*(k^2+c^2)⁻¹) (Ioi 0) := by
    simpa only [mul_comm] using (continueCauchyCos_integrable hc r).integrableOn (s:=Ioi 0)
  have hiw : IntegrableOn (fun k : ℝ => Real.cos (r*k)*(k^2+w^2)⁻¹) (Ioi 0) := by
    simpa only [mul_comm] using (continueCauchyCos_integrable hw r).integrableOn (s:=Ioi 0)
  have hvc : (∫ k : ℝ in Ioi 0,Real.cos (r*k)*(k^2+c^2)⁻¹)=Real.pi/(2*c)*Real.exp (-c*|r|) := by
    simpa only [mul_comm] using continueCauchyCos_integral hc r
  have hvw : (∫ k : ℝ in Ioi 0,Real.cos (r*k)*(k^2+w^2)⁻¹)=Real.pi/(2*w)*Real.exp (-w*|r|) := by
    simpa only [mul_comm] using continueCauchyCos_integral hw r
  rw [integral_const_mul,integral_sub hic hiw,hvc,hvw]
  field_simp

theorem continuePairCos_hasDerivAt {c w : ℝ} (hc : 0<c) (hw : 0<w) (r : ℝ) :
    HasDerivAt (continuePairCos c w)
      (-(∫ k : ℝ in Ioi 0,k*Real.sin (r*k)*((k^2+c^2)⁻¹*(k^2+w^2)⁻¹))) r := by
  have hQ : Continuous (fun k : ℝ => (k^2+c^2)⁻¹*(k^2+w^2)⁻¹) := by
    apply Continuous.mul
    · exact ((continuous_id.pow 2).add continuous_const).inv₀ (fun k => by positivity)
    · exact ((continuous_id.pow 2).add continuous_const).inv₀ (fun k => by positivity)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=fun t k : ℝ => Real.cos (t*k)*((k^2+c^2)⁻¹*(k^2+w^2)⁻¹))
    (F':=fun t k : ℝ => -(k*Real.sin (t*k)*((k^2+c^2)⁻¹*(k^2+w^2)⁻¹)))
    (x₀:=r) (ε:=1) (μ:=volume.restrict (Ioi 0))
    (bound:=fun k : ℝ => k*((k^2+c^2)⁻¹*(k^2+w^2)⁻¹))
    (by norm_num)
    (Eventually.of_forall fun t =>
      ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul hQ).aestronglyMeasurable)
    (continuePairCos_integrable hc hw r)
    (((continuous_id.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))).mul hQ).neg).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with k hk t _
      have hk₀ : 0<k := hk
      simp only [norm_neg,norm_mul,Real.norm_eq_abs,abs_of_pos hk₀,
        abs_of_nonneg (by positivity : 0≤(k^2+c^2)⁻¹),
      abs_of_nonneg (by positivity : 0≤(k^2+w^2)⁻¹)]
      calc
        _ ≤ k*1*((k^2+c^2)⁻¹*(k^2+w^2)⁻¹) := by gcongr; exact Real.abs_sin_le_one _
        _ = _ := by ring)
    (continuePairK_integrable hc hw)
    (Eventually.of_forall fun k t _ => by
      convert (((hasDerivAt_id t).mul_const k).cos).mul_const ((k^2+c^2)⁻¹*(k^2+w^2)⁻¹) using 1
      simp only [id_eq]
      ring)
  simpa only [continuePairCos,integral_neg] using hd.2

theorem continuePairSin_formula {c w r : ℝ} (hc : 0<c) (hw : 0<w) (hcw : c≠w) (hr : 0<r) :
    (∫ k : ℝ in Ioi 0,k*Real.sin (r*k)*((k^2+c^2)⁻¹*(k^2+w^2)⁻¹)) =
      (Real.pi/2)*(Real.exp (-c*r)-Real.exp (-w*r))/(w^2-c^2) := by
  have he : continuePairCos c w =ᶠ[𝓝 r] fun t : ℝ =>
      (Real.pi/2)*(Real.exp (-c*t)/c-Real.exp (-w*t)/w)/(w^2-c^2) := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    change 0<t at ht
    simpa only [abs_of_pos ht] using continuePairCos_formula hc hw hcw t
  have hdC := (((hasDerivAt_id r).const_mul (-c)).exp.div_const c)
  have hdW := (((hasDerivAt_id r).const_mul (-w)).exp.div_const w)
  have hd := ((hdC.sub hdW).const_mul (Real.pi/2)).div_const (w^2-c^2)
  have hd' := hd.congr_of_eventuallyEq he
  have h := (continuePairCos_hasDerivAt hc hw r).unique hd'
  simp only [id_eq] at h
  have hdif : w^2-c^2≠0 := by
    intro hz
    exact hcw ((sq_eq_sq₀ hw.le hc.le).mp (sub_eq_zero.mp hz)).symm
  field_simp [hdif] at h ⊢
  simp_rw [mul_comm _ r] at h
  nlinarith [h]

end UV.RevisionSpectrum
