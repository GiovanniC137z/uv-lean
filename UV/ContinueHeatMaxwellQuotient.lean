import UV.ContinueHeatMaxwellZero
import UV.ContinueHeatMaxwellNativeCoefficient
import UV.ContinueHeatMaxwellNativeWidth
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The actual divided continuum response as the external momentum tends to
zero within the fixed plane, including both signs. -/

noncomputable section
open MeasureTheory Set Filter UV.SectorPlane
open scoped Topology
namespace UV.HeatMaxwell

local instance quotientSectorMeasurable : MeasurableSpace EuclideanPlaneMomentum := borel _
local instance quotientSectorBorel : BorelSpace EuclideanPlaneMomentum := ⟨rfl⟩

theorem heat_loop_divided_limit (a : HeatLoopCurve ℝ) (h₀ : (∫ k, a.value 0 k)=0)
    (h₁ : (∫ k, a.first 0 k)=0) :
    Tendsto (fun t : ℝ => (∫ k, a.value t k)/t^2) (𝓝[≠] 0) (𝓝 ((∫ k, a.second 0 k)/2)) := by
  obtain ⟨hv,hf⟩ := heat_loop_integral_local_derivatives a
  have hlim := hf.tendsto_slope_zero.div_const 2
  simp only [zero_add,h₁,sub_zero,smul_eq_mul] at hlim
  have hder : Tendsto (fun t : ℝ => (∫ k, a.first t k)/(2*t)) (𝓝[≠] 0) (𝓝 ((∫ k, a.second 0 k)/2)) := by
    convert hlim using 1
    ext t
    ring
  have hS : ∀ᶠ t : ℝ in 𝓝[≠] 0, |t|<1 :=
    (continuous_abs.continuousAt (x := (0:ℝ))).eventually_lt continuousAt_const (by norm_num) |>.filter_mono nhdsWithin_le_nhds
  apply HasDerivAt.lhopital_zero_nhdsNE (hS.mono (fun t ht => hv t ht))
    (Eventually.of_forall (fun t => by simpa using hasDerivAt_pow 2 t)) _ _ _ hder
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_ne_zero (by norm_num) ht
  · simpa only [h₀] using (hv 0 (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · simpa using (show Tendsto (fun t : ℝ => t^2) (𝓝[≠] 0) (𝓝 ((0:ℝ)^2)) from
        (continuous_pow 2).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

/-- The coefficient is the two-sided limit of the literal integrated response
divided by squared external momentum in the unit-width chart. -/
theorem heat_native_divided_limit {m a : ℝ} (hm : 0<m) (ha : 0<a) :
    Tendsto (fun t : ℝ => (4/(2*Real.pi)^4)*(∫ k, heatNativeResponse (m*a) k t)/t^2)
      (𝓝[≠] 0) (𝓝 (heatTransverseSoftCoefficient m a)) := by
  let A := heatNativeCurve (mul_pos hm ha)
  have hval : A.value = fun t k => heatNativeResponse (m*a) k t :=
    funext fun t => funext fun k => heat_native_curve_value _ t k
  have h₀ : (∫ k, A.value 0 k) = 0 := by rw [hval]; exact heat_native_zero_integral (mul_pos hm ha)
  have hfirst (k : EuclideanPlaneMomentum) : A.first 0 k = 0 := by
    have hd := (A.deriv_value 0 k).deriv
    rw [hval] at hd
    exact hd.symm.trans (heat_native_pointwise_first (mul_pos hm ha) k)
  have h₁ : (∫ k, A.first 0 k) = 0 := by simp [hfirst]
  have hc := heat_native_soft_coefficient hm ha
  have hint : (fun t => ∫ k, A.value t k) = (fun t => ∫ k, heatNativeResponse (m*a) k t) := by rw [hval]
  rw [←hint,heat_loop_integral_second] at hc
  have h := (heat_loop_divided_limit A h₀ h₁).const_mul (4/(2*Real.pi)^4)
  rw [hc] at h
  simpa only [hval,mul_div_assoc] using h

/-- For every physical positive mass and width the normalized native
bubble/contact response has a strictly positive two-sided soft limit.
Continuous external readouts with value one at zero retain it. -/
theorem heat_width_divided_limit {m a : ℝ} (hm : 0<m) (ha : 0<a) {readout : ℝ → ℝ}
    (hh : Tendsto readout (𝓝[≠] 0) (𝓝 1)) :
    (Tendsto (fun t : ℝ => (4/(2*Real.pi)^4)*(∫ k, heatWidthNativeResponse m a k t)*readout t/t^2)
       (𝓝[≠] 0) (𝓝 (heatTransverseSoftCoefficient m a))) ∧ 0<heatTransverseSoftCoefficient m a := by
  have hne : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ≠ 0 := self_mem_nhdsWithin
  have hs : Tendsto (fun t : ℝ => a*t) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,hne.mono fun _ ht => mul_ne_zero ha.ne' ht⟩
    simpa using ((tendsto_id (x := 𝓝 (0:ℝ))).const_mul a).mono_left nhdsWithin_le_nhds
  refine ⟨?_,heatTransverseSoftCoefficient_pos hm ha⟩
  have h := ((heat_native_divided_limit hm ha).comp hs).mul hh
  rw [mul_one] at h
  apply h.congr'
  filter_upwards [hne] with t ht
  change (4/(2*Real.pi)^4)*(∫ k, heatNativeResponse (m*a) k (a*t))/(a*t)^2*readout t = _
  rw [heat_width_native_integral hm ha t]
  field_simp

end UV.HeatMaxwell
