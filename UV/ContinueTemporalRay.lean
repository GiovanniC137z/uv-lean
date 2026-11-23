import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Finite-energy profiles for the specified transverse normal equation
on the proper normal ray. -/

noncomputable section

namespace UV.TemporalRay

open MeasureTheory Filter Set
open scoped Topology ENNReal

def normalRayMeasure : Measure ℝ := volume.restrict (Ioi 0)

structure NormalProfile where
  amplitude : ℝ → ℝ
  gradient : ℝ → ℝ
  has_gradient : ∀ r ≥ 0, HasDerivAt amplitude (gradient r) r
  amplitude_L2 : MemLp amplitude 2 normalRayMeasure
  gradient_L2 : MemLp gradient 2 normalRayMeasure

def modePotential (b c : ℝ → ℝ) (k y r : ℝ) : ℝ := b r * k^2 + c r * y

structure NormalTransfer (a p : ℝ → ℝ) extends NormalProfile where
  boundary_one : amplitude 0 = 1
  flux_derivative : ∀ r ≥ 0, HasDerivAt (fun t => a t * gradient t) (p r * amplitude r) r

def boundaryFlux (a : ℝ → ℝ) {p : ℝ → ℝ} (u : NormalTransfer a p) : ℝ :=
  -(a 0 * u.gradient 0)

def profileDifference (u v : NormalProfile) : NormalProfile where
  amplitude r := v.amplitude r - u.amplitude r
  gradient r := v.gradient r - u.gradient r
  has_gradient r hr := (v.has_gradient r hr).sub (u.has_gradient r hr)
  amplitude_L2 := v.amplitude_L2.sub u.amplitude_L2
  gradient_L2 := v.gradient_L2.sub u.gradient_L2

/-- Multiplying an L² product by a bounded, measurable coefficient
preserves integrability on the proper normal ray. -/
theorem ray_product_integrable {f g c : ℝ → ℝ} (hf : MemLp f 2 normalRayMeasure)
    (hg : MemLp g 2 normalRayMeasure) (hc : Measurable c) {C : ℝ}
    (hb : ∀ r > 0, |c r| ≤ C) :
    Integrable (fun r => c r * f r * g r) normalRayMeasure := by
  have hi := (hf.norm.integrable_mul hg.norm).const_mul C
  refine hi.mono' ((hc.aestronglyMeasurable.mul hf.aestronglyMeasurable).mul hg.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi (0:ℝ)) measurableSet_Ioi] with r hr
  change ‖c r * f r * g r‖ ≤ C * (‖f r‖*‖g r‖)
  rw [norm_mul,norm_mul,mul_assoc,Real.norm_eq_abs (c r)]
  exact mul_le_mul_of_nonneg_right (hb r hr) (by positivity)

private theorem ray_limit_zero_of_integrable {F : ℝ → ℝ} {a L : ℝ}
    (hF : IntegrableOn F (Ioi a)) (h : Tendsto F atTop (𝓝 L)) : L = 0 := by
  by_contra hL
  have hpos : 0 < ‖L‖/2 := by positivity
  have he : ∀ᶠ r in atTop, ‖L‖/2 < ‖F r‖ :=
    h.norm.eventually_const_lt (by linarith)
  obtain ⟨R,hR⟩ := eventually_atTop.mp he
  let B := max R a
  have hi : IntegrableOn F (Ioi B) := hF.mono_set (Ioi_subset_Ioi (le_max_right R a))
  have hconst : Integrable (fun _ : ℝ => ‖L‖/2) (volume.restrict (Ioi B)) := by
    refine hi.norm.mono' aestronglyMeasurable_const ?_
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi B) measurableSet_Ioi] with r hr
    rw [Real.norm_of_nonneg hpos.le]
    exact (hR r ((le_max_left R a).trans hr.le)).le
  have hfinite := (integrable_const_iff_isFiniteMeasure hpos.ne').mp hconst
  have htop : (volume.restrict (Ioi B)) univ = ∞ := by
    simp [Measure.restrict_apply,Real.volume_Ioi]
  exact (lt_irrefl ∞) (htop ▸ hfinite.measure_univ_lt_top)

theorem ray_derivative_tendsto_zero {F f : ℝ → ℝ} {a : ℝ}
    (hd : ∀ r ≥ a, HasDerivAt F (f r) r)
    (hF : IntegrableOn F (Ioi a)) (hf : IntegrableOn f (Ioi a)) :
    Tendsto F atTop (𝓝 0) := by
  have hlim := (intervalIntegral_tendsto_integral_Ioi a hf tendsto_id).const_add (F a)
  have hlimit : Tendsto F atTop (𝓝 (F a + ∫ r in Ioi a, f r)) := by
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop a] with b hb
    have hi : IntervalIntegrable f volume a b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mpr (hf.mono_set Ioc_subset_Ioi_self)
    have hdb (r : ℝ) (hr : r ∈ uIcc a b) : HasDerivAt F (f r) r := by
      rw [uIcc_of_le hb] at hr
      exact hd r hr.1
    change F a + (∫ r in a..b, f r) = F b
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hdb hi]
    ring
  simpa only [ray_limit_zero_of_integrable hF hlimit] using hlimit

theorem integral_ray_derivative {F f : ℝ → ℝ} {a : ℝ}
    (hd : ∀ r ≥ a, HasDerivAt F (f r) r)
    (hF : IntegrableOn F (Ioi a)) (hf : IntegrableOn f (Ioi a)) :
    (∫ r in Ioi a, f r) = -F a := by
  simpa only [zero_sub] using integral_Ioi_of_hasDerivAt_of_tendsto' hd hf
    (ray_derivative_tendsto_zero hd hF hf)

def normalBilinear (a p : ℝ → ℝ) (u v : NormalProfile) : ℝ :=
  ∫ r in Ioi (0:ℝ), a r * u.gradient r * v.gradient r + p r * u.amplitude r * v.amplitude r

/-- Testing the actual normal equation against any finite-energy profile
gives its only boundary term, with the outward sign fixed at r = 0. -/
theorem normal_bilinear_flux {a p : ℝ → ℝ} (u : NormalTransfer a p) (v : NormalProfile)
    (ha : Measurable a) (hp : Measurable p)
    {A P : ℝ}
    (hba : ∀ r > 0, |a r| ≤ A) (hbp : ∀ r > 0, |p r| ≤ P) :
    normalBilinear a p u.toNormalProfile v = boundaryFlux a u * v.amplitude 0 := by
  have hF := ray_product_integrable u.gradient_L2 v.amplitude_L2 ha hba
  have hf := (ray_product_integrable u.gradient_L2 v.gradient_L2 ha hba).add
    (ray_product_integrable u.amplitude_L2 v.amplitude_L2 hp hbp)
  have hd (r : ℝ) (hr : 0 ≤ r) : HasDerivAt (fun r => a r * u.gradient r * v.amplitude r)
      (a r * u.gradient r * v.gradient r + p r * u.amplitude r * v.amplitude r) r := by
    simpa only [add_comm] using (u.flux_derivative r hr).mul (v.has_gradient r hr)
  have h := integral_ray_derivative (a := 0) hd hF hf
  change _ = -(a 0 * u.gradient 0 * v.amplitude 0) at h
  simpa only [normalBilinear,boundaryFlux,neg_mul] using h

theorem normal_energy_flux {a p : ℝ → ℝ} (u : NormalTransfer a p)
    (ha : Measurable a) (hp : Measurable p)
    {A P : ℝ}
    (hba : ∀ r > 0, |a r| ≤ A) (hbp : ∀ r > 0, |p r| ≤ P) :
    (∫ r in Ioi (0:ℝ), a r * u.gradient r ^ 2 + p r * u.amplitude r ^ 2) = boundaryFlux a u := by
  have h := normal_bilinear_flux u u.toNormalProfile ha hp hba hbp
  simpa only [normalBilinear,pow_two,mul_assoc,u.boundary_one,mul_one] using h

end UV.TemporalRay
