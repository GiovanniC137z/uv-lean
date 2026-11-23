import UV.ContinueTemporalFlux
import Mathlib.MeasureTheory.Integral.Prod

/-! The energy domain on the normal half-line in its one-dimensional
Sobolev representative: a locally absolutely continuous primitive with
both the function and its weak derivative in L². -/

noncomputable section

namespace UV.TemporalRay

open MeasureTheory Set Filter
open scoped Topology

structure NormalEnergyProfile where
  value : ℝ → ℝ
  slope : ℝ → ℝ
  value_L2 : MemLp value 2 normalRayMeasure
  slope_L2 : MemLp slope 2 normalRayMeasure
  primitive : ∀ r ≥ 0, value r = value 0 + ∫ t in (0:ℝ)..r, slope t

theorem normal_ray_interval_integrable {F : Type*} [NormedAddCommGroup F] {g : ℝ → F} (hg : MemLp g 2 normalRayMeasure)
    {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) : IntervalIntegrable g volume s r := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hsr).mpr
  exact (hg.mono_measure (Measure.restrict_mono_set volume
    (show Ioc s r ⊆ Ioi (0:ℝ) from fun _ ht => hs.trans_lt ht.1))).integrable (by norm_num)

def NormalProfile.toEnergyProfile (u : NormalProfile) : NormalEnergyProfile where
  value := u.amplitude
  slope := u.gradient
  value_L2 := u.amplitude_L2
  slope_L2 := u.gradient_L2
  primitive r hr := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht =>
      u.has_gradient t (by rw [uIcc_of_le hr] at ht; exact ht.1))
      (normal_ray_interval_integrable u.gradient_L2 le_rfl hr)]
    ring

/-- Integration over the time-ordered triangle for two L¹ factors on a
finite normal interval, including weak derivatives of finite-energy tests. -/
private theorem ray_primitive_swap {R : ℝ} (hR : 0 ≤ R) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 R) (hg : IntervalIntegrable g volume 0 R) :
    (∫ r in (0:ℝ)..R, f r*(∫ t in (0:ℝ)..r, g t)) =
      ∫ t in (0:ℝ)..R, (∫ r in t..R, f r)*g t := by
  let μ := (volume : Measure ℝ).restrict (Ioc 0 R)
  letI : SFinite μ := by dsimp [μ]; infer_instance
  let K (r t : ℝ) := if t < r then f r*g t else 0
  have hL : MeasurableSet {p : ℝ × ℝ | p.2 < p.1} := measurableSet_lt measurable_snd measurable_fst
  have hK : Integrable (Function.uncurry K) (μ.prod μ) := by
    convert (hf.1.mul_prod hg.1).indicator hL using 1
  have hfirst (r : ℝ) (hr : r ∈ Ioc (0:ℝ) R) :
      (∫ t, K r t ∂μ) = f r * ∫ t in (0:ℝ)..r, g t := by
    have h : K r = fun t => f r*(Iio r).indicator g t := by
      funext t
      by_cases h : t < r <;> simp [K,Set.indicator,h]
    rw [h,integral_const_mul,integral_indicator measurableSet_Iio]
    unfold μ
    rw [Measure.restrict_restrict measurableSet_Iio,intervalIntegral.integral_of_le hr.1.le]
    congr 1
    apply setIntegral_congr_set
    apply (Iio_ae_eq_Iic (μ := volume) (a := r)).inter (EventuallyEq.rfl (f := Ioc (0:ℝ) R)) |>.trans
    rw [show Iic r ∩ Ioc 0 R = Ioc 0 r by
      ext x
      simp only [mem_inter_iff,mem_Iic,mem_Ioc]
      constructor
      · exact fun h => ⟨h.2.1,h.1⟩
      · exact fun h => ⟨h.2,h.1,h.2.trans hr.2⟩]
  have hsecond (t : ℝ) (ht : t ∈ Ioc (0:ℝ) R) :
      (∫ r, K r t ∂μ) = (∫ r in t..R, f r)*g t := by
    have h : (fun r => K r t) = fun r => (Ioi t).indicator f r*g t := by
      funext r
      by_cases h : t < r <;> simp [K,Set.indicator,h]
    rw [h,integral_mul_const,integral_indicator measurableSet_Ioi]
    unfold μ
    rw [Measure.restrict_restrict measurableSet_Ioi,intervalIntegral.integral_of_le ht.2,
      show Ioi t ∩ Ioc 0 R = Ioc t R by
        ext x
        simp only [mem_inter_iff,mem_Ioi,mem_Ioc]
        exact ⟨fun h => ⟨h.1,h.2.2⟩, fun h => ⟨h.1,ht.1.trans h.1,h.2⟩⟩]
  rw [intervalIntegral.integral_of_le hR, intervalIntegral.integral_of_le hR]
  change (∫ r, _ ∂μ) = ∫ t, _ ∂μ
  have ha : ∀ᵐ t ∂μ, t ∈ Ioc (0:ℝ) R := ae_restrict_mem measurableSet_Ioc
  exact (integral_congr_ae (ha.mono fun r hr => (hfirst r hr).symm)).trans
    ((integral_integral_swap hK).trans (integral_congr_ae (ha.mono hsecond)))

private theorem weak_ray_product_interval (v : NormalEnergyProfile) {F f : ℝ → ℝ}
    (hd : ∀ r ≥ 0, HasDerivAt F (f r) r) (hc : ContinuousOn f (Ici 0))
    {R : ℝ} (hR : 0 ≤ R) :
    (∫ r in (0:ℝ)..R, f r*v.value r + F r*v.slope r) =
      F R*v.value R - F 0*v.value 0 := by
  have hfi (s : ℝ) (hs : 0 ≤ s) (hsR : s ≤ R) : IntervalIntegrable f volume s R := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hsR]
    exact hc.mono fun _ hx => hs.trans hx.1
  have hdif (s : ℝ) (hs : 0 ≤ s) (hsR : s ≤ R) : (∫ r in s..R, f r) = F R-F s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r hr => hd r (by rw [uIcc_of_le hsR] at hr; exact hs.trans hr.1)) (hfi s hs hsR)
  have hg := normal_ray_interval_integrable v.slope_L2 le_rfl hR
  have hF : ContinuousOn F (uIcc 0 R) := by
    rw [uIcc_of_le hR]
    exact fun r hr => (hd r hr.1).continuousAt.continuousWithinAt
  have hfg : IntervalIntegrable (fun r => F r*v.slope r) volume 0 R :=
    hg.continuousOn_mul hF
  have hI : IntervalIntegrable (fun r => ∫ t in (0:ℝ)..r, v.slope t) volume 0 R :=
    (intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc).intervalIntegrable
  have hfc := hc.mono (show uIcc 0 R ⊆ Ici 0 by rw [uIcc_of_le hR]; exact fun _ hx => hx.1)
  have hprod := hI.continuousOn_mul hfc
  calc
    _ = ∫ r in (0:ℝ)..R, (f r*v.value 0 + f r*(∫ t in (0:ℝ)..r, v.slope t)) + F r*v.slope r := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le hR] at hr
      dsimp only
      rw [v.primitive r hr.1, mul_add]
    _ = (∫ r in (0:ℝ)..R, f r)*v.value 0 + (∫ r in (0:ℝ)..R, f r*(∫ t in (0:ℝ)..r, v.slope t)) +
          ∫ r in (0:ℝ)..R, F r*v.slope r := by
      rw [intervalIntegral.integral_add (((hfi 0 le_rfl hR).mul_const _).add hprod) hfg,
        intervalIntegral.integral_add ((hfi 0 le_rfl hR).mul_const _) hprod,
        intervalIntegral.integral_mul_const]
    _ = (F R-F 0)*v.value 0 + (∫ t in (0:ℝ)..R, (F R-F t)*v.slope t) + ∫ r in (0:ℝ)..R, F r*v.slope r := by
      rw [hdif 0 le_rfl hR, ray_primitive_swap hR (hfi 0 le_rfl hR) hg]
      congr 2
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hR] at ht
      dsimp only
      rw [hdif t ht.1 ht.2]
    _ = _ := by
      simp_rw [sub_mul]
      rw [intervalIntegral.integral_sub (hg.const_mul _) hfg,intervalIntegral.integral_const_mul,
        v.primitive R hR]
      ring

/-- Green's identity tested on the full finite-energy domain. There is no
endpoint contribution at infinity. -/
theorem normal_weak_flux_identity (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (u : NormalTransfer D.a (D.potential y)) (v : NormalEnergyProfile) :
    (∫ r in Ioi (0:ℝ), D.potential y r*u.amplitude r*v.value r +
      (D.a r*u.gradient r)*v.slope r) = boundaryFlux D.a u * v.value 0 := by
  let F := fun r => D.a r*u.gradient r
  let f := fun r => D.potential y r*u.amplitude r
  let hval := fun r => f r*v.value r + F r*v.slope r
  have hFi : IntegrableOn (fun r => F r*v.value r) (Ioi 0) :=
    ray_product_integrable u.gradient_L2 v.value_L2 D.continuous_a.measurable (fun _ hr => D.abs_a_bound hr.le)
  have hhi : IntegrableOn hval (Ioi 0) := (ray_product_integrable u.amplitude_L2 v.value_L2
    (D.continuous_potential y).measurable fun _ hr => D.potential_upper hy hr.le).add
    (ray_product_integrable u.gradient_L2 v.slope_L2 D.continuous_a.measurable fun _ hr => D.abs_a_bound hr.le)
  have hfc : ContinuousOn f (Ici 0) := (D.continuous_potential y).continuousOn.mul
    (fun r hr => (u.has_gradient r hr).continuousAt.continuousWithinAt)
  have hlim : Tendsto (fun r => F r*v.value r) atTop (𝓝 (F 0*v.value 0 + ∫ r in Ioi 0, hval r)) := by
    apply ((intervalIntegral_tendsto_integral_Ioi 0 hhi tendsto_id).const_add (F 0*v.value 0)).congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
    change F 0*v.value 0 + (∫ r in (0:ℝ)..R, f r*v.value r + F r*v.slope r) = F R*v.value R
    rw [weak_ray_product_interval v u.flux_derivative hfc hR]
    ring
  have hz := ray_limit_zero_of_integrable hFi hlim
  change (∫ r in Ioi (0:ℝ), hval r) = -(F 0)*v.value 0
  linarith only [hz]

end UV.TemporalRay
