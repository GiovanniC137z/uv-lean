import UV.ContinueTemporalRay
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Green's identity and stability of the temporal normal flux under
a change in the squared carrier frequency. -/

noncomputable section

namespace UV.TemporalRay

open MeasureTheory Filter Set Real
open scoped Topology ENNReal

structure NormalChannel where
  k : ℝ
  a : ℝ → ℝ
  spatial : ℝ → ℝ
  temporal : ℝ → ℝ
  aMin : ℝ
  aMax : ℝ
  spMin : ℝ
  spMax : ℝ
  parMax : ℝ
  k_pos : 0 < k
  aMin_pos : 0 < aMin
  spMin_pos : 0 < spMin
  continuous_a : Continuous a
  continuous_spatial : Continuous spatial
  continuous_temporal : Continuous temporal
  a_bound : ∀ r ≥ 0, aMin ≤ a r ∧ a r ≤ aMax
  spatial_bound : ∀ r ≥ 0, spMin ≤ spatial r ∧ spatial r ≤ spMax
  temporal_bound : ∀ r ≥ 0, 0 ≤ temporal r ∧ temporal r ≤ parMax

def NormalChannel.potential (D : NormalChannel) (y : ℝ) : ℝ → ℝ :=
  modePotential D.spatial D.temporal D.k y

theorem NormalChannel.continuous_potential (D : NormalChannel) (y : ℝ) :
    Continuous (D.potential y) :=
  (D.continuous_spatial.mul continuous_const).add (D.continuous_temporal.mul continuous_const)

theorem NormalChannel.potential_lower (D : NormalChannel) {y r : ℝ} (hy : 0 ≤ y) (hr : 0 ≤ r) :
    D.spMin*D.k^2 ≤ D.potential y r := by
  unfold NormalChannel.potential modePotential
  exact le_add_of_le_of_nonneg
    (mul_le_mul_of_nonneg_right (D.spatial_bound r hr).1 (sq_nonneg D.k))
    (mul_nonneg (D.temporal_bound r hr).1 hy)

theorem NormalChannel.potential_upper (D : NormalChannel) {y r : ℝ} (hy : 0 ≤ y) (hr : 0 ≤ r) :
    |D.potential y r| ≤ D.spMax*D.k^2+D.parMax*y := by
  have h : 0 ≤ D.potential y r := (mul_nonneg D.spMin_pos.le (sq_nonneg D.k)).trans (D.potential_lower hy hr)
  rw [abs_of_nonneg h]
  exact add_le_add
    (mul_le_mul_of_nonneg_right (D.spatial_bound r hr).2 (sq_nonneg D.k))
    (mul_le_mul_of_nonneg_right (D.temporal_bound r hr).2 hy)

theorem NormalChannel.abs_a_bound (D : NormalChannel) {r : ℝ} (hr : 0 ≤ r) : |D.a r| ≤ D.aMax := by
  rw [abs_of_nonneg (D.aMin_pos.le.trans (D.a_bound r hr).1)]
  exact (D.a_bound r hr).2

theorem NormalChannel.abs_temporal_bound (D : NormalChannel) {r : ℝ} (hr : 0 ≤ r) :
    |D.temporal r| ≤ D.parMax := by
  rw [abs_of_nonneg (D.temporal_bound r hr).1]
  exact (D.temporal_bound r hr).2

def temporalPairing (D : NormalChannel) (u v : ℝ → ℝ) : ℝ :=
  ∫ r in Ioi (0:ℝ), D.temporal r*u r*v r

def rayL2Size (u : ℝ → ℝ) : ℝ := √(∫ r in Ioi (0:ℝ), u r ^ 2)

theorem ray_L2_size_nonneg (u : ℝ → ℝ) : 0 ≤ rayL2Size u := sqrt_nonneg _

theorem ray_L2_size_sq (u : ℝ → ℝ) : rayL2Size u ^ 2 = ∫ r in Ioi (0:ℝ), u r^2 :=
  sq_sqrt (integral_nonneg (fun r => sq_nonneg (u r)))

theorem temporal_pairing_integrable (D : NormalChannel) {u v : ℝ → ℝ}
    (hu : MemLp u 2 normalRayMeasure) (hv : MemLp v 2 normalRayMeasure) :
    Integrable (fun r => D.temporal r*u r*v r) normalRayMeasure :=
  ray_product_integrable hu hv D.continuous_temporal.measurable fun _ hr => D.abs_temporal_bound hr.le

theorem temporal_pairing_norm_bound (D : NormalChannel) {u v : ℝ → ℝ}
    (hu : MemLp u 2 normalRayMeasure) (hv : MemLp v 2 normalRayMeasure) :
    (∫ r in Ioi (0:ℝ), ‖D.temporal r*u r*v r‖) ≤ D.parMax * (rayL2Size u * rayL2Size v) := by
  have hC : 0 ≤ D.parMax := (D.temporal_bound 0 le_rfl).1.trans (D.temporal_bound 0 le_rfl).2
  have hc := integral_mul_norm_le_Lp_mul_Lq (μ := normalRayMeasure)
    (Real.HolderConjugate.two_two : Real.HolderConjugate 2 2)
    (by simpa using hu) (by simpa using hv)
  simp_rw [← sqrt_eq_rpow, Real.rpow_two, Real.norm_eq_abs, sq_abs] at hc
  change (∫ r in Ioi (0:ℝ), |u r| * |v r|) ≤ rayL2Size u*rayL2Size v at hc
  calc
    _ ≤ D.parMax * ∫ r in Ioi (0:ℝ), |u r| * |v r| := by
      rw [← integral_const_mul]
      apply integral_mono_ae (temporal_pairing_integrable D hu hv).norm
        ((hu.norm.integrable_mul hv.norm).const_mul D.parMax)
      filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi (0:ℝ)) measurableSet_Ioi] with r hr
      rw [norm_mul,norm_mul,mul_assoc,Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (D.abs_temporal_bound hr.le) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hc hC

theorem temporal_pairing_bound (D : NormalChannel) {u v : ℝ → ℝ}
    (hu : MemLp u 2 normalRayMeasure) (hv : MemLp v 2 normalRayMeasure) :
    |temporalPairing D u v| ≤ D.parMax * (rayL2Size u * rayL2Size v) := by
  rw [← Real.norm_eq_abs]
  exact (norm_integral_le_integral_norm _).trans (temporal_pairing_norm_bound D hu hv)

private theorem channel_pairing_integrable (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (u v : NormalProfile) :
    Integrable (fun r => D.a r * u.gradient r * v.gradient r +
      D.potential y r * u.amplitude r * v.amplitude r) normalRayMeasure :=
  (ray_product_integrable u.gradient_L2 v.gradient_L2 D.continuous_a.measurable
    fun _ hr => D.abs_a_bound hr.le).add
    (ray_product_integrable u.amplitude_L2 v.amplitude_L2 (D.continuous_potential y).measurable
      fun _ hr => D.potential_upper hy hr.le)

theorem normal_channel_flux (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (u : NormalTransfer D.a (D.potential y)) (v : NormalProfile) :
    normalBilinear D.a (D.potential y) u.toNormalProfile v = boundaryFlux D.a u * v.amplitude 0 :=
  normal_bilinear_flux u v D.continuous_a.measurable (D.continuous_potential y).measurable
    (fun _ hr => D.abs_a_bound hr.le) (fun _ hr => D.potential_upper hy hr.le)

private theorem normal_bilinear_symm (a p : ℝ → ℝ) (u v : NormalProfile) :
    normalBilinear a p u v = normalBilinear a p v u := by
  apply integral_congr_ae
  exact Eventually.of_forall fun r => by ring

private theorem normal_bilinear_sub_left (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (u v w : NormalProfile) :
    normalBilinear D.a (D.potential y) (profileDifference u v) w =
      normalBilinear D.a (D.potential y) v w - normalBilinear D.a (D.potential y) u w := by
  unfold normalBilinear
  have hs := integral_sub (channel_pairing_integrable D hy v w) (channel_pairing_integrable D hy u w)
  unfold normalRayMeasure at hs
  rw [← hs]
  apply integral_congr_ae
  exact Eventually.of_forall fun r => by simp only [profileDifference]; ring

private theorem normal_bilinear_variation (D : NormalChannel) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z)
    (u v : NormalProfile) :
    normalBilinear D.a (D.potential z) u v - normalBilinear D.a (D.potential y) u v =
      (z-y) * temporalPairing D u.amplitude v.amplitude := by
  unfold normalBilinear temporalPairing
  have hs := integral_sub (channel_pairing_integrable D hz u v) (channel_pairing_integrable D hy u v)
  unfold normalRayMeasure at hs
  rw [← hs,← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun r => by simp only [NormalChannel.potential,modePotential]; ring

/-- Exact flux difference, before taking any limit or dividing by the
frequency difference. -/
theorem transverse_flux_difference (D : NormalChannel) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z)
    (u : NormalTransfer D.a (D.potential y)) (v : NormalTransfer D.a (D.potential z)) :
    boundaryFlux D.a v - boundaryFlux D.a u =
      (z-y) * temporalPairing D u.amplitude v.amplitude := by
  have h := normal_bilinear_variation D hy hz u.toNormalProfile v.toNormalProfile
  rwa [normal_bilinear_symm D.a (D.potential z),normal_channel_flux D hz,
    normal_channel_flux D hy,u.boundary_one,v.boundary_one,mul_one,mul_one] at h

private theorem normal_bilinear_coercive (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (w : NormalProfile) :
    (D.spMin*D.k^2) * rayL2Size w.amplitude^2 ≤ normalBilinear D.a (D.potential y) w w := by
  rw [ray_L2_size_sq,← integral_const_mul]
  apply integral_mono_ae
  · have hi := (memLp_two_iff_integrable_sq w.amplitude_L2.aestronglyMeasurable).mp w.amplitude_L2
    exact hi.const_mul _
  · exact channel_pairing_integrable D hy w w
  · filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi (0:ℝ)) measurableSet_Ioi] with r hr
    have ha : 0 ≤ D.a r := D.aMin_pos.le.trans (D.a_bound r hr.le).1
    have h := mul_le_mul_of_nonneg_right (D.potential_lower hy hr.le) (sq_nonneg (w.amplitude r))
    have hnr := mul_nonneg ha (sq_nonneg (w.gradient r))
    nlinarith only [h,hnr]

theorem transverse_amplitude_L2_stability (D : NormalChannel) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z)
    (u : NormalTransfer D.a (D.potential y)) (v : NormalTransfer D.a (D.potential z)) :
    rayL2Size (fun r => v.amplitude r-u.amplitude r) ≤
      |z-y| * D.parMax / (D.spMin*D.k^2) * rayL2Size u.amplitude := by
  let w := profileDifference u.toNormalProfile v.toNormalProfile
  have h0 : w.amplitude 0 = 0 := by simp [w,profileDifference,u.boundary_one,v.boundary_one]
  have h := normal_bilinear_variation D hy hz u.toNormalProfile w
  rw [normal_channel_flux D hy u w,h0,mul_zero,sub_zero] at h
  have hE := normal_bilinear_sub_left D hz u.toNormalProfile v.toNormalProfile w
  change normalBilinear D.a (D.potential z) w w = _ at hE
  rw [normal_channel_flux D hz v w,h0,mul_zero,zero_sub,h] at hE
  have hcs := temporal_pairing_bound D u.amplitude_L2 w.amplitude_L2
  have hco := normal_bilinear_coercive D hz w
  rw [hE] at hco
  have hle : (D.spMin*D.k^2) * rayL2Size w.amplitude^2 ≤
      |z-y| * D.parMax*rayL2Size u.amplitude*rayL2Size w.amplitude := by
    refine hco.trans ((le_abs_self _).trans ?_)
    rw [abs_neg,abs_mul]
    calc
      _ ≤ |z-y| *(D.parMax*(rayL2Size u.amplitude*rayL2Size w.amplitude)) :=
        mul_le_mul_of_nonneg_left hcs (abs_nonneg _)
      _ = _ := by ring
  have hp : 0 < D.spMin*D.k^2 := mul_pos D.spMin_pos (pow_pos D.k_pos _)
  change rayL2Size w.amplitude ≤ _
  by_cases hW : rayL2Size w.amplitude = 0
  · have hC : 0 ≤ D.parMax := (D.temporal_bound 0 le_rfl).1.trans (D.temporal_bound 0 le_rfl).2
    rw [hW]
    exact mul_nonneg (div_nonneg (mul_nonneg (abs_nonneg _) hC) hp.le) (ray_L2_size_nonneg _)
  · have hWpos := lt_of_le_of_ne (ray_L2_size_nonneg w.amplitude) (Ne.symm hW)
    have hcancel : (D.spMin*D.k^2) * rayL2Size w.amplitude ≤
        |z-y| * D.parMax * rayL2Size u.amplitude := by
      apply (mul_le_mul_iff_left₀ hWpos).mp
      convert hle using 1
      ring
    rw [div_mul_eq_mul_div,le_div_iff₀ hp]
    rwa [mul_comm (rayL2Size w.amplitude)]

theorem normal_channel_energy_minimizer (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (u : NormalTransfer D.a (D.potential y)) (v : NormalProfile) (hv : v.amplitude 0 = 1) :
    normalBilinear D.a (D.potential y) u.toNormalProfile u.toNormalProfile ≤
      normalBilinear D.a (D.potential y) v v := by
  let w := profileDifference u.toNormalProfile v
  have hw : w.amplitude 0 = 0 := by simp [w,profileDifference,hv,u.boundary_one]
  have h2 : normalBilinear D.a (D.potential y) u.toNormalProfile w = 0 := by
    rw [normal_channel_flux D hy u w,hw,mul_zero]
  have h := normal_bilinear_sub_left D hy u.toNormalProfile v v
  have h' := normal_bilinear_sub_left D hy u.toNormalProfile v w
  change normalBilinear D.a (D.potential y) w v = _ at h
  change normalBilinear D.a (D.potential y) w w = _ at h'
  rw [normal_bilinear_symm D.a (D.potential y) v w,h2,sub_zero] at h'
  have h3 : normalBilinear D.a (D.potential y) u.toNormalProfile v =
      normalBilinear D.a (D.potential y) u.toNormalProfile u.toNormalProfile := by
    rw [normal_channel_flux D hy u v,normal_channel_flux D hy u u.toNormalProfile,
      hv,u.boundary_one]
  have hpos := normal_bilinear_coercive D hy w
  have h0 : 0 ≤ (D.spMin*D.k^2) * rayL2Size w.amplitude^2 :=
    mul_nonneg (mul_nonneg D.spMin_pos.le (sq_nonneg _)) (sq_nonneg _)
  linarith only [h, h', h3, hpos, h0]

end UV.TemporalRay
