import UV.Convergence
import UV.ContinuationSectorPlane
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-! Normal Green readout of two real, compactly supported unit profiles.
The normal coordinate is independent of the norm-one GT carrier. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace UV.NextNativeBridge

structure NormalProfile where
  profile : ℝ → ℝ
  continuous_profile : Continuous profile
  compact_profile : HasCompactSupport profile
  unit_profile : (∫ y, profile y ^ 2) = 1

def Separated (f g : NormalProfile) (d : ℝ) : Prop :=
  ∀ y z : ℝ, f.profile y ≠ 0 → g.profile z ≠ 0 → d ≤ |y - z|

theorem separated_symm {f g : NormalProfile} {d : ℝ} (h : Separated f g d) :
    Separated g f d := by
  intro y z hy hz
  simpa only [abs_sub_comm y z] using h z y hz hy

def unitNormalKernel (u : ℝ) : ℝ := Real.exp (-|u|) / 2

private theorem unit_kernel_integrable : Integrable unitNormalKernel := by
  have h := UV.integrable_norm_pow_exp (E := ℝ) (μ := volume) (a := 1) (by norm_num) 0
  simpa only [unitNormalKernel, Real.norm_eq_abs, pow_zero, one_mul] using h.div_const 2

theorem unit_normal_kernel_mass : (∫ u, unitNormalKernel u) = 1 := by
  have hpos : (∫ u in Ioi (0 : ℝ), unitNormalKernel u) = 1 / 2 := by
    rw [show (∫ u in Ioi (0 : ℝ), unitNormalKernel u) =
        ∫ u in Ioi (0 : ℝ), Real.exp (-u) / 2 by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact congrArg (fun x : ℝ => Real.exp (-x) / 2) (abs_of_pos (mem_Ioi.mp hu))]
    rw [integral_div, integral_exp_neg_Ioi_zero]
  have hneg : (∫ u in Iic (0 : ℝ), unitNormalKernel u) = 1 / 2 := by
    rw [← neg_zero, ← integral_comp_neg_Ioi]
    simpa only [unitNormalKernel, abs_neg] using hpos
  rw [← integral_add_compl measurableSet_Ioi unit_kernel_integrable, compl_Ioi, hpos, hneg]
  norm_num

def normalGreenKernel (ω t : ℝ) : ℝ := Real.exp (-ω * |t|) / (2 * ω)

def normalCovariance (f g : NormalProfile) (ω : ℝ) : ℝ :=
  ∫ y, f.profile y * ∫ z, g.profile z * normalGreenKernel ω (y - z)

theorem normalCovariance_stronglyMeasurable (f g : NormalProfile) :
    StronglyMeasurable (normalCovariance f g) := by
  unfold normalCovariance
  apply StronglyMeasurable.integral_prod_right
  have h : StronglyMeasurable (fun a : ℝ × ℝ =>
      ∫ z, g.profile z * normalGreenKernel a.1 (a.2 - z)) := by
    apply StronglyMeasurable.integral_prod_right
    unfold normalGreenKernel
    exact ((g.continuous_profile.measurable.comp measurable_snd).mul
      (by fun_prop : Measurable (fun a : (ℝ × ℝ) × ℝ =>
        Real.exp (-a.1.1 * |a.1.2 - a.2|) / (2 * a.1.1)))).stronglyMeasurable
  exact (f.continuous_profile.comp continuous_snd).stronglyMeasurable.mul h

/-- The complete mixed normal integration has the exponential gap. The same
formula with (d=0) bounds every covariance entry. -/
theorem normalCovariance_bound (f g : NormalProfile) {d ω : ℝ}
    (hω : 0 < ω) (hd : Separated f g d) :
    ‖normalCovariance f g ω‖ ≤
      (∫ y, ‖f.profile y‖) * (∫ z, ‖g.profile z‖) * Real.exp (-ω * d) / (2 * ω) := by
  let A := Real.exp (-ω * d) / (2 * ω)
  have hf := (f.continuous_profile.integrable_of_hasCompactSupport (μ := volume) f.compact_profile).norm
  have hg := (g.continuous_profile.integrable_of_hasCompactSupport (μ := volume) g.compact_profile).norm
  have he : ‖normalCovariance f g ω‖ ≤ ∫ y, ‖f.profile y‖ * ((∫ z, ‖g.profile z‖) * A) := by
    apply norm_integral_le_of_norm_le (hf.mul_const _)
    refine Eventually.of_forall fun y => ?_
    by_cases hy : f.profile y = 0
    · simp [hy]
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [← integral_mul_const]
    apply norm_integral_le_of_norm_le (hg.mul_const _)
    refine Eventually.of_forall fun z => ?_
    have hnonneg : 0 ≤ normalGreenKernel ω (y - z) := by
      unfold normalGreenKernel
      positivity
    rw [norm_mul, Real.norm_of_nonneg hnonneg]
    by_cases hz : g.profile z = 0
    · simp [hz]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left (hd y z hy hz) hω.le])
  rw [integral_mul_const, ← mul_assoc] at he
  simpa only [A, mul_div_assoc] using he

private theorem unitNormalKernel_nonneg (u : ℝ) : 0 ≤ unitNormalKernel u := by
  unfold unitNormalKernel
  positivity

/-- Exact rescaling of the literal Green kernel. -/
theorem normalCovariance_rescale (f g : NormalProfile) {ω : ℝ} (hω : 0 < ω) :
    ω ^ 2 * normalCovariance f g ω =
      ∫ y, f.profile y * ∫ u, g.profile (y + u / ω) * unitNormalKernel u := by
  have hin (y : ℝ) : (∫ u, g.profile (y + u / ω) * unitNormalKernel u) =
      ω ^ 2 * ∫ z, g.profile z * normalGreenKernel ω (y - z) := by
    let F := fun t : ℝ => g.profile (t + y) * normalGreenKernel ω (-t)
    have htrans : (∫ z, g.profile z * normalGreenKernel ω (y - z)) = ∫ t, F t := by
      calc
        _ = ∫ t, g.profile (t + y) * normalGreenKernel ω (y - (t + y)) :=
          (integral_add_right_eq_self (μ := volume)
            (fun z : ℝ => g.profile z * normalGreenKernel ω (y - z)) y).symm
        _ = _ := by
          congr 1
          funext t
          simp [F]
    have hscale := Measure.integral_comp_mul_left F ω⁻¹
    rw [inv_inv, abs_of_pos hω, smul_eq_mul] at hscale
    have hpoint (u : ℝ) : g.profile (y + u / ω) * unitNormalKernel u =
        ω * F (ω⁻¹ * u) := by
      unfold F normalGreenKernel unitNormalKernel
      rw [abs_neg, abs_mul, abs_of_pos (inv_pos.mpr hω)]
      have hs : -(ω * (ω⁻¹ * |u|)) = -|u| := by
        rw [← mul_assoc, mul_inv_cancel₀ hω.ne', one_mul]
      rw [neg_mul, hs, show y + u / ω = ω⁻¹ * u + y by rw [div_eq_inv_mul, add_comm]]
      field_simp [hω.ne']
    simp_rw [hpoint]
    rw [integral_const_mul, hscale, htrans]
    ring
  simp_rw [hin, normalCovariance, ← integral_const_mul]
  congr 1
  funext y
  ring_nf

private theorem profile_bound (f : NormalProfile) : ∃ C ≥ 0, ∀ y, ‖f.profile y‖ ≤ C := by
  have h := f.compact_profile
  obtain ⟨C, hC⟩ := ((h.image f.continuous_profile).image continuous_norm).bddAbove
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  by_cases hy : y ∈ tsupport f.profile
  · exact (hC ⟨f.profile y, ⟨y, hy, rfl⟩, rfl⟩).trans (le_max_left _ _)
  · simp only [tsupport] at hy
    have hz : f.profile y = 0 := by
      by_contra hne
      exact hy (subset_closure hne)
    simp [hz]

private theorem normal_readout_tendsto (g : NormalProfile) (y C : ℝ)
    (hC : ∀ z, ‖g.profile z‖ ≤ C) :
    Tendsto (fun ω : ℝ => ∫ u, g.profile (y + u / ω) * unitNormalKernel u)
      atTop (𝓝 (g.profile y)) := by
  have h : Tendsto (fun ω : ℝ => ∫ u, g.profile (y + u / ω) * unitNormalKernel u)
      atTop (𝓝 (∫ u, g.profile y * unitNormalKernel u)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun u => C * unitNormalKernel u)
    · exact Eventually.of_forall (fun ω => by
        unfold unitNormalKernel
        exact ((g.continuous_profile.comp
          (by fun_prop : Continuous (fun u : ℝ => y + u / ω))).mul
          (by fun_prop : Continuous (fun u : ℝ =>
            Real.exp (-|u|) / 2))).aestronglyMeasurable)
    · exact Eventually.of_forall (fun _ => Eventually.of_forall fun u => by
        rw [norm_mul, Real.norm_of_nonneg (unitNormalKernel_nonneg _)]
        exact mul_le_mul_of_nonneg_right (hC _) (unitNormalKernel_nonneg _))
    · exact unit_kernel_integrable.const_mul C
    · refine Eventually.of_forall fun u => ?_
      have hu : Tendsto (fun ω : ℝ => u / ω) atTop (𝓝 0) := by
        simpa only [div_eq_mul_inv, mul_zero] using
          (tendsto_inv_atTop_zero.const_mul u : Tendsto (fun ω : ℝ => u * ω⁻¹) atTop _)
      have hy : Tendsto (fun ω : ℝ => y + u / ω) atTop (𝓝 y) := by
        simpa only [add_zero] using tendsto_const_nhds.add hu
      exact (g.continuous_profile.continuousAt.tendsto.comp hy).mul_const _
  simpa only [integral_const_mul, unit_normal_kernel_mass, mul_one] using h

/-- The high-frequency diagonal coefficient counts the entire norm-one
normal profile. Signed real profiles are allowed. -/
theorem normalCovariance_diagonal_tendsto (f : NormalProfile) :
    Tendsto (fun ω : ℝ => ω ^ 2 * normalCovariance f f ω) atTop (𝓝 1) := by
  obtain ⟨C, hC₀, hC⟩ := profile_bound f
  have h : Tendsto (fun ω : ℝ => ∫ y, f.profile y * ∫ u,
      f.profile (y + u / ω) * unitNormalKernel u) atTop (𝓝 (∫ y, f.profile y ^ 2)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun y => ‖f.profile y‖ * C)
    · exact Eventually.of_forall (fun ω => by
        use fun y => f.profile y * ∫ u, f.profile (y + u / ω) * unitNormalKernel u
        constructor
        · apply f.continuous_profile.stronglyMeasurable.mul
          apply StronglyMeasurable.integral_prod_right
          unfold unitNormalKernel
          exact ((f.continuous_profile.comp
            (by fun_prop : Continuous (fun a : ℝ × ℝ => a.1 + a.2 / ω))).mul
            (by fun_prop : Continuous (fun a : ℝ × ℝ =>
              Real.exp (-|a.2|) / 2))).stronglyMeasurable
        · rfl)
    · exact Eventually.of_forall (fun _ => Eventually.of_forall fun y => by
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        calc
          _ ≤ ∫ u, C * unitNormalKernel u := by
            apply norm_integral_le_of_norm_le (unit_kernel_integrable.const_mul C)
            exact Eventually.of_forall fun u => by
              rw [norm_mul, Real.norm_of_nonneg (unitNormalKernel_nonneg _)]
              exact mul_le_mul_of_nonneg_right (hC _) (unitNormalKernel_nonneg _)
          _ = C := by rw [integral_const_mul, unit_normal_kernel_mass, mul_one])
    · exact (f.continuous_profile.integrable_of_hasCompactSupport (μ := volume) f.compact_profile).norm.mul_const C
    · exact Eventually.of_forall fun y => by
        simpa only [pow_two] using (normal_readout_tendsto f y C hC).const_mul (f.profile y)
  rw [f.unit_profile] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ω hω
  exact (normalCovariance_rescale f f hω).symm

end UV.NextNativeBridge
