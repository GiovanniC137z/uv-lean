import UV.ContinueTemporalRiccati
import UV.ContinueTemporalGreenOperator
import UV.ContinueTemporalPolarization

/-! Construction of the half-line transfer from the curvature coefficients.
The auxiliary negative half-ray uses constant endpoint coefficients to
give ordinary derivatives at zero. All bounds and energies use the
proper normal ray. -/

noncomputable section

namespace UV.TemporalRay

open MeasureTheory Filter Set Real
open scoped Topology

private theorem channel_aMax_pos (D : NormalChannel) : 0 < D.aMax :=
  D.aMin_pos.trans_le ((D.a_bound 0 le_rfl).1.trans (D.a_bound 0 le_rfl).2)

private theorem channel_mass_pos (D : NormalChannel) : 0 < D.spMin*D.k^2 :=
  mul_pos D.spMin_pos (pow_pos D.k_pos 2)

private theorem channel_mass_order (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y) :
    D.spMin*D.k^2 ≤ D.spMax*D.k^2 + D.parMax*y :=
  (D.potential_lower (r := 0) hy le_rfl).trans
    ((le_abs_self _).trans (D.potential_upper (r := 0) hy le_rfl))

private def channelImpedance (D : NormalChannel) (y : ℝ) (hy : 0 ≤ y) : ImpedanceBounds where
  invA r := (D.a (max r 0))⁻¹
  p r := D.potential y (max r 0)
  continuous_invA := (D.continuous_a.comp (continuous_id.max continuous_const)).inv₀
    fun r => (D.aMin_pos.trans_le (D.a_bound _ (le_max_right r 0)).1).ne'
  continuous_p := (D.continuous_potential y).comp (continuous_id.max continuous_const)
  invMin := D.aMax⁻¹
  invMax := D.aMin⁻¹
  lo := √(D.aMin*(D.spMin*D.k^2))
  hi := √(D.aMax*(D.spMax*D.k^2+D.parMax*y))
  invMin_pos := inv_pos.mpr (channel_aMax_pos D)
  inv_bounds r := by
    have ha := D.a_bound (max r 0) (le_max_right _ _)
    exact ⟨inv_anti₀ (D.aMin_pos.trans_le ha.1) ha.2, inv_anti₀ D.aMin_pos ha.1⟩
  lo_pos := sqrt_pos.mpr (mul_pos D.aMin_pos (channel_mass_pos D))
  lo_le_hi := sqrt_le_sqrt (mul_le_mul ((D.a_bound 0 le_rfl).1.trans (D.a_bound 0 le_rfl).2)
    (channel_mass_order D hy) (channel_mass_pos D).le (channel_aMax_pos D).le)
  barriers r := by
    have hr : 0 ≤ max r 0 := le_max_right _ _
    have ha := D.aMin_pos.trans_le (D.a_bound _ hr).1
    have hP := (channel_mass_pos D).trans_le (channel_mass_order D hy)
    rw [sq_sqrt (mul_pos D.aMin_pos (channel_mass_pos D)).le,
      sq_sqrt (mul_pos (channel_aMax_pos D) hP).le]
    constructor
    · rw [← div_eq_inv_mul]
      apply (div_le_iff₀ ha).mpr
      calc
        _ ≤ D.a (max r 0)*D.potential y (max r 0) := mul_le_mul (D.a_bound _ hr).1
          (D.potential_lower hy hr) (channel_mass_pos D).le ha.le
        _ = _ := mul_comm _ _
    · rw [← div_eq_inv_mul]
      apply (le_div_iff₀ ha).mpr
      calc
        _ ≤ (D.spMax*D.k^2 + D.parMax*y)*D.aMax := mul_le_mul
          ((le_abs_self _).trans (D.potential_upper hy hr)) (D.a_bound _ hr).2 ha.le hP.le
        _ = _ := mul_comm _ _

theorem normal_ray_exp_decay_memLp {c : ℝ} (hc : 0 < c) :
    MemLp (fun r : ℝ => exp (-c*r)) 2 normalRayMeasure := by
  have hm : Continuous (fun r : ℝ => exp (-c*r)) := continuous_exp.comp (continuous_const.mul continuous_id)
  apply (memLp_two_iff_integrable_sq (μ := normalRayMeasure) hm.aestronglyMeasurable).mpr
  refine (integrableOn_exp_mul_Ioi (a := -(2*c)) (by linarith) 0).congr ?_
  filter_upwards with r
  rw [sq, ← exp_add]
  congr 1
  ring

/-- The normalized positive-energy solution exists for every squared frequency
admitted by the normal channel. No solution or boundary impedance is supplied. -/
theorem normal_transfer_exists (D : NormalChannel) (y : ℝ) (hy : 0 ≤ y) :
    Nonempty (NormalTransfer D.a (D.potential y)) := by
  let B := channelImpedance D y hy
  obtain ⟨q,hqc,hqb,hqd⟩ := exists_normal_impedance B
  let v := fun r => B.invA r*q r
  have hvc : Continuous v := B.continuous_invA.mul hqc
  let u := fun r : ℝ => exp (-(∫ t in (0:ℝ)..r, v t))
  let grad := fun r : ℝ => -(D.a r)⁻¹*q r*u r
  have hu (r : ℝ) : HasDerivAt u (-v r*u r) r := by
    have hd := intervalIntegral.integral_hasDerivAt_right (hvc.intervalIntegrable 0 r)
      hvc.aestronglyMeasurable.stronglyMeasurableAtFilter hvc.continuousAt
    simpa only [u,mul_comm] using hd.neg.exp
  have huc : Continuous u := continuous_iff_continuousAt.mpr fun r => (hu r).continuousAt
  let c := B.invMin*B.lo
  have hc : 0 < c := mul_pos B.invMin_pos B.lo_pos
  have hvl (r : ℝ) : c ≤ v r := mul_le_mul (B.inv_bounds r).1 (hqb r).1 B.lo_pos.le
    (B.invMin_pos.le.trans (B.inv_bounds r).1)
  have hub (r : ℝ) (hr : 0 ≤ r) : u r ≤ exp (-c*r) := by
    apply exp_le_exp.mpr
    have h := intervalIntegral.integral_mono_on hr (f := fun _ => c) (μ := volume) intervalIntegrable_const
      (hvc.intervalIntegrable 0 r) (fun s _ => hvl s)
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
    linarith only [h]
  have hup (r : ℝ) : 0 < u r := exp_pos _
  have huL : MemLp u 2 normalRayMeasure := by
    refine (normal_ray_exp_decay_memLp hc).mono' huc.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi (0:ℝ)) measurableSet_Ioi] with r hr
    simpa only [Real.norm_of_nonneg (hup r).le] using hub r hr.le
  have hgv (r : ℝ) (hr : 0 ≤ r) : grad r = -v r*u r := by
    dsimp [grad,v,B,channelImpedance]
    rw [max_eq_left hr,neg_mul]
  have hgL : MemLp grad 2 normalRayMeasure := by
    have hgmeas : Measurable grad := ((D.continuous_a.measurable.inv.neg.mul hqc.measurable).mul huc.measurable)
    refine (huL.const_mul (B.invMax*B.hi)).mono' hgmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi (0:ℝ)) measurableSet_Ioi] with r hr
    rw [hgv r hr.le, norm_mul, norm_neg, Real.norm_of_nonneg (hc.le.trans (hvl r)),
      Real.norm_of_nonneg (hup r).le]
    change v r*u r ≤ (B.invMax*B.hi)*u r
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (B.inv_bounds r).2 (hqb r).2 (B.lo_pos.le.trans (hqb r).1)
        (B.invMin_pos.le.trans ((B.inv_bounds r).1.trans (B.inv_bounds r).2))) (hup r).le
  refine ⟨{ amplitude := u, gradient := grad, amplitude_L2 := huL, gradient_L2 := hgL,
            boundary_one := by simp [u]
            has_gradient := fun r hr => (hgv r hr).symm ▸ hu r
            flux_derivative := ?_ }⟩
  intro r hr
  have ha := D.aMin_pos.trans_le (D.a_bound r hr).1
  have he : (fun s => D.a s*grad s) =ᶠ[𝓝 r] fun s => -q s*u s := by
    filter_upwards [D.continuous_a.continuousAt.eventually_ne ha.ne'] with s hs
    dsimp [grad]
    field_simp
  apply HasDerivAt.congr_of_eventuallyEq _ he
  convert (hqd r).neg.mul (hu r) using 1
  change D.potential y r * u r =
    -(B.invA r*q r^2 - B.p r)*u r + -q r * (-(B.invA r*q r)*u r)
  have hp : B.p r = D.potential y r := by simp [B,channelImpedance,max_eq_left hr]
  rw [hp]
  ring

/-- The channel now determines a transfer family on the whole frequency ray. -/
def normalMinimizingTransfer (D : NormalChannel) (y : ℝ) (hy : 0 ≤ y) :
    NormalTransfer D.a (D.potential y) := (normal_transfer_exists D y hy).some

end UV.TemporalRay
