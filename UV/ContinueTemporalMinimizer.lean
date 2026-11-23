import UV.ContinueTemporalExistence
import UV.ContinueTemporalWeakRay

/-! The unique normalized minimizer on the full half-line form domain,
and the manuscript's two flux and readout derivatives for the
constructed family. -/

noncomputable section

namespace UV.TemporalRay

open MeasureTheory Set Filter Real
open scoped Topology

def normalEnergyDensity (D : NormalChannel) (y : ℝ) (v : NormalEnergyProfile) (r : ℝ) : ℝ :=
  D.a r*(v.slope r)^2 + D.potential y r*(v.value r)^2

def normalFormEnergy (D : NormalChannel) (y : ℝ) (v : NormalEnergyProfile) : ℝ :=
  (∫ r in Ioi (0:ℝ), normalEnergyDensity D y v r)/2

theorem normal_energy_density_integrable (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (v : NormalEnergyProfile) : Integrable (normalEnergyDensity D y v) normalRayMeasure := by
  have hs := ray_product_integrable v.slope_L2 v.slope_L2 D.continuous_a.measurable
    fun _ hr => D.abs_a_bound hr.le
  have hv := ray_product_integrable v.value_L2 v.value_L2 (D.continuous_potential y).measurable
    fun _ hr => D.potential_upper hy hr.le
  exact (hs.add hv).congr (Eventually.of_forall fun r => by
    change D.a r*v.slope r*v.slope r + D.potential y r*v.value r*v.value r = _
    unfold normalEnergyDensity
    ring)

private theorem energy_density_nonneg (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (v : NormalEnergyProfile) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ normalEnergyDensity D y v r :=
  add_nonneg (mul_nonneg (D.aMin_pos.le.trans (D.a_bound r hr).1) (sq_nonneg _))
    (mul_nonneg ((mul_nonneg D.spMin_pos.le (sq_nonneg D.k)).trans (D.potential_lower hy hr)) (sq_nonneg _))

theorem normal_form_energy_nonneg (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y) (v : NormalEnergyProfile) :
    0 ≤ normalFormEnergy D y v := by
  apply div_nonneg _ (by norm_num)
  exact integral_nonneg_of_ae ((ae_restrict_mem (μ := volume) measurableSet_Ioi).mono
    fun _ hr => energy_density_nonneg D hy v hr.le)

theorem normal_zero_energy_slope (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (v : NormalEnergyProfile) (he : normalFormEnergy D y v = 0) :
    v.slope =ᵐ[normalRayMeasure] 0 := by
  have hray : ∀ᵐ r ∂normalRayMeasure, 0 < r := ae_restrict_mem measurableSet_Ioi
  have hz : (∫ r, normalEnergyDensity D y v r ∂normalRayMeasure) = 0 := by
    change (∫ r, normalEnergyDensity D y v r ∂normalRayMeasure)/2 = 0 at he
    linarith only [he]
  have h := (integral_eq_zero_iff_of_nonneg_ae (hray.mono fun _ hr => energy_density_nonneg D hy v hr.le)
    (normal_energy_density_integrable D hy v)).mp hz
  filter_upwards [hray,h] with r hr h0
  have hp : 0 ≤ D.potential y r := (mul_nonneg D.spMin_pos.le (sq_nonneg _)).trans (D.potential_lower hy hr.le)
  have ha := D.aMin_pos.trans_le (D.a_bound r hr.le).1
  have h1 : D.a r*(v.slope r)^2 = 0 := le_antisymm (by
    change D.a r*(v.slope r)^2 + D.potential y r*(v.value r)^2 = 0 at h0
    linarith only [h0,mul_nonneg hp (sq_nonneg (v.value r))]) (mul_nonneg ha.le (sq_nonneg _))
  exact pow_eq_zero ((mul_eq_zero.mp h1).resolve_left ha.ne')

def NormalEnergyProfile.sub (v u : NormalEnergyProfile) : NormalEnergyProfile where
  value r := v.value r-u.value r
  slope r := v.slope r-u.slope r
  value_L2 := v.value_L2.sub u.value_L2
  slope_L2 := v.slope_L2.sub u.slope_L2
  primitive r hr := by
    rw [intervalIntegral.integral_sub (normal_ray_interval_integrable v.slope_L2 le_rfl hr)
      (normal_ray_interval_integrable u.slope_L2 le_rfl hr), v.primitive r hr, u.primitive r hr]
    ring

/-- Exact energy gap for a normalized comparison profile with weak derivative. -/
theorem normal_minimum_energy_gap (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (u : NormalTransfer D.a (D.potential y)) (v : NormalEnergyProfile) (hv : v.value 0 = 1) :
    normalFormEnergy D y v - normalFormEnergy D y u.toNormalProfile.toEnergyProfile =
      normalFormEnergy D y (v.sub u.toNormalProfile.toEnergyProfile) := by
  let U := u.toNormalProfile.toEnergyProfile
  let d := v.sub U
  let cross := fun r => D.potential y r*u.amplitude r*d.value r + (D.a r*u.gradient r)*d.slope r
  have hc : Integrable cross normalRayMeasure := (ray_product_integrable u.amplitude_L2 d.value_L2
      (D.continuous_potential y).measurable fun _ hr => D.potential_upper hy hr.le).add
    (ray_product_integrable u.gradient_L2 d.slope_L2 D.continuous_a.measurable fun _ hr => D.abs_a_bound hr.le)
  have hz := normal_weak_flux_identity D hy u d
  have hd : d.value 0 = 0 := by simp [d,U,NormalEnergyProfile.sub,NormalProfile.toEnergyProfile,hv,u.boundary_one]
  rw [hd,mul_zero] at hz
  change (∫ r, cross r ∂normalRayMeasure) = 0 at hz
  have he : normalEnergyDensity D y v = fun r => normalEnergyDensity D y U r +
      normalEnergyDensity D y d r + 2*cross r := by
    funext r
    dsimp [d,U,normalEnergyDensity,cross,NormalEnergyProfile.sub,NormalProfile.toEnergyProfile]
    ring
  change (∫ r, normalEnergyDensity D y v r ∂normalRayMeasure)/2 -
    (∫ r, normalEnergyDensity D y U r ∂normalRayMeasure)/2 =
    (∫ r, normalEnergyDensity D y d r ∂normalRayMeasure)/2
  have hi : Integrable (fun r => normalEnergyDensity D y U r + normalEnergyDensity D y d r) normalRayMeasure :=
    (normal_energy_density_integrable D hy U).add (normal_energy_density_integrable D hy d)
  rw [he]
  dsimp only
  rw [integral_add hi (hc.const_mul 2), integral_add (normal_energy_density_integrable D hy U) (normal_energy_density_integrable D hy d),
    integral_const_mul,hz]
  ring

theorem normal_minimizes_full_form (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (v : NormalEnergyProfile) (hv : v.value 0 = 1) :
    normalFormEnergy D y (normalMinimizingTransfer D y hy).toNormalProfile.toEnergyProfile ≤
      normalFormEnergy D y v := by
  apply sub_nonneg.mp
  rw [normal_minimum_energy_gap D hy _ v hv]
  exact normal_form_energy_nonneg D hy _

/-- Equality forces equality of the actual weak slopes almost everywhere
and equality of the continuous Sobolev representatives at every depth. -/
theorem normal_minimizer_unique (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y)
    (u : NormalTransfer D.a (D.potential y)) (v : NormalEnergyProfile) (hv : v.value 0 = 1)
    (he : normalFormEnergy D y v = normalFormEnergy D y u.toNormalProfile.toEnergyProfile) :
    v.slope =ᵐ[normalRayMeasure] u.gradient ∧ ∀ r ≥ 0, v.value r = u.amplitude r := by
  let U := u.toNormalProfile.toEnergyProfile
  let d := v.sub U
  have hg := normal_minimum_energy_gap D hy u v hv
  rw [he,sub_self] at hg
  have hs : v.slope =ᵐ[normalRayMeasure] u.gradient :=
    (normal_zero_energy_slope D hy d hg.symm).mono fun _ h => sub_eq_zero.mp h
  refine ⟨hs, fun r hr => ?_⟩
  have hu := U.primitive r hr
  change u.amplitude r = u.amplitude 0 + ∫ t in (0:ℝ)..r, u.gradient t at hu
  rw [v.primitive r hr,hu,hv,u.boundary_one]
  congr 1
  rw [intervalIntegral.integral_of_le hr,intervalIntegral.integral_of_le hr]
  exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset Ioc_subset_Ioi_self hs)

/-- Both equations at the constructed minimizing transfer. At zero squared
frequency these are right derivatives, at positive frequencies ordinary derivatives. -/
theorem normal_curvature_response (D : NormalChannel) {y : ℝ} (hy : 0 ≤ y) {r : ℝ} (hr : 0 ≤ r) :
    let U := normalMinimizingTransfer D
    HasDerivWithinAt (normalFamilyFlux D U)
      (∫ s in Ioi (0:ℝ), D.temporal s*(U y hy).amplitude s^2) (Ici 0) y ∧
    HasDerivWithinAt (familyNormalReadout D U r)
      (-(∫ s in Ioi (0:ℝ), normalGreenKernel D (U y hy).amplitude r s *
        D.temporal s * (U y hy).amplitude s)) (Ici 0) y := by
  refine ⟨?_,normal_family_readout_green_derivative D (normalMinimizingTransfer D) hy hr⟩
  simpa only [temporalPairing,pow_two,mul_assoc] using
    normal_family_flux_hasDerivWithinAt D (normalMinimizingTransfer D) hy

/-- The frequency test in the actual carrier variable, with y = ω². -/
theorem normal_carrier_frequency_independent_iff (D : NormalChannel) {r : ℝ} (hr : 0 < r) :
    (∀ ω : ℝ, (normalMinimizingTransfer D (ω^2) (sq_nonneg _)).amplitude r =
      (normalMinimizingTransfer D 0 le_rfl).amplitude r) ↔ ∀ t ≥ 0, D.temporal t = 0 := by
  rw [← normal_readout_frequency_independent_iff D (normalMinimizingTransfer D) hr]
  constructor
  · intro h y hy
    let value := fun t : Ici (0:ℝ) => (normalMinimizingTransfer D t.val t.property).amplitude r
    have he : (⟨y,hy⟩ : Ici (0:ℝ)) = ⟨(√y)^2,sq_nonneg (√y)⟩ := Subtype.ext (sq_sqrt hy).symm
    exact (congrArg value he).trans (h (√y))
  · intro h ω
    exact h (ω^2) (sq_nonneg _)

end UV.TemporalRay
