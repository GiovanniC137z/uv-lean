import UV.ContinueHeatMaxwellSignPrimitive
import UV.ContinueHeatMaxwellSignSphere
import UV.ContinueHeatMaxwellSignMarks

/-! The exact angularly integrated soft two-mark coefficient. -/

noncomputable section

namespace UV.HeatMaxwell

open MeasureTheory Set Filter
open scoped Topology

/-- The continuum two-mark quadratic response after polar integration and
the substitution u = ‖k‖². The factor 2 comes from the spinor trace 4
and the radial Jacobian 1/2. -/
def heatTransverseSoftCoefficient (m a : ℝ) : ℝ :=
  (2 / (2 * Real.pi) ^ 4) *
    ∫ u in Ioi 0, u * ∫ n : HeatUnitSphere,
      heatTwoMarkQuadratic u (Real.sqrt u * n.1 1) (Real.sqrt u * n.1 2)
        (heatNormalizedGaussian ((m * a) ^ 2) u)
        ∂(volume : Measure UV.ScalarMomentum).toSphere

theorem heatTransverseSoftCoefficient_eq_radial {m a : ℝ} (hm : 0 < m) (ha : 0 < a) :
    heatTransverseSoftCoefficient m a = heatMaxwellCoefficient ((m * a) ^ 2) := by
  have hx := sq_pos_of_pos (mul_pos hm ha)
  rw [← heatAngularCoefficient_eq_radial hx]
  unfold heatTransverseSoftCoefficient heatAngularCoefficient
  have h :
      (∫ u in Ioi 0, u * ∫ n : HeatUnitSphere,
        heatTwoMarkQuadratic u (Real.sqrt u * n.1 1) (Real.sqrt u * n.1 2)
          (heatNormalizedGaussian ((m * a) ^ 2) u)
          ∂(volume : Measure UV.ScalarMomentum).toSphere) =
        ∫ u in Ioi 0, (2 * Real.pi ^ 2) * (u * heatAngularMean u
          (heatNormalizedGaussian ((m * a) ^ 2) u)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    rw [heatTwoMarkQuadratic_sphere_mean (le_of_lt hu)]
    ring
  rw [h, integral_const_mul]
  have hp := Real.pi_ne_zero
  field_simp
  ring

/-- The angularly integrated heat-link quadratic jet is strictly positive
for every positive mass and positive heat width. -/
theorem heatTransverseSoftCoefficient_pos {m a : ℝ} (hm : 0 < m) (ha : 0 < a) :
    0 < heatTransverseSoftCoefficient m a := by
  rw [heatTransverseSoftCoefficient_eq_radial hm ha]
  exact heatMaxwellCoefficient_mass_width_pos hm ha

/-- The stated a⁻² rescaling of the two-mark kernel and an external
readout tending to one preserve the soft quotient coefficient. -/
theorem heatSoft_width_transfer {a c : ℝ} (ha : 0 < a) {F h : ℝ → ℝ}
    (hF : Tendsto (fun t => F t / t ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 c))
    (hh : Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    Tendsto (fun t => (a ^ 2)⁻¹ * F (a * t) * h t / t ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  have he : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hscale : Tendsto (fun t : ℝ => a * t) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, he.mono fun _ ht => mul_pos ha ht⟩
    simpa only [mul_zero] using
      ((tendsto_id (x := 𝓝 (0 : ℝ))).const_mul a).mono_left nhdsWithin_le_nhds
  have ht := (hF.comp hscale).mul hh
  rw [mul_one] at ht
  apply ht.congr'
  filter_upwards [he] with t ht
  change F (a * t) / (a * t) ^ 2 * h t =
    (a ^ 2)⁻¹ * F (a * t) * h t / t ^ 2
  field_simp

end UV.HeatMaxwell
