import UV.ContinueRigidLawEdge
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Angular weights and solid angle for the rigid-source law, using the spatial
unit sphere of the reconstructed sector plane. -/

noncomputable section

open MeasureTheory Set Real Filter Asymptotics
open scoped ENNReal RealInnerProductSpace Topology

namespace UV.ContinueRigidLaw

abbrev Direction := UV.SectorPlane.UnitVector UV.SectorPlane.Spatial

/-- The spatial solid angle from the Euclidean volume polar decomposition. -/
def solidAngle : Measure Direction :=
  (volume : Measure UV.SectorPlane.Spatial).toSphere.map
    (fun n : Metric.sphere (0 : UV.SectorPlane.Spatial) 1 ↦ ⟨n.1, mem_sphere_zero_iff_norm.1 n.2⟩)

instance : IsFiniteMeasure solidAngle := Measure.isFiniteMeasure_map _ _

/-- The polarization-summed soft angular coefficient of the paper. -/
def angularWeight (e : ℝ) (v : UV.SectorPlane.Spatial) (n : Direction) : ℝ :=
  e^2/(2*(2*π)^3) * (‖v‖^2 - ⟪v, (n : UV.SectorPlane.Spatial)⟫^2) / doppler v n^2

theorem angularWeight_nonneg (e : ℝ) (v : UV.SectorPlane.Spatial) (n : Direction) :
    0 ≤ angularWeight e v n := by
  have h := abs_real_inner_le_norm v (n : UV.SectorPlane.Spatial)
  rw [n.property, mul_one] at h
  have hsq := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs] at hsq
  exact div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hsq)) (sq_nonneg _)

theorem angularWeight_measurable (e : ℝ) (v : UV.SectorPlane.Spatial) :
    Measurable (angularWeight e v) := by
  have hm : Measurable (fun n : Direction ↦ ⟪v, (n : UV.SectorPlane.Spatial)⟫) :=
    (continuous_const.inner continuous_id).measurable.comp measurable_subtype_coe
  have hD : Measurable (doppler v) := measurable_const.sub hm
  exact ((measurable_const.sub (hm.pow_const 2)).const_mul _).div (hD.pow_const 2)

/-- The weighted angular measure used in the Laplace law. -/
def angularMeasure (e : ℝ) (v : UV.SectorPlane.Spatial) : Measure Direction :=
  solidAngle.withDensity (fun n ↦ ENNReal.ofReal (angularWeight e v n))

theorem finite_angularMeasure (e : ℝ) {v : UV.SectorPlane.Spatial} (hv : ‖v‖ < 1) :
    IsFiniteMeasure (angularMeasure e v) := by
  let K := e^2/(2*(2*π)^3) * ‖v‖^2 / (1-‖v‖)^2
  have hK : ∀ n, angularWeight e v n ≤ K := by
    intro n
    have hd := (doppler_bounds v n).1
    have h₀ := sub_pos.mpr hv
    have hs : (1-‖v‖)^2 ≤ doppler v n^2 := pow_le_pow_left₀ h₀.le hd 2
    have hc : 0 ≤ e^2/(2*(2*π)^3) := by positivity
    calc
      _ ≤ (e^2/(2*(2*π)^3) * ‖v‖^2) / doppler v n^2 := by
        unfold angularWeight
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) hc) (sq_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hc (sq_nonneg _)) (sq_pos_of_pos h₀) hs
  constructor
  rw [angularMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hb : (∫⁻ n, ENNReal.ofReal (angularWeight e v n) ∂solidAngle) ≤
      ∫⁻ _ : Direction, ENNReal.ofReal K ∂solidAngle :=
    lintegral_mono fun n ↦ ENNReal.ofReal_le_ofReal (hK n)
  rw [lintegral_const] at hb
  exact hb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))

theorem integral_angularMeasure (e : ℝ) (v : UV.SectorPlane.Spatial) (g : Direction → ℝ) :
    (∫ n, g n ∂angularMeasure e v) =
      ∫ n, angularWeight e v n * g n ∂solidAngle := by
  unfold angularMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (angularWeight_measurable e v).ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal, angularWeight_nonneg]

/-- The manuscript's exponent with the explicit weight and the solid-angle measure. -/
theorem laplaceTransform_angularLaw (e : ℝ) {a τ : ℝ} (ha : 0 < a)
    {v : UV.SectorPlane.Spatial} (hv : ‖v‖ < 1)
    (hα : 0 < (angularMeasure e v).real univ) (hτ : 0 ≤ τ) :
    laplaceTransform
      (emittedEnergyLaw (dopplerRateMeasure (angularMeasure e v) a v) (2*a/(1-‖v‖))) τ =
      ENNReal.ofReal (exp (-(∫ n, angularWeight e v n * log (1+τ*doppler v n/(2*a)) ∂solidAngle))) := by
  haveI := finite_angularMeasure e hv
  rw [laplaceTransform_dopplerLaw _ ha hv hα hτ, integral_angularMeasure]

theorem angularMeasure_mass (e : ℝ) (v : UV.SectorPlane.Spatial) :
    (angularMeasure e v).real univ = ∫ n, angularWeight e v n ∂solidAngle := by
  simpa using integral_angularMeasure e v (fun _ ↦ 1)

theorem dopplerRateMeasure_mass (ρ : Measure Direction) (a : ℝ) (v : UV.SectorPlane.Spatial) :
    (dopplerRateMeasure ρ a v).real univ = ρ.real univ := by
  rw [measureReal_def, measureReal_def, dopplerRateMeasure,
    Measure.map_apply (measurable_dopplerRate a v) MeasurableSet.univ]
  simp

theorem angularMeasure_eq_zero {e : ℝ} {v : UV.SectorPlane.Spatial} (h : e = 0 ∨ v = 0) :
    angularMeasure e v = 0 := by
  rcases h with he | hv
  · simp [angularMeasure, angularWeight, he]
  · simp [angularMeasure, angularWeight, hv]

/-- The full weighted edge law, including its angular coefficient. -/
theorem angularLaw_density_edge (e : ℝ) {a : ℝ} (ha : 0 < a)
    {v : UV.SectorPlane.Spatial} (hv : ‖v‖ < 1)
    (hα : 0 < ∫ n, angularWeight e v n ∂solidAngle) :
    let α := ∫ n, angularWeight e v n ∂solidAngle
    let ν := dopplerRateMeasure (angularMeasure e v) a v
    let B := 2*a/(1-‖v‖)
    let C := (2*a)^α * exp (-(∫ n, angularWeight e v n * log (doppler v n) ∂solidAngle))
    let f := gammaPoissonDensity (residual ν B) α B
    emittedEnergyLaw ν B = volume.withDensity f ∧
      (fun x ↦ (f x).toReal) ~[𝓝[>] (0 : ℝ)] fun x ↦ C/Gamma α * x^(α-1) := by
  intro α ν B C f
  haveI := finite_angularMeasure e hv
  haveI : IsFiniteMeasure ν := Measure.isFiniteMeasure_map _ _
  have hmass : ν.real univ = α := (dopplerRateMeasure_mass _ a v).trans (angularMeasure_mass e v)
  have hlow : 0 < 2*a/(1+‖v‖) := by positivity
  have hhigh : 2*a/(1+‖v‖) ≤ B :=
    div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr hv) (by linarith [norm_nonneg v])
  have hα' : 0 < ν.real univ := hmass.symm ▸ hα
  have hd := emittedEnergyLaw_density_edge ν hlow hhigh (dopplerRate_bounds ha hv) hα'
  have hC := doppler_edgeCoefficient (angularMeasure e v) ha hv
  dsimp only at hC hd
  rw [angularMeasure_mass, integral_angularMeasure] at hC
  rw [hmass] at hd
  refine ⟨hd.1, ?_⟩
  have heq (x : ℝ) :
      exp (-(residualMeasure ν B).real univ) * (B^α/Gamma α) * x^(α-1) =
        C/Gamma α * x^(α-1) := by
    rw [← mul_div_assoc]
    have hC' : exp (-(residualMeasure ν B).real univ) * B^α = C := hC
    rw [hC']
  simpa only [heq] using hd.2

end UV.ContinueRigidLaw
