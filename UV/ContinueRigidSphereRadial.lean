import UV.ContinueRigidSphereSupport

/-! Radial Coulomb energy and transverse spectral weights in the rigid-source calculation. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Real
open scoped ENNReal RealInnerProductSpace

namespace UV.ContinueRigidLaw

open UV.SectorPlane

/-- Spatial Coulomb integral with the manuscript's two harmonic-extension factors. -/
theorem spatial_coulombIntegral {a : ℝ} (ha : 0 < a) :
    (∫ k : Spatial, exp (-(2*a*‖k‖))/‖k‖^2) = 2*π/a := by
  have h := integral_fun_norm_addHaar (volume : Measure Spatial)
    (fun r : ℝ ↦ exp (-(2*a*r))/r^2)
  have hm : (volume : Measure Spatial).real (Metric.ball 0 1) = 4*π/3 := by
    rw [measureReal_def, EuclideanSpace.volume_ball_fin_three]
    simp only [ENNReal.ofReal_one, one_pow, one_mul,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ π*4/3)]
    ring
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, hm, nsmul_eq_mul, Nat.cast_ofNat,
    smul_eq_mul] at h
  rw [h]
  have hh : (∫ r in Ioi (0 : ℝ), r^2 * (exp (-(2*a*r))/r^2)) =
      ∫ r in Ioi (0 : ℝ), exp ((-(2*a))*r) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hp : 0 < r := hr
    change r^2 * (exp (-(2*a*r))/r^2) = exp (-(2*a)*r)
    rw [show -(2*a*r) = -(2*a)*r by ring]
    field_simp
  rw [hh, integral_exp_mul_Ioi (show -(2*a) < 0 by linarith)]
  simp only [mul_zero, exp_zero]
  field_simp
  ring

theorem coulombEnergy_eq (e : ℝ) {a : ℝ} (ha : 0 < a) :
    (e^2/(2*(2*π)^3)) * (∫ k : Spatial, exp (-(2*a*‖k‖))/‖k‖^2) = e^2/(8*π^2*a) := by
  rw [spatial_coulombIntegral ha]
  field_simp [pi_ne_zero]
  ring

/-- The scalar quadratic form of the neutral transverse magnetic weight. -/
def neutralMagneticWeight (r : ℝ) (n : Direction) (q : Spatial) : ℝ :=
  (r/2) * (‖q‖^2 - ⟪q, (n : Spatial)⟫^2)

theorem neutralMagneticWeight_nonneg {r : ℝ} (hr : 0 ≤ r) (n : Direction) (q : Spatial) :
    0 ≤ neutralMagneticWeight r n q := by
  have h := abs_real_inner_le_norm q (n : Spatial)
  rw [n.property, mul_one] at h
  have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs] at hs
  exact mul_nonneg (by positivity) (sub_nonneg.mpr hs)

theorem neutralMagneticWeight_pos {r : ℝ} (hr : 0 < r) (n : Direction) {q : Spatial}
    (hq : q ≠ 0) (hperp : ⟪q, (n : Spatial)⟫ = 0) :
    0 < neutralMagneticWeight r n q := by
  have hn := norm_pos_iff.mpr hq
  rw [neutralMagneticWeight, hperp, zero_pow (by decide : 2 ≠ 0), sub_zero]
  positivity

/-- The neutral transversely polarized covariance has its stated positive moving-frame atom. -/
theorem neutralPhoton_atom {r : ℝ} (hr : 0 < r) (n : Direction) {v q : Spatial}
    (hv : ‖v‖ < 1) (hq : q ≠ 0) (hperp : ⟪q, (n : Spatial)⟫ = 0) (τ : ℝ) :
    let ω := r*doppler v n
    let c := neutralMagneticWeight r n q
    let μ := ENNReal.ofReal c • Measure.dirac ω
    0 < ω ∧ 0 < μ {ω} ∧ laplaceTransform μ τ = ENNReal.ofReal (c * exp (-(τ*ω))) := by
  intro ω c μ
  have hω : 0 < ω := mul_pos hr ((sub_pos.mpr hv).trans_le (doppler_bounds v n).1)
  have hc : 0 < c := neutralMagneticWeight_pos hr n hq hperp
  constructor
  · exact hω
  constructor
  · change 0 < (ENNReal.ofReal c • Measure.dirac ω) {ω}
    simpa [Measure.smul_apply] using (ENNReal.ofReal_pos.mpr hc)
  · change (∫⁻ y, laplaceTest τ y ∂(ENNReal.ofReal c • Measure.dirac ω)) = _
    rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul, laplaceTest,
      ← ENNReal.ofReal_mul hc.le]

end UV.ContinueRigidLaw
