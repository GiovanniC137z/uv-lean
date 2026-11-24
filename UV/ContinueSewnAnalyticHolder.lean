import UV.ContinueSewnAnalyticMoments

/-! The loss of exponent when passing from chart volume to the complete
weighted paired measure is precisely the conjugate-exponent Hölder bound. -/

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal
namespace UV.SewnFlags

/-- A volume sublevel power `b` gives the weighted power `b/q`, where `q`
is conjugate to the density exponent `p>1`. -/
theorem weighted_sublevel_holder {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [SFinite μ] (f : X → ℝ) {C : ℝ≥0∞} {b p : ℝ} (hp : 1 < p)
    (w : X → ℂ) (hw : MemLp w (ENNReal.ofReal p) μ)
    (hsub : ∀ r : ℝ, 0 < r → r ≤ 1 → μ {x | |f x| < r} ≤ C*ENNReal.ofReal (r^b))
    {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    μ.withDensity (fun x => ‖w x‖ₑ) {x | |f x| < r} ≤
      (eLpNorm w (ENNReal.ofReal p) μ * C^(1/Real.conjExponent p)) *
        ENNReal.ofReal (r^(b/Real.conjExponent p)) := by
  let S := {x | |f x| < r}
  let q := Real.conjExponent p
  have hconj : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hp₀ := hconj.pos
  have hq₀ := hconj.symm.pos
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict S) hconj
    (f := fun x => ‖w x‖ₑ) (g := fun _ => 1)
    hw.aestronglyMeasurable.aemeasurable.enorm.restrict aemeasurable_const
  simp only [Pi.mul_apply,mul_one, ENNReal.one_rpow, lintegral_one, Measure.restrict_apply_univ] at hH
  rw [withDensity_apply',eLpNorm_eq_lintegral_rpow_enorm (ENNReal.ofReal_ne_zero_iff.mpr hp₀)
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp₀.le]
  calc
    _ ≤ _ := hH
    _ ≤ (∫⁻ x, ‖w x‖ₑ^p ∂μ)^(1/p) * (C*ENNReal.ofReal (r^b))^(1/q) := by
      apply mul_le_mul'
      · exact ENNReal.rpow_le_rpow (setLIntegral_le_lintegral S _) (by positivity)
      · exact ENNReal.rpow_le_rpow (hsub r hr hr₁) (by positivity)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1/q),
        ENNReal.ofReal_rpow_of_pos (rpow_pos_of_pos hr b), ← Real.rpow_mul hr.le,
        mul_one_div, mul_assoc]

end UV.SewnFlags
