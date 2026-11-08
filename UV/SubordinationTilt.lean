import UV.KernelMeasure

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal

namespace UV

/-- A convenient single-exponential form of the literal manuscript density. -/
theorem oqedDensity_as_exp (μ τ : ℝ) :
    oqedDensity μ τ =
      (τ ^ (-(3 : ℝ) / 2) / (2 * Real.sqrt Real.pi)) *
        Real.exp (μ - μ ^ 2 * τ - 1 / (4 * τ)) := by
  unfold oqedDensity oqedDensityCore
  calc
    _ = (τ ^ (-(3 : ℝ) / 2) / (2 * Real.sqrt Real.pi)) *
        (Real.exp μ * Real.exp (-(μ ^ 2 * τ) - 1 / (4 * τ))) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      congr 1
      ring

/-- A Laplace tilt changes the tempering parameter to the square root of the
shifted squared mass. This is a pointwise density identity. -/
theorem oqedDensity_laplace_tilt (μ z τ : ℝ) (hz : 0 ≤ μ ^ 2 + z) :
    Real.exp (-z * τ) * oqedDensity μ τ =
      Real.exp (μ - Real.sqrt (μ ^ 2 + z)) *
        oqedDensity (Real.sqrt (μ ^ 2 + z)) τ := by
  rw [oqedDensity_as_exp, oqedDensity_as_exp]
  calc
    _ = (τ ^ (-(3 : ℝ) / 2) / (2 * Real.sqrt Real.pi)) *
        Real.exp ((-z * τ) + (μ - μ ^ 2 * τ - 1 / (4 * τ))) := by
      rw [Real.exp_add]
      ring
    _ = (τ ^ (-(3 : ℝ) / 2) / (2 * Real.sqrt Real.pi)) *
        Real.exp ((μ - Real.sqrt (μ ^ 2 + z)) +
          (Real.sqrt (μ ^ 2 + z) - Real.sqrt (μ ^ 2 + z) ^ 2 * τ - 1 / (4 * τ))) := by
      rw [Real.sq_sqrt hz]
      congr 1
      congr 1
      ring
    _ = _ := by
      rw [Real.exp_add]
      ring

/-- The pointwise Laplace tilt induces an exact equality of measures, with no
normalization premise. -/
theorem oqedMeasure_laplace_tilt (μ z : ℝ) (hz : 0 ≤ μ ^ 2 + z) :
    (oqedMeasure μ).withDensity (fun τ => ENNReal.ofReal (Real.exp (-z * τ))) =
      ENNReal.ofReal (Real.exp (μ - Real.sqrt (μ ^ 2 + z))) •
        oqedMeasure (Real.sqrt (μ ^ 2 + z)) := by
  have hd : Measurable (fun τ : ℝ => ENNReal.ofReal (oqedDensity μ τ)) :=
    (oqedDensity_measurable μ).ennreal_ofReal
  have he : Measurable (fun τ : ℝ => ENNReal.ofReal (Real.exp (-z * τ))) := by
    fun_prop
  unfold oqedMeasure
  rw [← withDensity_mul _ hd he,
    ← withDensity_smul _ (oqedDensity_measurable (Real.sqrt (μ ^ 2 + z))).ennreal_ofReal]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  change ENNReal.ofReal (oqedDensity μ τ) * ENNReal.ofReal (Real.exp (-z * τ)) =
    ENNReal.ofReal (Real.exp (μ - Real.sqrt (μ ^ 2 + z))) *
      ENNReal.ofReal (oqedDensity (Real.sqrt (μ ^ 2 + z)) τ)
  rw [← ENNReal.ofReal_mul (oqedDensity_nonneg μ τ hτ.le),
    ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  congr 1
  rw [mul_comm, oqedDensity_laplace_tilt μ z τ hz]

/-- The nonnegative Laplace transform is exactly the total mass of the tilted
measure, and hence reduces to the new tempering parameter's total mass. -/
theorem oqedMeasure_laplace_tilt_mass (μ z : ℝ) (hz : 0 ≤ μ ^ 2 + z) :
    (∫⁻ τ : ℝ, ENNReal.ofReal (Real.exp (-z * τ)) ∂oqedMeasure μ) =
      ENNReal.ofReal (Real.exp (μ - Real.sqrt (μ ^ 2 + z))) *
        oqedMeasure (Real.sqrt (μ ^ 2 + z)) univ := by
  have hh := congrArg (fun ρ : Measure ℝ => ρ univ) (oqedMeasure_laplace_tilt μ z hz)
  dsimp only at hh
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    Measure.smul_apply] at hh
  simpa only [smul_eq_mul] using hh

theorem oqedLaplace_integrable (μ z : ℝ) (hz : 0 ≤ μ ^ 2 + z) :
    Integrable (fun τ : ℝ => Real.exp (-z * τ)) (oqedMeasure μ) := by
  refine ⟨by fun_prop, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
    (fun τ : ℝ => Real.exp_nonneg (-z * τ)))).mpr
  exact oqedExponentialMoment_finite μ (b := -z) (by linarith)

/-- The Bochner Laplace transform reduces to the total mass at the shifted
parameter. General normalization can therefore be used directly afterwards. -/
theorem oqedLaplace_eq_tilted_mass (μ z : ℝ) (hz : 0 ≤ μ ^ 2 + z) :
    laplace (oqedMeasure μ) z =
      Real.exp (μ - Real.sqrt (μ ^ 2 + z)) *
        (oqedMeasure (Real.sqrt (μ ^ 2 + z)) univ).toReal := by
  unfold laplace
  have hfun : (fun τ : ℝ => Real.exp (-τ * z)) =
      (fun τ : ℝ => Real.exp (-z * τ)) := by
    funext τ
    congr 1
    ring
  rw [hfun, integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun τ : ℝ => Real.exp_nonneg (-z * τ)))
    (oqedLaplace_integrable μ z hz).aestronglyMeasurable,
    oqedMeasure_laplace_tilt_mass μ z hz, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_nonneg _)]

end UV
