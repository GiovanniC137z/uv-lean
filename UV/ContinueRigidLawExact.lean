import UV.ContinueRigidLawPoisson
import UV.ContinuationSectorPlane

/-! Exact angular Laplace law on the reconstructed sector-plane.
The angular measure is the given positive weight of the unit directions on that
plane. The theorem identifies the scalar law once its vacuum Laplace exponent
has been obtained from the Hamiltonian. -/

noncomputable section

open MeasureTheory Set Real Filter ProbabilityTheory
open scoped ENNReal MeasureTheory RealInnerProductSpace

namespace UV.ContinueRigidLaw

private theorem residualTilt_nonneg {ν : Measure ℝ} {b₀ B τ : ℝ}
    (hb₀ : 0 < b₀) (hν : ∀ᵐ b ∂ν, b₀ ≤ b ∧ b ≤ B) (hτ : 0 ≤ τ) :
    ∀ᵐ b ∂ν, 0 ≤ log ((B+τ)/(b+τ)) := by
  filter_upwards [hν] with b hb
  exact log_nonneg ((le_div_iff₀ (by linarith [hb.1])).mpr (by linarith [hb.2]))

private theorem residualTilt_integrable (ν : Measure ℝ) [IsFiniteMeasure ν] {b₀ B τ : ℝ}
    (hb₀ : 0 < b₀) (hB : b₀ ≤ B) (hν : ∀ᵐ b ∂ν, b₀ ≤ b ∧ b ≤ B) (hτ : 0 ≤ τ) :
    Integrable (fun b ↦ log ((B+τ)/(b+τ))) ν := by
  refine (integrable_const (log ((B+τ)/(b₀+τ)))).mono' (measurable_log.comp (by fun_prop)).aestronglyMeasurable ?_
  filter_upwards [hν, residualTilt_nonneg hb₀ hν hτ] with b hb hbn
  rw [Real.norm_eq_abs, abs_of_nonneg hbn]
  exact log_le_log (div_pos (by linarith) (by linarith [hb.1]))
    (div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith [hb.1]))

theorem laplaceTransform_residual (ν : Measure ℝ) [IsFiniteMeasure ν] {b₀ B τ : ℝ}
    (hb₀ : 0 < b₀) (hB : b₀ ≤ B) (hν : ∀ᵐ b ∂ν, b₀ ≤ b ∧ b ≤ B) (hτ : 0 ≤ τ) :
    (laplaceTransform (residualMeasure ν B) τ).toReal = ∫ b, log ((B+τ)/(b+τ)) ∂ν := by
  unfold laplaceTransform
  rw [tilted_residualMeasure ν (hν.mono fun _ hb ↦ ⟨hb₀.trans_le hb.1, hb.2⟩) hτ,
    ← ofReal_integral_eq_lintegral_ofReal (residualTilt_integrable ν hb₀ hB hν hτ)
      (residualTilt_nonneg hb₀ hν hτ), ENNReal.toReal_ofReal]
  exact integral_nonneg_of_ae (residualTilt_nonneg hb₀ hν hτ)

private theorem log_difference {b B τ : ℝ} (hb : 0 < b) (hB : 0 < B) (hτ : 0 ≤ τ) :
    log (B/(B+τ)) + log ((B+τ)/(b+τ)) - log (B/b) = -log (1+τ/b) := by
  have hbt : 0 < b+τ := by linarith
  have hBt : 0 < B+τ := by linarith
  rw [show 1+τ/b = (b+τ)/b by rw [add_div, div_self hb.ne']]
  rw [log_div hB.ne' hBt.ne', log_div hBt.ne' hbt.ne', log_div hB.ne' hb.ne',
    log_div hbt.ne' hb.ne']
  ring

theorem residualMeasure_nonneg (ν : Measure ℝ) (B : ℝ) :
    ∀ᵐ y ∂residualMeasure ν B, 0 ≤ y := by
  rw [ae_iff]
  simp only [not_le]
  exact measure_mono_null Iio_subset_Iic_self (residualMeasure_below ν B)

theorem probability_emittedEnergyLaw (ν : Measure ℝ) [IsFiniteMeasure ν] {b₀ B : ℝ}
    (hb₀ : 0 < b₀) (hB : b₀ ≤ B) (hν : ∀ᵐ b ∂ν, b₀ ≤ b ∧ b ≤ B)
    (hα : 0 < ν.real univ) : IsProbabilityMeasure (emittedEnergyLaw ν B) := by
  haveI := finite_residualMeasure ν hb₀ hB hν
  haveI := probability_compoundPoisson _ (residualMeasure_nonneg ν B)
  haveI := isProbabilityMeasure_gammaMeasure hα (hb₀.trans_le hB)
  unfold emittedEnergyLaw
  infer_instance

theorem laplaceTransform_emittedEnergyLaw (ν : Measure ℝ) [IsFiniteMeasure ν] {b₀ B τ : ℝ}
    (hb₀ : 0 < b₀) (hB : b₀ ≤ B) (hν : ∀ᵐ b ∂ν, b₀ ≤ b ∧ b ≤ B)
    (hα : 0 < ν.real univ) (hτ : 0 ≤ τ) :
    laplaceTransform (emittedEnergyLaw ν B) τ =
      ENNReal.ofReal (exp (-(∫ b, log (1+τ/b) ∂ν))) := by
  have hBpos := hb₀.trans_le hB
  have hBt : 0 < B+τ := by linarith
  haveI := finite_residualMeasure ν hb₀ hB hν
  have hη := residualMeasure_nonneg ν B
  haveI := probability_compoundPoisson _ hη
  have hM : (residualMeasure ν B).real univ = ∫ b, log (B/b) ∂ν := by
    simpa only [laplaceTransform_zero, measureReal_def, add_zero] using
      laplaceTransform_residual ν hb₀ hB hν le_rfl
  rw [emittedEnergyLaw, laplaceTransform_conv, laplaceTransform_gamma hα hBpos hτ,
    laplaceTransform_compoundPoisson _ hη hτ, laplaceTransform_residual ν hb₀ hB hν hτ,
    hM, rpow_def_of_pos (div_pos hBpos hBt), ← ENNReal.ofReal_mul (exp_pos _).le,
    ← exp_add]
  congr 2
  have hi := residualTilt_integrable ν hb₀ hB hν hτ
  have hi₀ : Integrable (fun b ↦ log (B/b)) ν := by
    simpa only [add_zero] using residualTilt_integrable ν hb₀ hB hν le_rfl
  calc
    _ = ∫ b, (log (B/(B+τ)) + log ((B+τ)/(b+τ)) - log (B/b)) ∂ν := by
      have hi₁ : Integrable (fun b ↦ log (B/(B+τ)) + log ((B+τ)/(b+τ))) ν :=
        (integrable_const _).add hi
      rw [integral_sub hi₁ hi₀, integral_add (integrable_const _) hi,
        integral_const, smul_eq_mul]
      ring
    _ = _ := by
      rw [← integral_neg]
      exact integral_congr_ae (hν.mono fun b hb ↦ log_difference (hb₀.trans_le hb.1) hBpos hτ)

/-- The manuscript's Doppler factor on the spatial unit sphere. -/
def doppler (v : UV.SectorPlane.Spatial)
    (n : UV.SectorPlane.UnitVector UV.SectorPlane.Spatial) : ℝ :=
  1 - ⟪v, (n : UV.SectorPlane.Spatial)⟫

theorem doppler_bounds (v : UV.SectorPlane.Spatial)
    (n : UV.SectorPlane.UnitVector UV.SectorPlane.Spatial) :
    1-‖v‖ ≤ doppler v n ∧ doppler v n ≤ 1+‖v‖ := by
  have h := abs_real_inner_le_norm v (n : UV.SectorPlane.Spatial)
  rw [n.property, mul_one, abs_le] at h
  constructor <;> unfold doppler <;> linarith [h.1, h.2]

/-- Pushforward of the positive angular weight by the Doppler rate on one plane. -/
def dopplerRateMeasure (ρ : Measure (UV.SectorPlane.UnitVector UV.SectorPlane.Spatial))
    (a : ℝ) (v : UV.SectorPlane.Spatial) : Measure ℝ :=
  ρ.map (fun n ↦ 2*a/doppler v n)

theorem measurable_dopplerRate (a : ℝ) (v : UV.SectorPlane.Spatial) :
    Measurable (fun n : UV.SectorPlane.UnitVector UV.SectorPlane.Spatial ↦ 2*a/doppler v n) := by
  unfold doppler
  exact measurable_const.div (measurable_const.sub
    ((continuous_const.inner continuous_id).measurable.comp measurable_subtype_coe))

theorem dopplerRate_bounds {ρ : Measure (UV.SectorPlane.UnitVector UV.SectorPlane.Spatial)}
    {a : ℝ} (ha : 0 < a) {v : UV.SectorPlane.Spatial}
    (hv : ‖v‖ < 1) :
    ∀ᵐ b ∂dopplerRateMeasure ρ a v, 2*a/(1+‖v‖) ≤ b ∧ b ≤ 2*a/(1-‖v‖) := by
  unfold dopplerRateMeasure
  refine (ae_map_iff (measurable_dopplerRate a v).aemeasurable measurableSet_Icc).2 ?_
  apply ae_of_all
  intro n
  obtain ⟨hlo,hhi⟩ := doppler_bounds v n
  have hd : 0 < doppler v n := (sub_pos.mpr hv).trans_le hlo
  exact ⟨div_le_div_of_nonneg_left (by positivity) hd hhi,
    div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr hv) hlo⟩

/-- The exact scalar Laplace transform of the charged probe, in angular variables. -/
theorem laplaceTransform_dopplerLaw
    (ρ : Measure (UV.SectorPlane.UnitVector UV.SectorPlane.Spatial)) [IsFiniteMeasure ρ]
    {a τ : ℝ} (ha : 0 < a) {v : UV.SectorPlane.Spatial} (hv : ‖v‖ < 1)
    (hα : 0 < ρ.real univ) (hτ : 0 ≤ τ) :
    laplaceTransform (emittedEnergyLaw (dopplerRateMeasure ρ a v) (2*a/(1-‖v‖))) τ =
      ENNReal.ofReal (exp (-(∫ n, log (1+τ*doppler v n/(2*a)) ∂ρ))) := by
  haveI : IsFiniteMeasure (dopplerRateMeasure ρ a v) := Measure.isFiniteMeasure_map _ _
  have hm := measurable_dopplerRate a v
  have hmass : (dopplerRateMeasure ρ a v).real univ = ρ.real univ := by
    rw [measureReal_def, measureReal_def, dopplerRateMeasure, Measure.map_apply hm MeasurableSet.univ]
    simp
  have hlow : 0 < 2*a/(1+‖v‖) := by positivity
  have hhigh : 2*a/(1+‖v‖) ≤ 2*a/(1-‖v‖) :=
    div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr hv) (by linarith [norm_nonneg v])
  have hα' : 0 < (dopplerRateMeasure ρ a v).real univ := hmass.symm ▸ hα
  rw [laplaceTransform_emittedEnergyLaw _ hlow hhigh (dopplerRate_bounds ha hv) hα' hτ]
  congr 3
  unfold dopplerRateMeasure
  have hm' : Measurable (fun b : ℝ ↦ log (1+τ/b)) := measurable_log.comp (by fun_prop)
  rw [integral_map hm.aemeasurable hm'.aestronglyMeasurable]
  apply integral_congr_ae
  apply ae_of_all
  intro n
  change log (1+τ/(2*a/doppler v n)) = log (1+τ*doppler v n/(2*a))
  rw [div_div_eq_mul_div]

/-- The one-rate mass at zero tilt gives the exact angular edge coefficient. -/
theorem doppler_edgeCoefficient
    (ρ : Measure (UV.SectorPlane.UnitVector UV.SectorPlane.Spatial)) [IsFiniteMeasure ρ]
    {a : ℝ} (ha : 0 < a) {v : UV.SectorPlane.Spatial} (hv : ‖v‖ < 1) :
    let α := ρ.real univ
    let B := 2*a/(1-‖v‖)
    let M := (residualMeasure (dopplerRateMeasure ρ a v) B).real univ
    exp (-M)*B^α = (2*a)^α * exp (-(∫ n, log (doppler v n) ∂ρ)) := by
  intro α B M
  have ha₂ : 0 < 2*a := by positivity
  have hB : 0 < B := div_pos ha₂ (sub_pos.mpr hv)
  have hm := measurable_dopplerRate a v
  haveI : IsFiniteMeasure (dopplerRateMeasure ρ a v) := Measure.isFiniteMeasure_map _ _
  have hlow : 0 < 2*a/(1+‖v‖) := by positivity
  have hhi : 2*a/(1+‖v‖) ≤ B :=
    div_le_div_of_nonneg_left ha₂.le (sub_pos.mpr hv) (by linarith [norm_nonneg v])
  have hν := dopplerRate_bounds (ρ := ρ) ha hv
  have hmeas : Measurable (fun b : ℝ ↦ log (B/b)) := measurable_log.comp (by fun_prop)
  have hM : M = ∫ n, log (B / (2*a/doppler v n)) ∂ρ := by
    have hh := laplaceTransform_residual _ hlow hhi hν le_rfl
    simp only [laplaceTransform_zero, add_zero] at hh
    change M = _ at hh
    rw [hh, dopplerRateMeasure, integral_map hm.aemeasurable hmeas.aestronglyMeasurable]
  have hpoint (n : UV.SectorPlane.UnitVector UV.SectorPlane.Spatial) :
      log (B / (2*a/doppler v n)) = (log B-log (2*a)) + log (doppler v n) := by
    have hd := (sub_pos.mpr hv).trans_le (doppler_bounds v n).1
    rw [log_div hB.ne' (div_pos ha₂ hd).ne', log_div ha₂.ne' hd.ne']
    ring
  have hi : Integrable (fun n ↦ log (B / (2*a/doppler v n))) ρ := by
    have hi' : Integrable (fun b : ℝ ↦ log (B/b)) (dopplerRateMeasure ρ a v) := by
      simpa only [add_zero] using residualTilt_integrable _ hlow hhi hν le_rfl
    exact (integrable_map_measure hmeas.aestronglyMeasurable hm.aemeasurable).1 hi'
  have hi' : Integrable (fun n ↦ log (doppler v n)) ρ := by
    refine (hi.sub (integrable_const (log B-log (2*a)))).congr (ae_of_all _ ?_)
    intro n
    change log (B / (2*a/doppler v n)) - (log B-log (2*a)) = _
    rw [hpoint]
    ring
  rw [hM, integral_congr_ae (ae_of_all _ hpoint), integral_add (integrable_const _) hi',
    integral_const, smul_eq_mul, rpow_def_of_pos hB, rpow_def_of_pos ha₂, ← exp_add, ← exp_add]
  congr 1
  change -(ρ.real univ * (log B-log (2*a)) + _) + log B*ρ.real univ =
    log (2*a)*ρ.real univ + -_
  ring

end UV.ContinueRigidLaw
