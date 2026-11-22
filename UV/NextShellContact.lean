import UV.NextSameSideShell
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Local absolute tests for a completed opposite-side shell numerator.
These bounds use the invariant normal coordinate, with the test density
included in the numerator. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped Topology

theorem opposite_shell_linear_test {h : ℝ} (f : ℝ → ℝ) :
    (∫ D, oppositeShellKernel h D * (D * f D)) = ∫ D, polePV h D * f D := by
  apply integral_congr_ae
  exact Eventually.of_forall fun D => by unfold oppositeShellKernel polePV; ring

theorem opposite_shell_linear_limit {f : ℝ → ℝ} {L : NNReal}
    (hf : LipschitzWith L f) (hi : Integrable f) :
    Tendsto (fun h : ℝ => ∫ D, oppositeShellKernel h D * (D * f D))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ D in Ioi (0 : ℝ), symmetricTest f D)) := by
  simpa only [opposite_shell_linear_test] using pole_pv_test_limit hf hi

/-- A quadratic zero removes the singular absolute factor. -/
theorem opposite_shell_quadratic_limit {f : ℝ → ℝ} (hf : Integrable f) :
    Tendsto (fun h : ℝ => ∫ D, oppositeShellKernel h D * (D ^ 2 * f D))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ D, f D)) := by
  refine tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (fun D => ‖f D‖) ?_ ?_ hf.norm ?_
  · exact Eventually.of_forall fun h =>
      (((measurable_id.pow_const 2).add measurable_const).inv.aestronglyMeasurable).mul
        ((measurable_id.pow_const 2).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  · refine Eventually.of_forall fun h => Eventually.of_forall fun D => ?_
    have hden : 0 ≤ D ^ 2 + h ^ 2 := by positivity
    have he : oppositeShellKernel h D * (D ^ 2 * f D) =
        D ^ 2 / (D ^ 2 + h ^ 2) * f D := by unfold oppositeShellKernel; ring
    rw [he, norm_mul, Real.norm_of_nonneg (div_nonneg (sq_nonneg _) hden)]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rcases hden.eq_or_lt with hzero | hpos
    · simp [hzero.symm]
    · exact (div_le_one hpos).mpr (le_add_of_nonneg_right (sq_nonneg _))
  · have ha : ∀ᵐ D : ℝ ∂volume, D ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [ha] with D hD
    have hc : ContinuousAt (fun h : ℝ => (D ^ 2 + h ^ 2)⁻¹ * (D ^ 2 * f D)) 0 := by
      exact (((continuous_const.add (continuous_id.pow 2)).continuousAt).inv₀
        (by simpa using (sq_pos_of_ne_zero hD).ne')).mul continuousAt_const
    have hz : (D ^ 2 + (0 : ℝ) ^ 2)⁻¹ * (D ^ 2 * f D) = f D := by
      rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, ← mul_assoc,
        inv_mul_cancel₀ (sq_pos_of_ne_zero hD).ne', one_mul]
    simpa only [oppositeShellKernel, hz] using
      hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))

/-- The scalar comparison on the positive half of a regular shell
chart has an exact logarithmic integral. -/
theorem shell_contact_log_mass {h r : ℝ} (hh : 0 < h) (hr : 0 < r) :
    (∫ D in Ioc (0 : ℝ) r, polePV h D) =
      (Real.log (r ^ 2 + h ^ 2) - Real.log (h ^ 2)) / 2 := by
  have hd (D : ℝ) : HasDerivAt (fun x : ℝ => Real.log (x ^ 2 + h ^ 2) / 2)
      (polePV h D) D := by
    have hp : HasDerivAt (fun x : ℝ => x ^ 2 + h ^ 2) (2 * D) D := by
      simpa using ((hasDerivAt_id D).pow 2).add_const (h ^ 2)
    have H := ((Real.hasDerivAt_log (by positivity : D ^ 2 + h ^ 2 ≠ 0)).comp D hp).div_const 2
    convert H using 1
    unfold polePV
    ring
  rw [← intervalIntegral.integral_of_le hr.le, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun D _ => hd D) ((Continuous.div continuous_id
      ((continuous_id.pow 2).add continuous_const) (fun D => by positivity)).intervalIntegrable _ _)]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
  ring

/-- Linear lower and upper bounds on the numerator produce matching
logarithmic comparisons, with no cancellation inside the absolute value. -/
theorem shell_contact_linear_comparison {n : ℝ → ℝ} (hn : Continuous n)
    {h r c C : ℝ} (hh : 0 < h) (hr : 0 < r)
    (hl : ∀ D ∈ Ioc (0 : ℝ) r, c * D ≤ ‖n D‖)
    (hu : ∀ D ∈ Ioc (0 : ℝ) r, ‖n D‖ ≤ C * D) :
    let M := (Real.log (r ^ 2 + h ^ 2) - Real.log (h ^ 2)) / 2
    c * M ≤ (∫ D in Ioc (0 : ℝ) r, oppositeShellKernel h D * ‖n D‖) ∧
      (∫ D in Ioc (0 : ℝ) r, oppositeShellKernel h D * ‖n D‖) ≤ C * M := by
  have hk : Continuous (oppositeShellKernel h) :=
    ((continuous_id.pow 2).add continuous_const).inv₀ (fun D => by positivity)
  have hp : Continuous (polePV h) :=
    continuous_id.div ((continuous_id.pow 2).add continuous_const) (fun D => by positivity)
  have hi : IntegrableOn (fun D => oppositeShellKernel h D * ‖n D‖) (Ioc (0 : ℝ) r) :=
    ((hk.mul hn.norm).continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hj : IntegrableOn (polePV h) (Ioc (0 : ℝ) r) :=
    (hp.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have he (a D : ℝ) : a * polePV h D = oppositeShellKernel h D * (a * D) := by
    unfold polePV oppositeShellKernel
    ring
  have hnonneg (D : ℝ) : 0 ≤ oppositeShellKernel h D := by unfold oppositeShellKernel; positivity
  have low := setIntegral_mono_on (hj.const_mul c) hi measurableSet_Ioc (fun D hD => by
    rw [he c D]
    exact mul_le_mul_of_nonneg_left (hl D hD) (hnonneg D))
  have high := setIntegral_mono_on hi (hj.const_mul C) measurableSet_Ioc (fun D hD => by
    rw [he C D]
    exact mul_le_mul_of_nonneg_left (hu D hD) (hnonneg D))
  simp only [integral_const_mul, shell_contact_log_mass hh hr] at low high
  exact ⟨low, high⟩

/-- A nonzero first normal derivative gives the two matching local
linear bounds on the absolute numerator. -/
theorem shell_contact_simple_zero {n : ℝ → ℝ} {a : ℝ}
    (hn : HasDerivAt n a 0) (hz : n 0 = 0) (ha : a ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ D ∈ Ioc (0 : ℝ) r,
      (‖a‖ / 2) * D ≤ ‖n D‖ ∧ ‖n D‖ ≤ (3 * ‖a‖ / 2) * D := by
  have H : Tendsto (fun D : ℝ => n D / D) (𝓝[>] 0) (𝓝 a) := by
    simpa [hz, div_eq_inv_mul] using hn.tendsto_slope_zero_right
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hclose : ∀ᶠ D in 𝓝[>] (0 : ℝ), ‖n D / D - a‖ < ‖a‖ / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using H (Metric.ball_mem_nhds a (half_pos ha'))
  rw [eventually_nhdsWithin_iff] at hclose
  obtain ⟨r₀, hr₀, hball⟩ := Metric.eventually_nhds_iff_ball.mp hclose
  refine ⟨r₀ / 2, half_pos hr₀, fun D hD => ?_⟩
  have hp : 0 < D := hD.1
  have hmem : D ∈ Metric.ball (0 : ℝ) r₀ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hp]
    linarith [hD.2]
  have hd := hball D hmem hp
  have hl := norm_sub_norm_le a (n D / D)
  have hu := norm_sub_norm_le (n D / D) a
  rw [norm_sub_rev] at hl
  rw [norm_div, Real.norm_of_nonneg hp.le] at hl hu
  exact ⟨(le_div_iff₀ hp).mp (by linarith), (div_le_iff₀ hp).mp (by linarith)⟩

/-- A quadratic zero bounds the absolute integral on the whole finite
chart independently of the common positive height. -/
theorem shell_contact_double_zero_bound {n : ℝ → ℝ} (hn : Continuous n)
    {h r C : ℝ} (hh : 0 < h) (hr : 0 < r)
    (hn₂ : ∀ D ∈ Icc (-r) r, ‖n D‖ ≤ C * D ^ 2) :
    (∫ D in Icc (-r) r, oppositeShellKernel h D * ‖n D‖) ≤ (2 * r) * C := by
  have hk : Continuous (oppositeShellKernel h) :=
    ((continuous_id.pow 2).add continuous_const).inv₀ (fun D => by positivity)
  have hi := (hk.mul hn.norm).continuousOn.integrableOn_compact (μ := volume)
    (isCompact_Icc (a := -r) (b := r))
  have hC : 0 ≤ C := by
    have h := (norm_nonneg (n r)).trans (hn₂ r ⟨by linarith, le_rfl⟩)
    exact nonneg_of_mul_nonneg_left h (sq_pos_of_pos hr)
  have hum := setIntegral_mono_on hi
    (continuous_const.continuousOn.integrableOn_compact isCompact_Icc) measurableSet_Icc
    (fun D hD => by
      have hp : 0 < D ^ 2 + h ^ 2 := by positivity
      have he : oppositeShellKernel h D * (C * D ^ 2) = C * (D ^ 2 / (D ^ 2 + h ^ 2)) := by
        unfold oppositeShellKernel; ring
      calc
        _ ≤ oppositeShellKernel h D * (C * D ^ 2) :=
          mul_le_mul_of_nonneg_left (hn₂ D hD) (by unfold oppositeShellKernel; positivity)
        _ = C * (D ^ 2 / (D ^ 2 + h ^ 2)) := he
        _ ≤ C := mul_le_of_le_one_right hC
          ((div_le_one hp).mpr (le_add_of_nonneg_right (sq_nonneg _))))
  simpa [integral_const, Real.volume_real_Icc, sub_neg_eq_add, two_mul,
    max_eq_left (by positivity : 0 ≤ r + r)] using hum

end UV.SectorPlane
