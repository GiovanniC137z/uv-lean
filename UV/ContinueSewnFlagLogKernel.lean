import UV.RevisionJointHeatSelector

/-! The logarithmic residual loop kernel uses the full positive heat
axis. The ENNReal integral records the divergence at coincident points. -/

noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace UV.SewnFlags

open UV.RevisionJointHeat

def logKernel (μ x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((4*π)^2)⁻¹) * ∫⁻ t in Ioi (0:ℝ),
    ENNReal.ofReal (selectorDensity (μ^2) (x^2/4) 0 t)

private theorem logKernel_density_nonneg (μ x : ℝ) :
    0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] selectorDensity (μ^2) (x^2/4) 0 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  unfold selectorDensity
  exact mul_nonneg (rpow_nonneg ht.le _) (exp_pos _).le

theorem logKernel_proper_time (μ x : ℝ) :
    logKernel μ x = ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (exp (-(μ^2*t+x^2/(4*t)))/((4*π)^2*t)) := by
  unfold logKernel
  rw [← lintegral_const_mul _ (by unfold selectorDensity; fun_prop)]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  rw [← ENNReal.ofReal_mul (by positivity)]
  unfold selectorDensity
  rw [zero_sub,rpow_neg_one]
  congr 1
  rw [show x^2/4/t = x^2/(4*t) by rw [div_div],div_eq_mul_inv,mul_inv]
  ring

/-- The exact Fourier-normalized proper-time kernel is the actual
Schläfli Bessel function away from zero displacement. -/
theorem logKernel_bessel {μ x : ℝ} (hμ : 0 < μ) (hx : 0 < x) :
    logKernel μ x = ENNReal.ofReal (modifiedBesselK 0 (μ*x)/(8*π^2)) := by
  have hA : 0 < μ^2 := sq_pos_of_pos hμ
  have hB : 0 < x^2/4 := by positivity
  have hb : 2*sqrt (μ^2*(x^2/4)) = μ*x := by
    rw [sqrt_mul (sq_nonneg _),sqrt_sq hμ.le,sqrt_div (sq_nonneg _),sqrt_sq hx.le,
      show sqrt (4 : ℝ) = 2 by norm_num]
    ring
  unfold logKernel
  rw [← ofReal_integral_eq_lintegral_ofReal (selectorDensity_integrable hA hB 0) (logKernel_density_nonneg μ x),
    ← selectorZ, selectorZ_bessel hA hB, hb, zero_div, rpow_zero,mul_one,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp [pi_pos.ne']
  ring

theorem logKernel_zero {μ : ℝ} (hμ : 0 < μ) : logKernel μ 0 = ⊤ := by
  have hA : 0 < μ^2 := sq_pos_of_pos hμ
  have hm : Measurable (selectorDensity (μ^2) 0 0) := by unfold selectorDensity; fun_prop
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] selectorDensity (μ^2) 0 0 := by
    simpa using logKernel_density_nonneg μ 0
  have hdiv : (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (selectorDensity (μ^2) 0 0 t)) = ⊤ := by
    by_contra h
    exact (lt_irrefl (0:ℝ)) ((selectorDensity_zero_integrable_iff hA).1
      ((lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable hn).1 h))
  unfold logKernel
  rw [zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_div,hdiv,
    ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))]

end UV.SewnFlags
