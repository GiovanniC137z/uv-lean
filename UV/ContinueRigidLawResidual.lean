import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.WithDensity

/-! The positive residual in the rigid-source emitted-energy law.
The finite measure on rates is the pushforward of the angular weight
(w(\mathbf n)\,d\Omega) under the Doppler-rate map on the reconstructed plane. -/

noncomputable section

open MeasureTheory Set Real Filter
open scoped ENNReal Interval

namespace UV.ContinueRigidLaw

/-- The nonnegative integral representation of the one-rate residual density. -/
def rateResidual (B b y : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Ioc b B, ENNReal.ofReal (exp (-(r * y)))

theorem measurable_rateResidual (B : ℝ) :
    Measurable (fun p : ℝ × ℝ ↦ rateResidual B p.1 p.2) := by
  have hm : Measurable (fun p : (ℝ × ℝ) × ℝ ↦
      if p.1.1 < p.2 ∧ p.2 ≤ B then ENNReal.ofReal (exp (-(p.2 * p.1.2))) else 0) := by
    refine Measurable.ite ?_ (by fun_prop) measurable_const
    change MeasurableSet {p : (ℝ × ℝ) × ℝ | p.1.1 < p.2 ∧ p.2 ≤ B}
    exact (measurableSet_lt (measurable_fst.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  convert hm.lintegral_prod_right' (ν := volume) using 1
  ext p
  rw [rateResidual, ← lintegral_indicator measurableSet_Ioc]
  simp [indicator]

theorem rateResidual_eq {B b y : ℝ} (hbB : b ≤ B) (hy : 0 < y) :
    rateResidual B b y = ENNReal.ofReal ((exp (-(b*y)) - exp (-(B*y))) / y) := by
  have hc : Continuous (fun r : ℝ ↦ exp (-(r * y))) := by fun_prop
  have hi := hc.intervalIntegrable (μ := volume) b B
  rw [rateResidual, ← ofReal_integral_eq_lintegral_ofReal hi.1
    (ae_of_all _ fun _ ↦ (exp_pos _).le), ← intervalIntegral.integral_of_le hbB]
  congr 1
  have he : ∀ r : ℝ, exp (-(r * y)) = exp ((-y) * r) := fun r ↦ by ring_nf
  simp_rw [he]
  rw [intervalIntegral.integral_comp_mul_left (f := exp) (neg_ne_zero.mpr hy.ne'),
    integral_exp]
  simp only [smul_eq_mul, inv_neg, div_eq_mul_inv]
  ring

theorem rateResidual_le {B b y : ℝ} (hb : 0 ≤ b) (hy : 0 ≤ y) :
    rateResidual B b y ≤ ENNReal.ofReal (B-b) := by
  rw [rateResidual]
  calc
    _ ≤ ∫⁻ _ in Ioc b B, (1 : ℝ≥0∞) := by
      refine setLIntegral_mono' measurableSet_Ioc ?_
      intro r hr
      simpa using (exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (hb.trans hr.1.le) hy)))
    _ = _ := by simp

/-- Positive residual density in emitted energy, extended by zero at and below zero. -/
def residual (ν : Measure ℝ) (B y : ℝ) : ℝ≥0∞ :=
  (Ioi (0 : ℝ)).indicator (fun y ↦ ∫⁻ b, rateResidual B b y ∂ν) y

theorem measurable_residual (ν : Measure ℝ) [SFinite ν] (B : ℝ) :
    Measurable (residual ν B) := by
  apply Measurable.indicator _ measurableSet_Ioi
  exact ((measurable_rateResidual B).comp measurable_swap).lintegral_prod_right'

theorem residual_eq (ν : Measure ℝ) {B y : ℝ} (hy : 0 < y)
    (hν : ∀ᵐ b ∂ν, b ≤ B) :
    residual ν B y = ∫⁻ b, ENNReal.ofReal ((exp (-(b*y)) - exp (-(B*y))) / y) ∂ν := by
  rw [residual, indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy)]
  exact lintegral_congr_ae (hν.mono fun _ hb ↦ rateResidual_eq hb hy)

theorem residual_le (ν : Measure ℝ) {B y : ℝ} (hν : ∀ᵐ b ∂ν, 0 ≤ b) :
    residual ν B y ≤ ENNReal.ofReal B * ν univ := by
  by_cases hy : 0 < y
  · rw [residual, indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy), ← lintegral_const]
    apply lintegral_mono_ae
    filter_upwards [hν] with b hb
    exact (rateResidual_le hb hy.le).trans (ENNReal.ofReal_le_ofReal (by linarith))
  · rw [residual, indicator_of_notMem (show y ∉ Ioi (0 : ℝ) from hy)]
    exact zero_le _

/-- The full soft density splits into the gamma Lévy density and a positive residual. -/
theorem softDensity_split (ν : Measure ℝ) {B y : ℝ} (hy : 0 < y)
    (hν : ∀ᵐ b ∂ν, b ≤ B) :
    (∫⁻ b, ENNReal.ofReal (exp (-(b*y))/y) ∂ν) =
      ENNReal.ofReal (exp (-(B*y))/y) * ν univ + residual ν B y := by
  rw [residual_eq ν hy hν, ← lintegral_const]
  rw [← lintegral_add_left measurable_const]
  apply lintegral_congr_ae
  filter_upwards [hν] with b hb
  have hp : exp (-(B*y)) ≤ exp (-(b*y)) :=
    exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hb hy.le))
  rw [← ENNReal.ofReal_add (div_nonneg (exp_pos _).le hy.le)
    (div_nonneg (sub_nonneg.mpr hp) hy.le)]
  congr 1
  ring

/-- The positive residual Lévy measure in the manuscript. -/
def residualMeasure (ν : Measure ℝ) (B : ℝ) : Measure ℝ :=
  volume.withDensity (residual ν B)

theorem residualMeasure_below (ν : Measure ℝ) (B : ℝ) :
    residualMeasure ν B (Iic 0) = 0 := by
  rw [residualMeasure, withDensity_apply _ measurableSet_Iic,
    setLIntegral_congr_fun (g := fun _ ↦ 0) measurableSet_Iic, lintegral_zero]
  intro y hy
  exact indicator_of_notMem (not_lt.mpr hy) _

/-- Exponential test function for Laplace transforms of emitted energy. -/
def laplaceTest (τ y : ℝ) : ℝ≥0∞ := ENNReal.ofReal (exp (-(τ*y)))

@[fun_prop]
theorem measurable_laplaceTest (τ : ℝ) : Measurable (laplaceTest τ) := by
  unfold laplaceTest
  fun_prop

theorem tilted_rateResidual {B b τ : ℝ} (hb : 0 < b) (hbB : b ≤ B) (hτ : 0 ≤ τ) :
    ∫⁻ y in Ioi (0 : ℝ), rateResidual B b y * laplaceTest τ y =
      ENNReal.ofReal (log ((B+τ)/(b+τ))) := by
  have hswap : ∫⁻ y in Ioi (0 : ℝ), ∫⁻ r in Ioc b B, ENNReal.ofReal (exp (-((r+τ)*y))) =
      ∫⁻ r in Ioc b B, ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (exp (-((r+τ)*y))) :=
    lintegral_lintegral_swap (by fun_prop)
  calc
    _ = ∫⁻ y in Ioi (0 : ℝ), ∫⁻ r in Ioc b B, ENNReal.ofReal (exp (-((r+τ)*y))) := by
      apply lintegral_congr
      intro y
      rw [rateResidual, ← lintegral_mul_const _ (by fun_prop)]
      apply lintegral_congr
      intro r
      rw [laplaceTest, ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
      congr 2
      ring
    _ = _ := hswap
    _ = ∫⁻ r in Ioc b B, ENNReal.ofReal (1/(r+τ)) := by
      refine setLIntegral_congr_fun measurableSet_Ioc fun r hr ↦ ?_
      have hrt : 0 < r+τ := by have := hr.1; linarith
      have hn : -(r+τ) < 0 := neg_lt_zero.mpr hrt
      simp_rw [← neg_mul]
      rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Ioi hn 0)
        (ae_of_all _ fun _ ↦ (exp_pos _).le), integral_exp_mul_Ioi hn]
      simp only [mul_zero, exp_zero, neg_div_neg_eq]
    _ = _ := by
      have hpos : ∀ r ∈ [[b,B]], 0 < r+τ := by
        rw [uIcc_of_le hbB]
        intro r hr
        have := hr.1
        linarith
      have hc : ContinuousOn (fun r : ℝ ↦ 1/(r+τ)) [[b,B]] :=
        continuousOn_const.div (by fun_prop) (fun r hr ↦ (hpos r hr).ne')
      rw [← ofReal_integral_eq_lintegral_ofReal hc.intervalIntegrable.1,
        ← intervalIntegral.integral_of_le hbB,
        intervalIntegral.integral_comp_add_right (f := fun r : ℝ ↦ 1/r) τ,
        integral_one_div_of_pos (by linarith) (by linarith)]
      exact (ae_restrict_iff' measurableSet_Ioc).mpr <| ae_of_all _ fun r hr ↦ by
        exact one_div_nonneg.mpr (by have := hr.1; linarith)

theorem tilted_residualMeasure (ν : Measure ℝ) [SFinite ν] {B τ : ℝ}
    (hν : ∀ᵐ b ∂ν, 0 < b ∧ b ≤ B) (hτ : 0 ≤ τ) :
    ∫⁻ y, laplaceTest τ y ∂residualMeasure ν B =
      ∫⁻ b, ENNReal.ofReal (log ((B+τ)/(b+τ))) ∂ν := by
  rw [residualMeasure, lintegral_withDensity_eq_lintegral_mul _ (measurable_residual ν B)
    (measurable_laplaceTest τ)]
  change (∫⁻ y, residual ν B y * laplaceTest τ y) = _
  calc
    _ = ∫⁻ y in Ioi (0 : ℝ), (∫⁻ b, rateResidual B b y ∂ν) * laplaceTest τ y := by
      rw [← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro y
      exact (indicator_mul_left ..).symm
    _ = ∫⁻ y in Ioi (0 : ℝ), ∫⁻ b, rateResidual B b y * laplaceTest τ y ∂ν := by
      apply lintegral_congr
      intro y
      have hm : Measurable (fun b ↦ rateResidual B b y) :=
        (measurable_rateResidual B).comp (f := fun b ↦ (b,y)) (by fun_prop)
      exact (lintegral_mul_const _ hm).symm
    _ = ∫⁻ b, (∫⁻ y in Ioi (0 : ℝ), rateResidual B b y * laplaceTest τ y) ∂ν := by
      have hm : Measurable (fun p : ℝ × ℝ ↦ rateResidual B p.2 p.1 * laplaceTest τ p.1) :=
        ((measurable_rateResidual B).comp measurable_swap).mul
          ((measurable_laplaceTest τ).comp measurable_fst)
      exact lintegral_lintegral_swap (f := fun y b ↦ rateResidual B b y * laplaceTest τ y)
        hm.aemeasurable
    _ = _ := lintegral_congr_ae (hν.mono fun _ hb ↦ tilted_rateResidual hb.1 hb.2 hτ)

theorem residualMeasure_mass (ν : Measure ℝ) [SFinite ν] {B : ℝ}
    (hν : ∀ᵐ b ∂ν, 0 < b ∧ b ≤ B) :
    residualMeasure ν B univ = ∫⁻ b, ENNReal.ofReal (log (B/b)) ∂ν := by
  simpa [laplaceTest] using tilted_residualMeasure ν hν (le_refl (0 : ℝ))

theorem finite_residualMeasure (ν : Measure ℝ) [IsFiniteMeasure ν] {b₀ B : ℝ}
    (hb₀ : 0 < b₀) (hb₀B : b₀ ≤ B) (hν : ∀ᵐ b ∂ν, b₀ ≤ b ∧ b ≤ B) :
    IsFiniteMeasure (residualMeasure ν B) := by
  constructor
  rw [residualMeasure_mass ν (hν.mono fun _ hb ↦ ⟨hb₀.trans_le hb.1, hb.2⟩)]
  refine lt_of_le_of_lt (b := ENNReal.ofReal (log (B/b₀)) * ν univ) ?_ ?_
  · rw [← lintegral_const]
    apply lintegral_mono_ae
    filter_upwards [hν] with b hb
    exact ENNReal.ofReal_le_ofReal (log_le_log (div_pos (hb₀.trans_le hb₀B) (hb₀.trans_le hb.1))
      (div_le_div_of_nonneg_left (hb₀.le.trans hb₀B) hb₀ hb.1))
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

end UV.ContinueRigidLaw
