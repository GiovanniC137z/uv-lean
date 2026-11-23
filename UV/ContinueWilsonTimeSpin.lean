import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! The compact symmetric displacement marginal and the two time-spin
Laplace blocks of the Wilson endpoint at zero spatial momentum. -/

noncomputable section

open MeasureTheory Set Filter ProbabilityTheory Real
open scoped Topology

namespace UV

/-- The positive interior band is implied by the manuscript's positive
interior density. Reflection means sign reversal of the displacement. -/
structure WilsonRestLaw (L : ℝ) where
  law : Measure ℝ
  probability : IsProbabilityMeasure law
  length_pos : 0 < L
  band : ∀ᵐ s ∂law, |s| ≤ 2*L
  symmetric : MeasurePreserving (fun s : ℝ => -s) law law
  interior_mass : 0 < law (Ioo (L/2) L)

attribute [instance] WilsonRestLaw.probability

def wilsonTimeWeight (L σ s : ℝ) : ℝ := 1 + σ*s/(2*L)

def WilsonRestLaw.moment {L : ℝ} (D : WilsonRestLaw L) (n : ℕ) (x : ℝ) : ℝ :=
  ∫ s, s^n * exp (x*s) ∂D.law

def WilsonRestLaw.block {L : ℝ} (D : WilsonRestLaw L) (σ : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∫ s, wilsonTimeWeight L σ s * (s^n * exp (x*s)) ∂D.law

theorem WilsonRestLaw.exp_domain {L : ℝ} (D : WilsonRestLaw L) (x : ℝ) :
    x ∈ interior (integrableExpSet (id : ℝ → ℝ) D.law) := by
  have hset : integrableExpSet (id : ℝ → ℝ) D.law = univ := by
    apply eq_univ_of_forall
    intro t
    change Integrable (fun s : ℝ => exp (t*s)) D.law
    apply (integrable_const (exp (|t| * (2*L)))).mono' (by fun_prop)
    filter_upwards [D.band] with s hs
    rw [Real.norm_of_nonneg (exp_pos _).le]
    exact exp_le_exp.mpr ((le_abs_self (t*s)).trans ((abs_mul t s) ▸
      mul_le_mul_of_nonneg_left hs (abs_nonneg t)))
  simp [hset]

theorem WilsonRestLaw.moment_integrable {L : ℝ} (D : WilsonRestLaw L) (n : ℕ) (x : ℝ) :
    Integrable (fun s : ℝ => s^n * exp (x*s)) D.law :=
  integrable_pow_mul_exp_of_mem_interior_integrableExpSet (D.exp_domain x) n

theorem WilsonRestLaw.block_integrable {L : ℝ} (D : WilsonRestLaw L) (σ : ℝ) (n : ℕ) (x : ℝ) :
    Integrable (fun s => wilsonTimeWeight L σ s * (s^n * exp (x*s))) D.law := by
  apply ((D.moment_integrable n x).add ((D.moment_integrable (n+1) x).const_mul (σ/(2*L)))).congr
  filter_upwards with s
  simp only [Pi.add_apply, wilsonTimeWeight, pow_succ]
  ring

theorem WilsonRestLaw.block_moments {L : ℝ} (D : WilsonRestLaw L) (σ : ℝ) (n : ℕ) (x : ℝ) :
    D.block σ n x = D.moment n x + σ/(2*L) * D.moment (n+1) x := by
  unfold WilsonRestLaw.block WilsonRestLaw.moment
  rw [← integral_const_mul, ← integral_add (D.moment_integrable n x)
    ((D.moment_integrable (n+1) x).const_mul (σ/(2*L)))]
  congr 1
  funext s
  simp only [wilsonTimeWeight, pow_succ]
  ring

theorem WilsonRestLaw.moment_derivative {L : ℝ} (D : WilsonRestLaw L) (n : ℕ) (x : ℝ) :
    HasDerivAt (D.moment n) (D.moment (n+1) x) x :=
  hasDerivAt_integral_pow_mul_exp_real (D.exp_domain x) n

theorem WilsonRestLaw.block_derivative {L : ℝ} (D : WilsonRestLaw L) (σ : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (D.block σ n) (D.block σ (n+1) x) x := by
  rw [show D.block σ n = fun t => D.moment n t + σ/(2*L) * D.moment (n+1) t
    from funext (D.block_moments σ n), D.block_moments]
  exact (D.moment_derivative n x).add ((D.moment_derivative (n+1) x).const_mul _)

theorem WilsonRestLaw.mean_zero {L : ℝ} (D : WilsonRestLaw L) : D.moment 1 0 = 0 := by
  have h := D.symmetric.integral_comp (Homeomorph.neg ℝ).measurableEmbedding (id : ℝ → ℝ)
  change (∫ s, -s ∂D.law) = ∫ s, s ∂D.law at h
  rw [integral_neg] at h
  simp only [WilsonRestLaw.moment, zero_mul, exp_zero, mul_one, pow_one]
  linarith

theorem WilsonRestLaw.block_at_zero {L : ℝ} (D : WilsonRestLaw L) (σ : ℝ) :
    D.block σ 0 0 = 1 := by
  rw [D.block_moments, zero_add, D.mean_zero, mul_zero, add_zero]
  simp [WilsonRestLaw.moment]

theorem wilsonTimeWeight_nonneg {L σ s : ℝ} (hL : 0 < L) (hσ : |σ| ≤ 1) (hs : |s| ≤ 2*L) :
    0 ≤ wilsonTimeWeight L σ s := by
  have ha := (abs_mul σ s).symm ▸ mul_le_mul hσ hs (abs_nonneg _) zero_le_one
  simp only [one_mul] at ha
  unfold wilsonTimeWeight
  have h := (abs_le.mp ha).1
  have hlower : -1 ≤ σ*s/(2*L) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  linarith

private theorem WilsonRestLaw.weight_half {L : ℝ} (D : WilsonRestLaw L) {σ s : ℝ}
    (hσ : |σ| ≤ 1) (hs : s ∈ Ioo (L/2) L) : 1/2 ≤ wilsonTimeWeight L σ s := by
  have hl := D.length_pos
  have hs0 : 0 < s := (half_pos hl).trans hs.1
  have h1 := mul_le_mul hσ (show |s| ≤ L by simpa [abs_of_pos hs0] using hs.2.le)
    (abs_nonneg s) zero_le_one
  rw [← abs_mul, one_mul, abs_le] at h1
  unfold wilsonTimeWeight
  have hdiv : -(1/2:ℝ) ≤ σ*s/(2*L) := (le_div_iff₀ (by positivity)).mpr (by linarith [h1.1])
  linarith

theorem WilsonRestLaw.block_second_pos {L : ℝ} (D : WilsonRestLaw L) {σ : ℝ} (hσ : |σ| ≤ 1) (x : ℝ) :
    0 < D.block σ 2 x := by
  have hl := D.length_pos
  let f := fun s => wilsonTimeWeight L σ s * (s^2 * exp (x*s))
  have hnn : 0 ≤ᵐ[D.law] f := D.band.mono (fun s hs =>
    mul_nonneg (wilsonTimeWeight_nonneg hl hσ hs) (by positivity))
  apply (integral_pos_iff_support_of_nonneg_ae hnn (D.block_integrable σ 2 x)).mpr
  apply D.interior_mass.trans_le (measure_mono _)
  intro s hs
  have hw : 0 < wilsonTimeWeight L σ s := (by norm_num : (0:ℝ) < 1/2).trans_le (D.weight_half hσ hs)
  have hs0 : 0 < s := (half_pos hl).trans hs.1
  exact (mul_pos hw (mul_pos (sq_pos_of_pos hs0) (exp_pos _))).ne'

/-- A positive band of interior displacements forces either spin block
to grow without bound on the positive real energy axis. -/
theorem WilsonRestLaw.block_atTop {L : ℝ} (D : WilsonRestLaw L) {σ : ℝ} (hσ : |σ| ≤ 1) :
    Tendsto (D.block σ 0) atTop atTop := by
  let I := Ioo (L/2) L
  have hl := D.length_pos
  have hm : 0 < D.law.real I := ENNReal.toReal_pos (ne_of_gt D.interior_mass) (measure_ne_top _ _)
  have hlim : Tendsto (fun x : ℝ => (D.law.real I / 2) * exp (x*(L/2))) atTop atTop :=
    Tendsto.const_mul_atTop (half_pos hm) (tendsto_exp_atTop.comp
      (tendsto_id.atTop_mul_const (half_pos hl)))
  apply tendsto_atTop_mono' atTop _ hlim
  filter_upwards [Ici_mem_atTop (0:ℝ)] with x hx
  let f := fun s => wilsonTimeWeight L σ s * (s^0 * exp (x*s))
  have hf := D.block_integrable σ 0 x
  have hnn : 0 ≤ᵐ[D.law] f := D.band.mono (fun s hs =>
    mul_nonneg (wilsonTimeWeight_nonneg hl hσ hs) (by positivity))
  calc
    _ = ∫ s in I, (1/2:ℝ)*exp (x*(L/2)) ∂D.law := by
      rw [setIntegral_const, smul_eq_mul]
      ring
    _ ≤ ∫ s in I, f s ∂D.law := by
      apply integral_mono_ae (integrable_const _) hf.integrableOn
      filter_upwards [ae_restrict_mem (μ := D.law) (s := I) measurableSet_Ioo] with s hs
      simp only [pow_zero, one_mul]
      exact mul_le_mul (D.weight_half hσ hs)
        (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.1.le hx)) (exp_pos _).le
        (by linarith [D.weight_half hσ hs])
    _ ≤ _ := setIntegral_le_integral hf hnn

theorem WilsonRestLaw.block_reflect {L : ℝ} (D : WilsonRestLaw L) (σ x : ℝ) :
    D.block σ 0 (-x) = D.block (-σ) 0 x := by
  unfold WilsonRestLaw.block
  rw [← D.symmetric.integral_comp (Homeomorph.neg ℝ).measurableEmbedding
    (fun s => wilsonTimeWeight L σ s * (s^0 * exp (-x*s)))]
  congr 1
  funext s
  simp [wilsonTimeWeight]

end UV
