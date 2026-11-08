import Mathlib.MeasureTheory.Integral.Pi
import UV.GlobalConvergence
import UV.SchwingerEnvelope

/-! The positive joint-parameter step is a Fubini statement, not a Wick-rotation
claim. Finite line-parameter products are retained before the loop integral. -/
noncomputable section
open MeasureTheory Set Real
open scoped BigOperators
namespace UV

/-- The absolute integral over independent line parameters factors exactly.
    No integration-order exchange over loop momentum is used here. -/
theorem joint_parameter_norm_integral {ι T : Type*} [Fintype ι]
    [MeasurableSpace T] (ν : ι → Measure T) [∀ i, SigmaFinite (ν i)]
    (F : ι → T → ℝ) (N : ℝ) :
    (∫ t : ι → T, ‖N * ∏ i, F i (t i)‖ ∂Measure.pi ν) =
      ‖N‖ * ∏ i, ∫ t, ‖F i t‖ ∂ν i := by
  simp_rw [norm_mul, norm_prod]
  rw [integral_const_mul]
  congr 1
  exact integral_fintype_prod_eq_prod (μ := ν) (fun i t => ‖F i t‖)

/-- Once the loop-space absolute majorant is integrable, the actual joint
    line-parameter/loop product is integrable. The equivalence exposes precisely
    the remaining measurability and individual line-parameter obligations. -/
theorem joint_parameter_integrable_iff {ι T K : Type*} [Fintype ι]
    [MeasurableSpace T] [MeasurableSpace K]
    (ν : ι → Measure T) [∀ i, SigmaFinite (ν i)] (μ : Measure K) [SigmaFinite μ]
    (F : ι → K → T → ℝ) (N : K → ℝ)
    (hline : ∀ k i, Integrable (F i k) (ν i))
    (hmeas : AEStronglyMeasurable
      (fun z : K × (ι → T) => N z.1 * ∏ i, F i z.1 (z.2 i)) (μ.prod (Measure.pi ν))) :
    Integrable (fun z : K × (ι → T) => N z.1 * ∏ i, F i z.1 (z.2 i))
      (μ.prod (Measure.pi ν)) ↔
      Integrable (fun k => ‖N k‖ * ∏ i, ∫ t, ‖F i k t‖ ∂ν i) μ := by
  rw [integrable_prod_iff hmeas]
  have hinner : ∀ k, Integrable (fun t : ι → T => N k * ∏ i, F i k (t i))
      (Measure.pi ν) := fun k => (Integrable.fintype_prod (hline k)).const_mul _
  simp only [Filter.Eventually.of_forall hinner, true_and]
  simp_rw [joint_parameter_norm_integral]

/-- Actual proper-time/Laplace line factors have an absolutely integrable
    product at every nonnegative kinetic value. -/
theorem schwinger_laplace_parameter_integrable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0)
    {E : ℝ → ℝ} (hE : IntegrableOn E (Ioi 0))
    (hpos : ∀ α, 0 < α → 0 ≤ E α) {a z : ℝ} (hz : 0 ≤ z) :
    Integrable (fun t : ℝ × ℝ => exp (-t.1 * (a ^ 2 * z)) *
      (E t.2 * exp (-t.2 * z))) (ρ.prod (volume.restrict (Ioi 0))) := by
  have hτ : Integrable (fun τ : ℝ => exp (-τ * (a ^ 2 * z))) ρ := by
    refine (integrable_const (μ := ρ) (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [ae_positive_of_support_no_atom ρ hneg hzero] with τ hτ
    rw [Real.norm_of_nonneg (exp_nonneg _)]
    exact exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr hτ.le) (mul_nonneg (sq_nonneg a) hz))
  exact hτ.mul_prod (schwinger_covariance_parameter_integrable hE hpos hz)

theorem schwinger_laplace_parameter_integral (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (E : ℝ → ℝ) (a z : ℝ) :
    (∫ t : ℝ × ℝ, exp (-t.1 * (a ^ 2 * z)) * (E t.2 * exp (-t.2 * z))
      ∂ρ.prod (volume.restrict (Ioi 0))) =
      laplace ρ (a ^ 2 * z) * schwingerCovariance E z := by
  exact integral_prod_mul (fun τ : ℝ => exp (-τ * (a ^ 2 * z)))
    (fun α : ℝ => E α * exp (-α * z))

/-- The absolute inner integral is the actual damped covariance, rather than
    an independently postulated parameter majorant. -/
theorem schwinger_laplace_parameter_norm_integral (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {E : ℝ → ℝ} (hpos : ∀ α, 0 < α → 0 ≤ E α) (a z : ℝ) :
    (∫ t : ℝ × ℝ, ‖exp (-t.1 * (a ^ 2 * z)) * (E t.2 * exp (-t.2 * z))‖
      ∂ρ.prod (volume.restrict (Ioi 0))) =
      laplace ρ (a ^ 2 * z) * schwingerCovariance E z := by
  simp_rw [norm_mul, Real.norm_of_nonneg (exp_nonneg _)]
  rw [integral_prod_mul (fun τ : ℝ => exp (-τ * (a ^ 2 * z)))
    (fun α : ℝ => ‖E α‖ * exp (-α * z))]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro α hα
  dsimp only
  rw [Real.norm_of_nonneg (hpos α hα)]

/-- Actual finite proper-time and Laplace representations preserve absolute
    convergence. The loop-space hypothesis is the majorant proved by the graph
    theorem; joint parameter integrability is its derived conclusion. -/
theorem actual_joint_majorant_integrable {ι K : Type*} [Fintype ι]
    [MeasurableSpace K] (μ : Measure K) [SigmaFinite μ]
    (ρ : ι → Measure ℝ) [∀ i, IsFiniteMeasure (ρ i)]
    (E : ι → ℝ → ℝ) (a : ι → ℝ) (q : ι → K → ℝ) (N : K → ℝ)
    (hneg : ∀ i, ρ i (Iio 0) = 0) (hzero : ∀ i, ρ i {0} = 0)
    (hE : ∀ i, IntegrableOn (E i) (Ioi 0))
    (hpos : ∀ i α, 0 < α → 0 ≤ E i α) (hq : ∀ i k, 0 ≤ q i k)
    (hmeas : AEStronglyMeasurable
      (fun z : K × (ι → ℝ × ℝ) => N z.1 * ∏ i,
        exp (-(z.2 i).1 * ((a i) ^ 2 * q i z.1)) *
          (E i (z.2 i).2 * exp (-(z.2 i).2 * q i z.1)))
      (μ.prod (Measure.pi (fun i => (ρ i).prod (volume.restrict (Ioi 0))))))
    (hgraph : Integrable (fun k => ‖N k‖ * ∏ i,
      (laplace (ρ i) ((a i) ^ 2 * q i k) * schwingerCovariance (E i) (q i k))) μ) :
    Integrable (fun z : K × (ι → ℝ × ℝ) => N z.1 * ∏ i,
      exp (-(z.2 i).1 * ((a i) ^ 2 * q i z.1)) *
        (E i (z.2 i).2 * exp (-(z.2 i).2 * q i z.1)))
      (μ.prod (Measure.pi (fun i => (ρ i).prod (volume.restrict (Ioi 0))))) := by
  rw [integrable_prod_iff hmeas]
  constructor
  · apply Filter.Eventually.of_forall
    intro k
    exact (Integrable.fintype_prod (fun i =>
      schwinger_laplace_parameter_integrable (ρ i) (hneg i) (hzero i)
        (hE i) (hpos i) (hq i k))).const_mul (N k)
  · apply hgraph.congr
    apply Filter.Eventually.of_forall
    intro k
    symm
    calc
      _ = ‖N k‖ * ∏ i, ∫ t : ℝ × ℝ,
          ‖exp (-t.1 * ((a i) ^ 2 * q i k)) *
            (E i t.2 * exp (-t.2 * q i k))‖
          ∂(ρ i).prod (volume.restrict (Ioi 0)) :=
        joint_parameter_norm_integral
          (fun i => (ρ i).prod (volume.restrict (Ioi 0)))
          (fun i (t : ℝ × ℝ) => exp (-t.1 * ((a i) ^ 2 * q i k)) *
            (E i t.2 * exp (-t.2 * q i k))) (N k)
      _ = _ := by
        congr 1
        apply Finset.prod_congr rfl
        intro i _
        exact schwinger_laplace_parameter_norm_integral (ρ i) (hpos i) (a i) (q i k)

end UV
