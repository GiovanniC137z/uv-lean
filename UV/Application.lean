import UV.Convergence

/-! A concrete O--QED application of the exponential convergence criterion.
The bound is on the complete integrand, including vertices and denominators.
This is a sufficient subclass, not thm:OQED-fixed-graph in its full generality. -/

noncomputable section
open MeasureTheory

namespace UV

theorem kernel_norm_sq_upper {E : Type*} [NormedAddCommGroup E]
    {a M : ℝ} (ha : 0 ≤ a) (x : E) :
    kernel a M (‖x‖ ^ 2) ≤ Real.exp (a * M) * Real.exp (-(a * ‖x‖)) := by
  simpa only [Real.sqrt_sq (norm_nonneg x), neg_mul] using
    kernel_upper (M := M) ha (sq_nonneg ‖x‖)

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {μ : Measure E} [μ.HasTemperateGrowth]
  {F : Type*} [NormedAddCommGroup F] {P : Type*}

theorem oqed_complete_integrand_convergence {a M C : ℝ} {n : ℕ} {f : P → E → F}
    (ha : 0 < a) (hC : 0 ≤ C)
    (hf : ∀ p, AEStronglyMeasurable (f p) μ)
    (hcomplete : ∀ p x, ‖f p x‖ ≤ C * (1 + ‖x‖ ^ n) * kernel a M (‖x‖ ^ 2)) :
    ∀ p, Integrable (f p) μ := by
  apply graph_integrable_of_common_bound (C := C * Real.exp (a * M)) ha hf
  intro p x
  calc
    ‖f p x‖ ≤ C * (1 + ‖x‖ ^ n) * kernel a M (‖x‖ ^ 2) := hcomplete p x
    _ ≤ C * (1 + ‖x‖ ^ n) *
        (Real.exp (a * M) * Real.exp (-(a * ‖x‖))) := by
      exact mul_le_mul_of_nonneg_left (kernel_norm_sq_upper ha.le x) (by positivity)
    _ = _ := by ring

end UV
