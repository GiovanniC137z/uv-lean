import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! The real-valued common-routing dominated-convergence statement in
lem:OQED-grouped-convergence. Only the pointwise sum is required to be integrable. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace UV

theorem grouped_integrable {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    {μ : Measure X} {terms : ι → X → ℝ} {bound : X → ℝ}
    (hmeas : AEStronglyMeasurable (fun x => ∑ i, terms i x) μ)
    (hbound : Integrable bound μ)
    (hle : ∀ᵐ x ∂μ, ‖∑ i, terms i x‖ ≤ bound x) :
    Integrable (fun x => ∑ i, terms i x) μ := hbound.mono' hmeas hle

/-- The same integral is obtained for any measurable exhaustion whose indicators
    eventually equal one at each point. No integrals of individual terms occur. -/
theorem grouped_exhaustion_limit {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    {μ : Measure X} {terms : ι → X → ℝ} {bound : X → ℝ}
    (hmeas : AEStronglyMeasurable (fun x => ∑ i, terms i x) μ)
    (hbound : Integrable bound μ)
    (hle : ∀ᵐ x ∂μ, ‖∑ i, terms i x‖ ≤ bound x)
    (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hexhaust : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∈ s n) :
    Tendsto (fun n => ∫ x in s n, ∑ i, terms i x ∂μ) atTop
      (𝓝 (∫ x, ∑ i, terms i x ∂μ)) := by
  simp only [← integral_indicator (hs _)]
  apply tendsto_integral_of_dominated_convergence bound
  · intro n
    exact hmeas.indicator (hs n)
  · exact hbound
  · intro n
    filter_upwards [hle] with x hx
    by_cases hxs : x ∈ s n
    · simpa [Set.indicator_of_mem hxs] using hx
    · simp only [Set.indicator_of_notMem hxs, norm_zero]
      exact (norm_nonneg _).trans hx
  · filter_upwards [hexhaust] with x hx
    exact tendsto_const_nhds.congr' (hx.mono (fun n hn => by simp [hn]))

end UV
