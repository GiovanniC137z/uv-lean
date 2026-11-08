import UV.Grouped
import UV.Holomorphy

/-! Common-domain limits of actual finite complex sums.  Only the complete
pointwise sum is dominated; its constituents need not be integrable. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace UV

theorem complex_grouped_exhaustion_limit {X ι : Type*}
    [MeasurableSpace X] [Fintype ι] {μ : Measure X}
    (c : ι → ℂ) (J : ι → X → ℂ) {M : X → ℝ}
    (hm : AEStronglyMeasurable (fun x => ∑ i, c i * J i x) μ)
    (hM : Integrable M μ)
    (hb : ∀ᵐ x ∂μ, ‖∑ i, c i * J i x‖ ≤ M x)
    (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hexhaust : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∈ s n) :
    Integrable (fun x => ∑ i, c i * J i x) μ ∧
      Tendsto (fun n => ∫ x in s n, ∑ i, c i * J i x ∂μ) atTop
        (𝓝 (∫ x, ∑ i, c i * J i x ∂μ)) := by
  refine ⟨hM.mono' hm hb, ?_⟩
  simp only [← integral_indicator (hs _)]
  apply tendsto_integral_of_dominated_convergence M
  · intro n
    exact hm.indicator (hs n)
  · exact hM
  · intro n
    filter_upwards [hb] with x hx
    by_cases hxs : x ∈ s n
    · simpa only [Set.indicator_of_mem hxs] using hx
    · simp only [Set.indicator_of_notMem hxs, norm_zero]
      exact (norm_nonneg _).trans hx
  · filter_upwards [hexhaust] with x hx
    exact tendsto_const_nhds.congr' (hx.mono fun n hn => by simp [hn])

theorem common_integral_uniform_tail {X P : Type*} [MeasurableSpace X]
    {μ : Measure X} (F : P → X → ℂ) {M : X → ℝ}
    (hm : ∀ p, AEStronglyMeasurable (F p) μ) (hM : Integrable M μ)
    (hb : ∀ p, ∀ᵐ x ∂μ, ‖F p x‖ ≤ M x)
    {s : Set X} (hs : MeasurableSet s) (p : P) :
    ‖(∫ x in s, F p x ∂μ) - ∫ x, F p x ∂μ‖ ≤ ∫ x in sᶜ, M x ∂μ := by
  have hi := hM.mono' (hm p) (hb p)
  have he := integral_add_compl hs hi
  have hdiff : (∫ x in s, F p x ∂μ) - ∫ x, F p x ∂μ =
      -(∫ x in sᶜ, F p x ∂μ) := by rw [← he]; abel
  rw [hdiff, norm_neg]
  exact (norm_integral_le_integral_norm _).trans
    (integral_mono_ae hi.integrableOn.norm hM.integrableOn
      (ae_restrict_of_ae (hb p)))

theorem finite_common_routing_holomorphy
    {X ι H : Type*} [MeasurableSpace X] [Fintype ι]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H] [ProperSpace H]
    {μ : Measure X} (c : ι → ℂ) (J : ι → H → X → ℂ) {Ω : Set H}
    (hΩ : IsOpen Ω)
    (hm : ∀ z ∈ Ω, AEStronglyMeasurable (fun x => ∑ i, c i * J i z x) μ)
    (hd : ∀ᵐ x ∂μ, DifferentiableOn ℂ (fun z => ∑ i, c i * J i z x) Ω)
    (hb : ∀ K : Set H, IsCompact K → K ⊆ Ω → ∃ M : X → ℝ,
      Integrable M μ ∧ ∀ᵐ x ∂μ, ∀ z ∈ K, ‖∑ i, c i * J i z x‖ ≤ M x) :
    DifferentiableOn ℂ (fun z => ∫ x, ∑ i, c i * J i z x ∂μ) Ω :=
  holomorphy_from_compact_graph_majorants hΩ hm hd hb

/-- A declared finite-domain prescription is identified with the actual
common-domain integral before taking any limit. -/
theorem action_coefficient_common_domain_limit {X ι P : Type*}
    [MeasurableSpace X] [Fintype ι] {μ : Measure X}
    (c : ι → ℂ) (J : ι → P → X → ℂ) (A : ℕ → P → ℂ) {M : X → ℝ}
    (hm : ∀ p, AEStronglyMeasurable (fun x => ∑ i, c i * J i p x) μ)
    (hM : Integrable M μ)
    (hb : ∀ p, ∀ᵐ x ∂μ, ‖∑ i, c i * J i p x‖ ≤ M x)
    (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hexhaust : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∈ s n)
    (hprescription : ∀ n p, A n p = ∫ x in s n, ∑ i, c i * J i p x ∂μ) :
    ∀ p, Integrable (fun x => ∑ i, c i * J i p x) μ ∧
      Tendsto (fun n => A n p) atTop (𝓝 (∫ x, ∑ i, c i * J i p x ∂μ)) := by
  intro p
  simpa only [hprescription] using complex_grouped_exhaustion_limit
    c (fun i x => J i p x) (hm p) hM (hb p) s hs hexhaust

end UV
