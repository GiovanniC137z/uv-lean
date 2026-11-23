import UV.ContinueOmegaResultTwist
import Mathlib.Topology.ContinuousMap.Compact

/-! Exhausting radial collars for fixed-order marked integrals on
surviving paths, and positivity of a semibounded spectral heat weight. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace UV

/-- The same compact radial collar must contain the entire time path,
including every split endpoint and every normal excursion. -/
def omegaCollar {K : Type*} [TopologicalSpace K] (n : ℕ) : Set C(K,ℝ) :=
  ⋂ t : K, (fun r : C(K,ℝ) => r t) ⁻¹' Icc (1/(n+1:ℝ)) (1-1/(n+1:ℝ))

theorem omega_collar_closed {K : Type*} [TopologicalSpace K] (n : ℕ) :
    IsClosed (omegaCollar (K := K) n) := by
  exact isClosed_iInter (fun t => isClosed_Icc.preimage (continuous_eval_const t))

theorem omega_surviving_path_eventually_in_collar {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [Nonempty K] (r : C(K,ℝ)) (h : ∀ t, r t ∈ Ioo (0:ℝ) 1) :
    ∀ᶠ n : ℕ in atTop, r ∈ omegaCollar n := by
  obtain ⟨a,_,ha⟩ := isCompact_univ.exists_isMinOn (univ_nonempty (α := K)) r.continuous.continuousOn
  obtain ⟨b,_,hb⟩ := isCompact_univ.exists_isMaxOn (univ_nonempty (α := K)) r.continuous.continuousOn
  have he := tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [he.eventually_lt_const (h a).1,he.eventually_lt_const (sub_pos.mpr (h b).2)] with n hn hm
  apply mem_iInter.mpr
  intro t
  exact ⟨hn.le.trans (ha (mem_univ t)),(hb (mem_univ t)).trans (by linarith)⟩

/-- Conditional on the actual integrable joint majorant, removal of the
inner and outer killing collars holds for every complex marked amplitude.
Other coordinates can include every internal frequency and spatial loop
momentum, in the same measure as the shared surviving normal path. -/
theorem omega_marked_collar_exhaustion {K Ω : Type*} [TopologicalSpace K]
    [CompactSpace K] [Nonempty K] [MeasurableSpace Ω] (μ : Measure Ω)
    (r : Ω → C(K,ℝ)) (hr : @Measurable _ _ _ (borel _) r)
    (hs : ∀ᵐ x ∂μ, ∀ t, r x t ∈ Ioo (0:ℝ) 1) (F : Ω → ℂ) (hF : Integrable F μ) :
    Tendsto (fun n : ℕ => ∫ x, ((r ⁻¹' omegaCollar n).indicator F) x ∂μ)
      atTop (𝓝 (∫ x, F x ∂μ)) := by
  letI : MeasurableSpace C(K,ℝ) := borel _
  letI : BorelSpace C(K,ℝ) := ⟨rfl⟩
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖F x‖)
  · exact Eventually.of_forall fun n => hF.aestronglyMeasurable.indicator (hr ((omega_collar_closed n).measurableSet))
  · exact Eventually.of_forall fun n => Eventually.of_forall fun x => by
      by_cases hx : x ∈ r ⁻¹' omegaCollar n <;> simp [hx]
  · exact hF.norm
  · filter_upwards [hs] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [omega_surviving_path_eventually_in_collar (r x) hx] with n hn
    simp [hn]

/-- On the scalar spectral measure of a nonzero state, a semibounded
Hamiltonian gives a strictly positive diagonal heat matrix element, even
with unbounded spectrum. No spectral gap or compact resolvent is used. -/
theorem omega_semibounded_spectral_diagonal (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    {E₀ t : ℝ} (ht : 0 ≤ t) (hs : ∀ᵐ E ∂μ, E₀ ≤ E) :
    let w := fun E => Real.exp (-t*E)
    Integrable w μ ∧ 0 < ∫ E, w E ∂μ := by
  let w := fun E => Real.exp (-t*E)
  have hi : Integrable w μ := by
    apply (integrable_const (Real.exp (-t*E₀))).mono'
    · exact (show Continuous w by dsimp [w]; fun_prop).aestronglyMeasurable
    · filter_upwards [hs] with E hE
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hE (neg_nonpos.mpr ht))
  refine ⟨hi,(integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hi).mpr ?_⟩
  have he : Function.support w = univ := eq_univ_of_forall fun E => (Real.exp_pos _).ne'
  rw [he]
  exact Measure.measure_univ_pos.mpr hμ

end UV
