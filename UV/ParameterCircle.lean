import UV.Holomorphy
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Holomorphic parameter dependence of an actual circle integral. Compact
majorants follow from joint continuity, rather than being supplied as
integrability or derivative hypotheses. -/

noncomputable section
open MeasureTheory Filter Set Metric Complex
open scoped Topology

namespace UV

def parameterCircleIntegrand (F : ℂ → ℂ → ℂ) (c : ℂ) (r : ℝ) (lam : ℂ) (θ : ℝ) : ℂ :=
  deriv (circleMap c r) θ * F lam (circleMap c r θ)

theorem parameterCircle_compact_bound {Ω K : Set ℂ} {F : ℂ → ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hF : ContinuousOn (Function.uncurry F) (Ω ×ˢ sphere c r))
    (hK : IsCompact K) (hsub : K ⊆ Ω) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ lam ∈ K, ∀ z ∈ sphere c r, ‖F lam z‖ ≤ M := by
  obtain ⟨B, hB⟩ := (hK.prod (isCompact_sphere c r)).exists_bound_of_continuousOn
    (hF.mono (Set.prod_mono hsub subset_rfl))
  refine ⟨max B 0, le_max_right _ _, fun lam hlam z hz => ?_⟩
  exact (hB (lam, z) ⟨hlam, hz⟩).trans (le_max_left _ _)

theorem parameterCircleIntegrand_continuous {Ω : Set ℂ} {F : ℂ → ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hF : ContinuousOn (Function.uncurry F) (Ω ×ˢ sphere c r))
    {lam : ℂ} (hlam : lam ∈ Ω) : Continuous (parameterCircleIntegrand F c r lam) := by
  have hf : Continuous (fun θ : ℝ => F lam (circleMap c r θ)) :=
    hF.comp_continuous (continuous_const.prodMk (continuous_circleMap c r))
      (fun θ => ⟨hlam, circleMap_mem_sphere c hr θ⟩)
  have hw : Continuous (fun θ : ℝ => deriv (circleMap c r) θ) := by
    simp_rw [deriv_circleMap]
    exact (continuous_circleMap 0 r).mul continuous_const
  exact hw.mul hf

theorem parameterCircleIntegrand_norm {F : ℂ → ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (lam : ℂ) (θ : ℝ) :
    ‖parameterCircleIntegrand F c r lam θ‖ = r * ‖F lam (circleMap c r θ)‖ := by
  rw [parameterCircleIntegrand, norm_mul, deriv_circleMap, norm_mul, norm_circleMap_zero,
    norm_I, mul_one, abs_of_nonneg hr]

/-- The common compact majorant of the weighted, genuine circle integrand
is derived from continuity on the product with the compact circle. -/
theorem parameterCircle_differentiableOn {Ω : Set ℂ} {F : ℂ → ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hΩ : IsOpen Ω) (hr : 0 ≤ r)
    (hF : ContinuousOn (Function.uncurry F) (Ω ×ˢ sphere c r))
    (hhol : ∀ z ∈ sphere c r, DifferentiableOn ℂ (fun lam => F lam z) Ω) :
    DifferentiableOn ℂ (fun lam => circleIntegral (F lam) c r) Ω := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) (2 * Real.pi))
  have hm : ∀ lam ∈ Ω, AEStronglyMeasurable (parameterCircleIntegrand F c r lam) μ := by
    intro lam hlam
    exact (parameterCircleIntegrand_continuous hr hF hlam).aestronglyMeasurable
  have hd : ∀ᵐ θ ∂μ, DifferentiableOn ℂ (fun lam => parameterCircleIntegrand F c r lam θ) Ω := by
    exact Eventually.of_forall fun θ =>
      (hhol _ (circleMap_mem_sphere c hr θ)).const_mul _
  have hb : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∃ M : ℝ → ℝ,
      Integrable M μ ∧ ∀ᵐ θ ∂μ, ∀ lam ∈ K, ‖parameterCircleIntegrand F c r lam θ‖ ≤ M θ := by
    intro K hK hsub
    obtain ⟨B, _hB, hbound⟩ := parameterCircle_compact_bound hF hK hsub
    refine ⟨fun _ => r * B, integrable_const _, Eventually.of_forall fun θ lam hlam => ?_⟩
    rw [parameterCircleIntegrand_norm hr]
    exact mul_le_mul_of_nonneg_left (hbound lam hlam _ (circleMap_mem_sphere c hr θ)) hr
  have hi := holomorphy_from_compact_graph_majorants hΩ hm hd hb
  simpa only [circleIntegral_def_Icc, parameterCircleIntegrand, smul_eq_mul] using hi

theorem parameterCircle_analyticOnNhd {Ω : Set ℂ} {F : ℂ → ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hΩ : IsOpen Ω) (hr : 0 ≤ r)
    (hF : ContinuousOn (Function.uncurry F) (Ω ×ˢ sphere c r))
    (hhol : ∀ z ∈ sphere c r, DifferentiableOn ℂ (fun lam => F lam z) Ω) :
    AnalyticOnNhd ℂ (fun lam => circleIntegral (F lam) c r) Ω :=
  (parameterCircle_differentiableOn hΩ hr hF hhol).analyticOnNhd hΩ

end UV
