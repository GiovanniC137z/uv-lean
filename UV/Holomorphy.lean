import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic
import UV.DerivativeMeasurability

/-! Common function bounds yield derivative bounds by the complex Cauchy
estimate. No derivative majorant is an extra graph assumption. -/
noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology
namespace UV

theorem common_bound_fderiv_norm {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {f : H → ℂ} {c y : H} {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hf : DifferentiableOn ℂ f (ball c R))
    (hb : ∀ x ∈ ball c R, ‖f x‖ ≤ M) (hy : y ∈ ball c (R / 4)) :
    ‖fderiv ℂ f y‖ ≤ 2 * M / R := by
  letI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  let g : ℂ → ℂ := fun z => f (y + z • v)
  have hmaps : ∀ z ∈ closedBall (0 : ℂ) (R / 2), y + z • v ∈ ball c R := by
    intro z hz
    have hnorm : ‖z‖ ≤ R / 2 := by simpa using hz
    have hy' : ‖y - c‖ < R / 4 := by simpa only [mem_ball, dist_eq_norm] using hy
    rw [mem_ball, dist_eq_norm]
    have heq : y + z • v - c = (y - c) + z • v := by abel
    rw [heq]
    calc
      ‖(y - c) + z • v‖ ≤ ‖y - c‖ + ‖z • v‖ := norm_add_le _ _
      _ = ‖y - c‖ + ‖z‖ := by rw [norm_smul, hv, mul_one]
      _ < R := by linarith
  have hg : DifferentiableOn ℂ g (closedBall 0 (R / 2)) := by
    intro z hz
    have hm : Differentiable ℂ (fun z : ℂ => y + z • v) :=
      (differentiable_id.smul_const v).const_add y
    exact ((hf.differentiableAt (isOpen_ball.mem_nhds (hmaps z hz))).comp z
      (hm z)).differentiableWithinAt
  have hgc : DiffContOnCl ℂ g (ball 0 (R / 2)) := by
    apply hg.diffContOnCl_ball
    exact subset_rfl
  have he := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (show 0 < R / 2 by linarith) hgc
    (fun z hz => hb (y + z • v) (hmaps z (sphere_subset_closedBall hz)))
  have hyR : y ∈ ball c R := ball_subset_ball (by linarith) hy
  have hm : HasDerivAt (fun z : ℂ => y + z • v) v 0 := by
    simpa using (((hasDerivAt_id (0 : ℂ)).smul_const v).const_add y)
  have hd : HasFDerivAt f (fderiv ℂ f y) (y + (0 : ℂ) • v) := by
    simpa using (hf.differentiableAt (isOpen_ball.mem_nhds hyR)).hasFDerivAt
  have hder := hd.comp_hasDerivAt 0 hm
  have hder' : deriv g 0 = (fderiv ℂ f y) v := by
    simpa only [zero_smul, add_zero, one_smul, g] using hder.deriv
  rw [hder'] at he
  convert he using 1
  ring

/-- The common function majorant supplies an integrable derivative majorant;
    derivative measurability follows from point samples and differentiability. -/
theorem graph_integral_hasFDerivAt_of_common_majorant
    {H X : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
    [MeasurableSpace X] {μ : Measure X} {F : H → X → ℂ} {c : H} {R : ℝ}
    (hR : 0 < R) (hm : ∀ z, AEStronglyMeasurable (F z) μ)
    (hd : ∀ᵐ ξ ∂μ, DifferentiableOn ℂ (fun z => F z ξ) (ball c R))
    {M : X → ℝ} (hM : Integrable M μ)
    (hb : ∀ᵐ ξ ∂μ, ∀ z ∈ ball c R, ‖F z ξ‖ ≤ M ξ) :
    HasFDerivAt (fun z => ∫ ξ, F z ξ ∂μ)
      (∫ ξ, fderiv ℂ (fun z => F z ξ) c ∂μ) c := by
  have hdc : ∀ᵐ ξ ∂μ, DifferentiableAt ℂ (fun z => F z ξ) c := by
    filter_upwards [hd] with ξ hξ
    exact hξ.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hR))
  have hmc := aestronglyMeasurable_fderiv_of_point_samples hm hdc
  have hi : Integrable (F c) μ := by
    apply hM.mono' (hm c)
    filter_upwards [hb] with ξ hξ
    exact hξ c (mem_ball_self hR)
  have hbound : Integrable (fun ξ => 2 * M ξ / R) μ := by
    convert hM.const_mul (2 / R) using 1
    funext ξ
    ring
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun z ξ => fderiv ℂ (fun w => F w ξ) z)
    (show 0 < R / 4 by linarith) (Eventually.of_forall hm) hi hmc _ hbound
  · filter_upwards [hd] with ξ hξ
    intro z hz
    have hzR : z ∈ ball c R := ball_subset_ball (by linarith) hz
    exact (hξ.differentiableAt (isOpen_ball.mem_nhds hzR)).hasFDerivAt
  · filter_upwards [hd, hb] with ξ hξ hξb
    have hM0 : 0 ≤ M ξ := (norm_nonneg (F c ξ)).trans (hξb c (mem_ball_self hR))
    intro z hz
    exact common_bound_fderiv_norm hR hM0 hξ hξb hz

/-- Joint complex Fréchet differentiability of a graph integral on its actual
    open domain from local common pointwise L1 majorants. Outside the domain
    the integrand is extended by zero, rather than assuming measurability there. -/
theorem holomorphy_from_local_graph_majorants
    {H X : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
    [MeasurableSpace X] {μ : Measure X} {F : H → X → ℂ} {Ω : Set H}
    (hΩ : IsOpen Ω) (hm : ∀ z ∈ Ω, AEStronglyMeasurable (F z) μ)
    (hd : ∀ᵐ ξ ∂μ, DifferentiableOn ℂ (fun z => F z ξ) Ω)
    (hb : ∀ c ∈ Ω, ∃ R > 0, ball c R ⊆ Ω ∧ ∃ M : X → ℝ,
      Integrable M μ ∧ ∀ᵐ ξ ∂μ, ∀ z ∈ ball c R, ‖F z ξ‖ ≤ M ξ) :
    DifferentiableOn ℂ (fun z => ∫ ξ, F z ξ ∂μ) Ω := by
  classical
  let G : H → X → ℂ := fun z ξ => if z ∈ Ω then F z ξ else 0
  have hmG : ∀ z, AEStronglyMeasurable (G z) μ := by
    intro z
    by_cases hz : z ∈ Ω
    · simpa only [G, if_pos hz] using hm z hz
    · simp only [G, if_neg hz]
      exact aestronglyMeasurable_const
  intro c hc
  obtain ⟨R, hR, hball, M, hM, hbM⟩ := hb c hc
  have hdG : ∀ᵐ ξ ∂μ, DifferentiableOn ℂ (fun z => G z ξ) (ball c R) := by
    filter_upwards [hd] with ξ hξ
    apply (hξ.mono hball).congr
    intro z hz
    simp [G, hball hz]
  have hbG : ∀ᵐ ξ ∂μ, ∀ z ∈ ball c R, ‖G z ξ‖ ≤ M ξ := by
    filter_upwards [hbM] with ξ hξ
    intro z hz
    simpa only [G, if_pos (hball hz)] using hξ z hz
  have hG := graph_integral_hasFDerivAt_of_common_majorant hR hmG hdG hM hbG
  have heq : (fun z => ∫ ξ, F z ξ ∂μ) =ᶠ[𝓝 c] (fun z => ∫ ξ, G z ξ ∂μ) := by
    filter_upwards [hΩ.mem_nhds hc] with z hz
    simp only [G, if_pos hz]
  exact (hG.differentiableAt.congr_of_eventuallyEq heq).differentiableWithinAt

/-- Compact-domain formulation of the source common-majorant theorem. A
    finite-dimensional complex Euclidean momentum space is proper. -/
theorem holomorphy_from_compact_graph_majorants
    {H X : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
    [ProperSpace H] [MeasurableSpace X] {μ : Measure X} {F : H → X → ℂ} {Ω : Set H}
    (hΩ : IsOpen Ω) (hm : ∀ z ∈ Ω, AEStronglyMeasurable (F z) μ)
    (hd : ∀ᵐ ξ ∂μ, DifferentiableOn ℂ (fun z => F z ξ) Ω)
    (hb : ∀ K : Set H, IsCompact K → K ⊆ Ω → ∃ M : X → ℝ,
      Integrable M μ ∧ ∀ᵐ ξ ∂μ, ∀ z ∈ K, ‖F z ξ‖ ≤ M ξ) :
    DifferentiableOn ℂ (fun z => ∫ ξ, F z ξ ∂μ) Ω := by
  apply holomorphy_from_local_graph_majorants hΩ hm hd
  intro c hc
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hΩ c hc
  have hclosed : closedBall c (ε / 2) ⊆ Ω :=
    (closedBall_subset_ball (by linarith)).trans hsub
  obtain ⟨M, hM, hMb⟩ := hb (closedBall c (ε / 2)) (isCompact_closedBall _ _) hclosed
  refine ⟨ε / 2, by linarith, ball_subset_closedBall.trans hclosed, M, hM, ?_⟩
  filter_upwards [hMb] with ξ hξ
  exact fun z hz => hξ z (ball_subset_closedBall hz)

/-- On-domain differentiation commutes with graph integration, without making
    any assertion about the integrand outside the admitted ball. -/
theorem graph_integral_derivative_commutes
    {H X : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
    [MeasurableSpace X] {μ : Measure X} {F : H → X → ℂ} {c : H} {R : ℝ}
    (hR : 0 < R) (hm : ∀ z ∈ ball c R, AEStronglyMeasurable (F z) μ)
    (hd : ∀ᵐ ξ ∂μ, DifferentiableOn ℂ (fun z => F z ξ) (ball c R))
    {M : X → ℝ} (hM : Integrable M μ)
    (hb : ∀ᵐ ξ ∂μ, ∀ z ∈ ball c R, ‖F z ξ‖ ≤ M ξ) :
    HasFDerivAt (fun z => ∫ ξ, F z ξ ∂μ)
      (∫ ξ, fderiv ℂ (fun z => F z ξ) c ∂μ) c := by
  classical
  let G : H → X → ℂ := fun z ξ => if z ∈ ball c R then F z ξ else 0
  have hmG : ∀ z, AEStronglyMeasurable (G z) μ := by
    intro z
    by_cases hz : z ∈ ball c R
    · simpa only [G, if_pos hz] using hm z hz
    · simp only [G, if_neg hz]
      exact aestronglyMeasurable_const
  have hdG : ∀ᵐ ξ ∂μ, DifferentiableOn ℂ (fun z => G z ξ) (ball c R) := by
    filter_upwards [hd] with ξ hξ
    apply hξ.congr
    intro z hz
    simp only [G, if_pos hz]
  have hbG : ∀ᵐ ξ ∂μ, ∀ z ∈ ball c R, ‖G z ξ‖ ≤ M ξ := by
    filter_upwards [hb] with ξ hξ
    intro z hz
    simpa only [G, if_pos hz] using hξ z hz
  have hg := graph_integral_hasFDerivAt_of_common_majorant hR hmG hdG hM hbG
  have heq (ξ : X) : (fun z => G z ξ) =ᶠ[𝓝 c] (fun z => F z ξ) := by
    filter_upwards [ball_mem_nhds c hR] with z hz
    simp only [G, if_pos hz]
  have hder : (fun ξ => fderiv ℂ (fun z => G z ξ) c) =
      (fun ξ => fderiv ℂ (fun z => F z ξ) c) := by
    funext ξ
    exact (heq ξ).fderiv_eq
  rw [hder] at hg
  apply hg.congr_of_eventuallyEq
  filter_upwards [ball_mem_nhds c hR] with z hz
  simp only [G, if_pos hz]

end UV
