import UV.CurvatureWickIncidence

/-! The graph series of the literal curvature action at fixed order.
Project elementary probes with the same sphere as the interacting modes.
A probe omitted by the cutoff makes its entire coefficient zero. -/

noncomputable section

namespace UV.CurvatureWick

open Filter MeasureTheory Set
open scoped Topology

set_option maxHeartbeats 800000
open UV.VerifyCurvatureRouting UV.VerifyCurvatureReindex UV.VerifyCurvatureExpansion
open UV.VerifyCurvatureGraphBounds UV.AdvanceCurvatureWick UV.NextCurvatureLaw
open UV.FurtherCurvatureGraph UV.NextCurvatureFull UV.FurtherCurvatureDeterminant
open UV.ExtendCurvaturePotential UV.AdvanceCurvatureEnvelope

abbrev sourceMatchings (r p : ℕ) := matchings (sourcePositions r p).length (sourcePositions r p)

def sourceRealization (r p : ℕ) (g : Fin (sourceMatchings r p).length) :
    Realization ((sourceMatchings r p).get g) :=
  realizeMatching (List.get_mem _ _)

def projectedProbeMonomial {n p : ℕ} (Λ ℓ : ℝ) (X : ModeSlot n → ℝ) (probes : Fin p → ModeSlot n) : ℝ :=
  ∏ j : Fin p, if (probes j).1 ∈ retainedModes Λ then depthRescale ℓ X (probes j) else 0

theorem projected_probe_product {n p : ℕ} (Λ ℓ : ℝ) (X : ModeSlot n → ℝ) (probes : Fin p → ModeSlot n) :
    projectedProbeMonomial Λ ℓ X probes =
      if ∀ j, (probes j).1 ∈ retainedModes Λ then rawProbeMonomial ℓ X (List.ofFn probes) else 0 := by
  classical
  by_cases h : ∀ j, (probes j).1 ∈ retainedModes Λ
  · simp [projectedProbeMonomial,h,rawProbeMonomial,List.map_ofFn,List.prod_ofFn,Function.comp_def]
  · obtain ⟨j,hj⟩ := not_forall.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

def projectedGraph {n r p : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (probes : Fin p → ModeSlot n)
    (Λ ℓ : ℝ) (i : Fin (sourceMatchings r p).length) : ℝ :=
  if ∀ j, (probes j).1 ∈ retainedModes Λ then
    routedSphericalGraph B (sourceRealization r p i).graph probes Λ ℓ else 0

private theorem wick_expansion_as_fin_sum {n r p : ℕ} (v : Fin r → VertexChoice n)
    (probes : Fin p → ModeSlot n) (ℓ : ℝ) :
    let w := sourceOccurrences v (List.ofFn probes)
    osWickMoment (occurrenceCovariance ℓ) w.length w =
      ∑ i : Fin (sourceMatchings r p).length, matchingWeight
        (fun x y => occurrenceCovariance ℓ (assignedOccurrence v probes x) (assignedOccurrence v probes y))
        ((sourceMatchings r p).get i) := by
  dsimp only
  rw [positional_wick_expansion]
  let W := matchingWeight (fun x y => occurrenceCovariance ℓ (assignedOccurrence v probes x) (assignedOccurrence v probes y))
  change ((sourceMatchings r p).map W).sum = _
  have he := congrArg (List.map W) (List.ofFn_get (sourceMatchings r p))
  rw [← he,List.map_ofFn,List.sum_ofFn]
  rfl

/-- Every summand is built from a recursive Wick partner choice of the
actual quartic action. All fixed elementary modes are projected on the
same sphere. The equality includes vacuum graphs and repeated probes. -/
theorem cutoff_action_equals_graph_sum {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (r : ℕ) {p : ℕ} (probes : Fin p → ModeSlot n) (Λ ℓ : ℝ) :
    sphericalDeterminant n Λ ℓ *
      (∫ X, cutoffBracketPotential B Λ ℓ X ^ r * projectedProbeMonomial Λ ℓ X probes ∂commonGaussian n) =
    ∑ i, projectedGraph B probes Λ ℓ (r := r) i := by
  classical
  by_cases hp : ∀ j, (probes j).1 ∈ retainedModes Λ
  · simp only [projected_probe_product,projectedGraph,if_pos hp]
    rw [(cutoff_power_probe_wick B Λ ℓ r (List.ofFn probes)).2]
    let S := Fintype.piFinset (fun _ : Fin r => sphericalVertexChoices n Λ)
    let T (v : Fin r → VertexChoice n) (i : Fin (sourceMatchings r p).length) :=
      configuredGraphTerm B (sourceRealization r p i).graph probes ℓ v
    have he (v : Fin r → VertexChoice n) :
        (∏ z, vertexCoefficient B (v z)) * osWickMoment (occurrenceCovariance ℓ)
          (sourceOccurrences v (List.ofFn probes)).length (sourceOccurrences v (List.ofFn probes)) = ∑ i, T v i := by
      rw [wick_expansion_as_fin_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => matching_weight_is_configured_term (sourceRealization r p i) B v probes ℓ
    simp_rw [he]
    change sphericalDeterminant n Λ ℓ * (∑ v ∈ S, ∑ i, T v i) = _
    rw [Finset.sum_comm,Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => configured_sphericalGraph_eq_routed B (sourceRealization r p i).graph probes Λ ℓ hp
  · simp [projected_probe_product,projectedGraph,hp]

theorem projected_graph_limit {n r p : ℕ} (hn : 0 < n) (B : Fin n → Fin n → Fin n → ℝ)
    (probes : Fin p → ModeSlot n) (i : Fin (sourceMatchings r p).length)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ) :
    let g := (sourceRealization r p i).graph
    Integrable (fun ℓ => fullGraphSum n ℓ (routedCoefficient B g probes ℓ)) μ ∧
      Tendsto (fun Λ : ℝ => ∫ ℓ, projectedGraph B probes Λ ℓ i ∂μ) atTop
        (𝓝 (∫ ℓ, fullGraphSum n ℓ (routedCoefficient B g probes ℓ) ∂μ)) := by
  intro g
  obtain ⟨hi,hlim⟩ := integrated_routedGraph_limit hn B g probes μ hμ
  have he : ∀ᶠ Λ : ℝ in atTop, ∀ j, (probes j).1 ∈ retainedModes Λ := by
    rw [eventually_all]
    exact fun j => (eventually_ge_atTop _).mono fun _ h => (mem_retainedModes _ _).mpr h
  exact ⟨hi,hlim.congr' (he.mono fun Λ hΛ => by simp only [projectedGraph,if_pos hΛ,g])⟩

def projectedAbsoluteTail {n r p I J : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (g : Incidence r p I J)
    (probes : Fin p → ModeSlot n) (Λ M ℓ : ℝ) : ℝ :=
  if ∀ j, (probes j).1 ∈ retainedModes Λ then sphericalTail n Λ ℓ M (routedCoefficient B g probes ℓ) else 0

/-- Absolute tails of each literal graph, with one common depth law.
A sphere missing any external probe gives zero, uniformly down to cutoff zero. -/
theorem wick_graph_absolute_tails {n r p : ℕ} (hn : 0 < n) (B : Fin n → Fin n → Fin n → ℝ)
    (probes : Fin p → ModeSlot n) (i : Fin (sourceMatchings r p).length)
    {s : ℝ} (hs : 0 ≤ s) (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ) :
    let g := (sourceRealization r p i).graph
    let coeff := routedCoefficient B g probes
    ∃ C ≥ (0:ℝ), ∀ M > (0 : ℝ),
      Integrable (fun ℓ => fullAbsoluteTail n ℓ M (coeff ℓ)) μ ∧
      (∫ ℓ, fullAbsoluteTail n ℓ M (coeff ℓ) ∂μ) ≤ C * M^(-s) ∧
      fullAbsoluteTail n 0 M (coeff 0) = 0 ∧
      ∀ Λ ≥ (0:ℝ), Integrable (projectedAbsoluteTail B g probes Λ M) μ ∧
        (∫ ℓ, projectedAbsoluteTail B g probes Λ M ℓ ∂μ) ≤ C * M^(-s) := by
  intro g coeff
  obtain ⟨A,hA,ha⟩ := integrated_routedGraph_absolute_tail hn B g probes hs μ hμ
  obtain ⟨B',hB,hb⟩ := integrated_routedSphericalGraph_tail_uniform hn B g probes hs μ hμ
  refine ⟨max A B',hA.trans (le_max_left _ _), fun M hM => ?_⟩
  obtain ⟨hi,hle,_⟩ := ha hM
  have hpow := (Real.rpow_pos_of_pos hM (-s)).le
  refine ⟨hi,hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow),by simp [fullAbsoluteTail,fullGraphSum],fun Λ hΛ => ?_⟩
  by_cases h : ∀ j, (probes j).1 ∈ retainedModes Λ
  · obtain ⟨hi',hle'⟩ := hb hΛ hM
    have he : projectedAbsoluteTail B g probes Λ M = fun ℓ => sphericalTail n Λ ℓ M (coeff ℓ) := funext (fun ℓ => if_pos h)
    rw [he]
    exact ⟨hi',hle'.trans (mul_le_mul_of_nonneg_right (le_max_right A B') hpow)⟩
  · have he : projectedAbsoluteTail B g probes Λ M = fun _ => 0 := funext (fun _ => if_neg h)
    rw [he,integral_zero]
    exact ⟨integrable_zero _ _ _,mul_nonneg (hA.trans (le_max_left A B')) hpow⟩

end UV.CurvatureWick
