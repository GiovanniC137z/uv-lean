import UV.VerifyCurvatureGraphBounds

/-! Exact reconstruction of a curvature configuration from a matched
edge assignment and the inverse reconstruction from elementary slots. -/

noncomputable section

open MeasureTheory Filter Real
open scoped BigOperators Topology

namespace UV.VerifyCurvatureReindex

open UV.NextCurvatureLaw UV.AdvanceCurvatureWick UV.AdvanceCurvatureVertex
open UV.VerifyCurvatureExpansion UV.VerifyCurvatureRouting UV.VerifyCurvatureGraphBounds
open UV.FurtherCurvatureGraph UV.FurtherCurvatureShell UV.FurtherCurvatureDeterminant

abbrev RouteAssignment (n r I : ℕ) := (Fin I → MeanZeroMode) × (EdgeColors n I × (Fin r → Fin n))

def graphMatched {n r p I J : ℕ} (g : Incidence r p I J) (probes : Fin p → ModeSlot n)
    (v : Fin r → VertexChoice n) : Prop :=
  ∀ e, configuredSlot v probes (g.ends (e,0)) = configuredSlot v probes (g.ends (e,1))

def collectAssignment {n r p I J : ℕ} (g : Incidence r p I J) (probes : Fin p → ModeSlot n)
    (v : Fin r → VertexChoice n) : RouteAssignment n r I :=
  let slot := fun i => configuredSlot v probes (g.ends (.inl i,0))
  (fun i => (slot i).1, (fun i => (slot i).2, fun z => (v z).1))

def rebuildAssignment {n r p I J : ℕ} (g : Incidence r p I J) (probes : Fin p → ModeSlot n)
    (ρ : RouteAssignment n r I) : Fin r → VertexChoice n :=
  routedVertex g probes ρ.1 ρ.2.1 ρ.2.2

private theorem configured_slot_field {n r p : ℕ} (v : Fin r → VertexChoice n)
    (probes : Fin p → ModeSlot n) (z : Fin r) (x y : Fin 2) :
    (configuredSlot v probes (.inl (z,(x,y)))).2.1 = y := by
  fin_cases y <;> simp [configuredSlot, leftSlot, rightSlot]

private theorem configured_routedSlot {n r p I J : ℕ} (g : Incidence r p I J)
    (probes : Fin p → ModeSlot n) (ρ : RouteAssignment n r I)
    (hρ : routingConsistent g probes ρ.1 ρ.2.1) :
    configuredSlot (rebuildAssignment g probes ρ) probes = routedSlot g probes ρ.1 ρ.2.1 := by
  funext e
  rcases e with ⟨z,x,y⟩ | p
  · have hx : x = 0 ∨ x = 1 := by omega
    have hy : y = 0 ∨ y = 1 := by omega
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    all_goals
      simp [configuredSlot, rebuildAssignment, routedVertex, leftSlot, rightSlot]
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · exact (hρ.1 _ _ _).symm
        · rfl
  · exact (hρ.2 p).symm

private theorem matching_of_assignment {n r p I J : ℕ} (g : Incidence r p I J)
    (probes : Fin p → ModeSlot n) (ρ : RouteAssignment n r I)
    (hρ : routingConsistent g probes ρ.1 ρ.2.1) :
    graphMatched g probes (rebuildAssignment g probes ρ) := by
  intro e
  rw [configured_routedSlot g probes ρ hρ, routedSlot_end, routedSlot_end]

private theorem consistent_of_matching {n r p I J : ℕ} (g : Incidence r p I J)
    (probes : Fin p → ModeSlot n) (v : Fin r → VertexChoice n) (hm : graphMatched g probes v) :
    routingConsistent g probes (collectAssignment g probes v).1 (collectAssignment g probes v).2.1 := by
  unfold routingConsistent
  have h := routedSlot_recovers_matched_configuration g v probes hm
  change routedSlot g probes (collectAssignment g probes v).1 (collectAssignment g probes v).2.1 =
    configuredSlot v probes at h
  rw [h]
  exact ⟨configured_slot_field v probes, fun _ => rfl⟩

private theorem rebuild_collect {n r p I J : ℕ} (g : Incidence r p I J)
    (probes : Fin p → ModeSlot n) (v : Fin r → VertexChoice n) (hm : graphMatched g probes v) :
    rebuildAssignment g probes (collectAssignment g probes v) = v := by
  have h := routedSlot_recovers_matched_configuration g v probes hm
  change routedSlot g probes (collectAssignment g probes v).1 (collectAssignment g probes v).2.1 =
    configuredSlot v probes at h
  have hp (z : Fin r) (i j : Fin 2) :
      routedSlot g probes (collectAssignment g probes v).1 (collectAssignment g probes v).2.1
        (.inl (z,(i,j))) = configuredSlot v probes (.inl (z,(i,j))) := congrFun h _
  funext z
  unfold rebuildAssignment routedVertex
  simp only [hp]
  simp [configuredSlot, leftSlot, rightSlot, collectAssignment]

private theorem collect_rebuild {n r p I J : ℕ} (g : Incidence r p I J)
    (probes : Fin p → ModeSlot n) (ρ : RouteAssignment n r I)
    (hρ : routingConsistent g probes ρ.1 ρ.2.1) :
    collectAssignment g probes (rebuildAssignment g probes ρ) = ρ := by
  unfold collectAssignment
  rw [configured_routedSlot g probes ρ hρ]
  simp only [routedSlot_end, edgeSlot, rebuildAssignment, routedVertex]

/-- Every matching of the literal vertex configurations is equivalent to
the internal signed-mode and color assignments with prescribed probes. -/
def matchedAssignmentEquiv {n r p I J : ℕ} (g : Incidence r p I J) (probes : Fin p → ModeSlot n) :
    {v : Fin r → VertexChoice n // graphMatched g probes v} ≃
      {ρ : RouteAssignment n r I // routingConsistent g probes ρ.1 ρ.2.1} where
  toFun v := ⟨collectAssignment g probes v.1, consistent_of_matching g probes v.1 v.2⟩
  invFun ρ := ⟨rebuildAssignment g probes ρ.1, matching_of_assignment g probes ρ.1 ρ.2⟩
  left_inv v := Subtype.ext (rebuild_collect g probes v.1 v.2)
  right_inv ρ := Subtype.ext (collect_rebuild g probes ρ.1 ρ.2)

/-- A fixed incidence matching uses the exact covariance at every pair
of positions. Inconsistent original configurations contribute zero. -/
def configuredGraphTerm {n r p I J : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (g : Incidence r p I J) (probes : Fin p → ModeSlot n) (ℓ : ℝ)
    (v : Fin r → VertexChoice n) : ℝ :=
  (∏ z, vertexCoefficient B (v z)) *
    ∏ e : Fin I ⊕ Fin J, occurrenceCovariance ℓ
      (isInteraction (g.ends (e,0)), configuredSlot v probes (g.ends (e,0)))
      (isInteraction (g.ends (e,1)), configuredSlot v probes (g.ends (e,1)))

theorem configuredGraphTerm_zero_of_mismatch {n r p I J : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (g : Incidence r p I J) (probes : Fin p → ModeSlot n) (ℓ : ℝ)
    (v : Fin r → VertexChoice n) (hm : ¬graphMatched g probes v) :
    configuredGraphTerm B g probes ℓ v = 0 := by
  classical
  unfold graphMatched at hm
  push_neg at hm
  obtain ⟨e,he⟩ := hm
  unfold configuredGraphTerm
  rw [Finset.prod_eq_zero (Finset.mem_univ e), mul_zero]
  simp only [occurrence_covariance_eq, if_neg he]

/-- The matched configuration weight agrees term by term with the routed
weight, before the common-depth determinant and momentum sum. -/
theorem configuredGraphTerm_eq_routed_of_match {n r p I J : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (g : Incidence r p I J) (probes : Fin p → ModeSlot n) (ℓ : ℝ)
    (v : Fin r → VertexChoice n) (hm : graphMatched g probes v) :
    let ρ := collectAssignment g probes v
    configuredGraphTerm B g probes ℓ v = routedWickTerm B g probes ℓ ρ.1 ρ.2.1 ρ.2.2 := by
  classical
  dsimp only
  unfold configuredGraphTerm routedWickTerm vertexProduct
  rw [if_pos (consistent_of_matching g probes v hm)]
  have hV := rebuild_collect g probes v hm
  change routedVertex g probes (collectAssignment g probes v).1 (collectAssignment g probes v).2.1
    (collectAssignment g probes v).2.2 = v at hV
  rw [hV]
  have h := routedSlot_recovers_matched_configuration g v probes hm
  change routedSlot g probes (collectAssignment g probes v).1 (collectAssignment g probes v).2.1 =
    configuredSlot v probes at h
  simp only [routedOccurrence, h]

private def configurationFinset (n r : ℕ) (Λ : ℝ) : Finset (Fin r → VertexChoice n) :=
  Fintype.piFinset fun _ => sphericalVertexChoices n Λ

private def routingFinset (n r I : ℕ) (Λ : ℝ) : Finset (RouteAssignment n r I) :=
  (Fintype.piFinset fun _ : Fin I => UV.ExtendCurvaturePotential.retainedModes Λ) ×ˢ
    ((Finset.univ : Finset (EdgeColors n I)) ×ˢ (Finset.univ : Finset (Fin r → Fin n)))

open UV.ExtendCurvaturePotential (retainedModes)

private theorem configured_vertex_mem {n r p : ℕ} (v : Fin r → VertexChoice n)
    (Λ : ℝ) (probes : Fin p → ModeSlot n) (z : Fin r) :
    v z ∈ sphericalVertexChoices n Λ ↔
      ∀ x y : Fin 2, (configuredSlot v probes (.inl (z,(x,y)))).1 ∈ retainedModes Λ := by
  simp only [sphericalVertexChoices, vertexLegs, Finset.mem_product, Finset.mem_univ, true_and]
  constructor
  · intro h x y
    have hx : x = 0 ∨ x = 1 := by omega
    have hy : y = 0 ∨ y = 1 := by omega
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · simpa [configuredSlot, leftSlot] using h.1.1
    · simpa [configuredSlot, rightSlot] using h.1.2
    · simpa [configuredSlot, leftSlot] using h.2.1
    · simpa [configuredSlot, rightSlot] using h.2.2
  · intro h
    exact ⟨⟨h 0 0,h 0 1⟩,⟨h 1 0,h 1 1⟩⟩

private theorem collect_mem_routing {n r p I J : ℕ} (g : Incidence r p I J)
    (probes : Fin p → ModeSlot n) (Λ : ℝ) (v : Fin r → VertexChoice n)
    (hv : v ∈ configurationFinset n r Λ) : collectAssignment g probes v ∈ routingFinset n r I Λ := by
  simp only [routingFinset, Finset.mem_product, Finset.mem_univ, and_true, Fintype.mem_piFinset]
  intro i
  have hg := g.internalInteraction i 0
  change (configuredSlot v probes (g.ends (.inl i,0))).1 ∈ retainedModes Λ
  cases h : g.ends (.inl i,0) with
  | inl u =>
    obtain ⟨z,x,y⟩ := u
    exact (configured_vertex_mem v Λ probes z).1 (Fintype.mem_piFinset.mp hv z) x y
  | inr q => simp [h,isInteraction] at hg

private theorem rebuild_mem_configuration {n r p I J : ℕ} (g : Incidence r p I J)
    (probes : Fin p → ModeSlot n) (Λ : ℝ) (ρ : RouteAssignment n r I)
    (hP : ∀ p, (probes p).1 ∈ retainedModes Λ) (hρ : ρ ∈ routingFinset n r I Λ)
    (hc : routingConsistent g probes ρ.1 ρ.2.1) :
    rebuildAssignment g probes ρ ∈ configurationFinset n r Λ := by
  have hA : ∀ i, ρ.1 i ∈ retainedModes Λ := by
    simpa only [routingFinset, Finset.mem_product, Finset.mem_univ, and_true, Fintype.mem_piFinset]
      using hρ
  apply Fintype.mem_piFinset.mpr
  intro z
  apply (configured_vertex_mem (rebuildAssignment g probes ρ) Λ probes z).2
  intro x y
  rw [configured_routedSlot g probes ρ hc]
  unfold routedSlot
  cases (g.ends.symm (.inl (z,(x,y)))).1 with
  | inl i => exact hA i
  | inr j => exact hP _

private theorem configuration_sum_reindex {n r p I J : ℕ}
    (B : Fin n → Fin n → Fin n → ℝ) (g : Incidence r p I J) (probes : Fin p → ModeSlot n)
    (Λ ℓ : ℝ) (hP : ∀ p, (probes p).1 ∈ retainedModes Λ) :
    (∑ v ∈ configurationFinset n r Λ, configuredGraphTerm B g probes ℓ v) =
      ∑ ρ ∈ routingFinset n r I Λ, routedWickTerm B g probes ℓ ρ.1 ρ.2.1 ρ.2.2 := by
  classical
  let s := configurationFinset n r Λ
  let t := routingFinset n r I Λ
  let M := graphMatched g probes
  let C (ρ : RouteAssignment n r I) := routingConsistent g probes ρ.1 ρ.2.1
  let G := configuredGraphTerm B g probes ℓ
  let H (ρ : RouteAssignment n r I) := routedWickTerm B g probes ℓ ρ.1 ρ.2.1 ρ.2.2
  have hGs : (∑ v ∈ s.filter M, G v) = ∑ v ∈ s, G v := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro v _ hvm
    exact configuredGraphTerm_zero_of_mismatch B g probes ℓ v (fun hm => hvm (Finset.mem_filter.mpr ⟨‹v ∈ s›,hm⟩))
  have hHt : (∑ ρ ∈ t.filter C, H ρ) = ∑ ρ ∈ t, H ρ := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro ρ _ hrc
    have hn : ¬ C ρ := fun h => hrc (Finset.mem_filter.mpr ⟨‹ρ ∈ t›,h⟩)
    unfold H routedWickTerm vertexProduct
    rw [if_neg hn, zero_mul]
  change (∑ v ∈ s, G v) = ∑ ρ ∈ t, H ρ
  rw [← hGs, ← hHt]
  apply Finset.sum_bij' (fun v _ => collectAssignment g probes v)
      (fun ρ _ => rebuildAssignment g probes ρ)
  · intro v hv
    obtain ⟨hsv,hm⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨collect_mem_routing g probes Λ v hsv, consistent_of_matching g probes v hm⟩
  · intro ρ hρ
    obtain ⟨htρ,hc⟩ := Finset.mem_filter.mp hρ
    exact Finset.mem_filter.mpr ⟨rebuild_mem_configuration g probes Λ ρ hP htρ hc,
      matching_of_assignment g probes ρ hc⟩
  · intro v hv
    exact rebuild_collect g probes v (Finset.mem_filter.mp hv).2
  · intro ρ hρ
    exact collect_rebuild g probes ρ (Finset.mem_filter.mp hρ).2
  · intro v hv
    exact configuredGraphTerm_eq_routed_of_match B g probes ℓ v (Finset.mem_filter.mp hv).2

/-- Exact equality from the literal spherical vertex-configuration sum to
one independent signed momentum per internal edge, retaining the full
color multiplicities and the one common determinant. -/
theorem configured_sphericalGraph_eq_routed {n r p I J : ℕ}
    (B : Fin n → Fin n → Fin n → ℝ) (g : Incidence r p I J) (probes : Fin p → ModeSlot n)
    (Λ ℓ : ℝ) (hP : ∀ p, (probes p).1 ∈ retainedModes Λ) :
    sphericalDeterminant n Λ ℓ *
        (∑ v ∈ Fintype.piFinset (fun _ : Fin r => sphericalVertexChoices n Λ),
          configuredGraphTerm B g probes ℓ v) = routedSphericalGraph B g probes Λ ℓ := by
  classical
  change sphericalDeterminant n Λ ℓ *
    (∑ v ∈ configurationFinset n r Λ, configuredGraphTerm B g probes ℓ v) = _
  rw [configuration_sum_reindex B g probes Λ ℓ hP]
  unfold routedSphericalGraph routingFinset
  simp only [Finset.sum_product]
  apply congrArg (sphericalDeterminant n Λ ℓ * ·)
  apply Finset.sum_bij (fun (a : Fin I → MeanZeroMode) _ => fun i => (a i).1)
  · intro a ha
    exact Fintype.mem_piFinset.mpr fun i => Finset.mem_subtype.mp (Fintype.mem_piFinset.mp ha i)
  · intro a _ b _ hab
    funext i
    exact Subtype.ext (congrFun hab i)
  · intro a ha
    have hn (i : Fin I) := (mem_sphericalModes.mp (Fintype.mem_piFinset.mp ha i)).1
    let b (i : Fin I) : MeanZeroMode := ⟨a i, hn i⟩
    exact ⟨b, Fintype.mem_piFinset.mpr (fun i => Finset.mem_subtype.mpr (Fintype.mem_piFinset.mp ha i)), rfl⟩
  · intro a _
    simp only [dif_pos (fun i => (a i).2)]

end UV.VerifyCurvatureReindex
