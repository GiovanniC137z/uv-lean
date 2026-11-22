import UV.VerifyCurvatureExpansion
import UV.NextCurvatureFull

/-! A fixed curvature Wick graph is an incidence bijection from the two
ends of its lines to the literal interaction and elementary probe slots.
Its internal lines carry independent signed momenta. -/

noncomputable section

open MeasureTheory Filter Real
open scoped BigOperators Topology

namespace UV.VerifyCurvatureRouting

open UV.NextCurvatureLaw UV.AdvanceCurvatureWick UV.AdvanceCurvatureVertex
open UV.VerifyCurvatureExpansion UV.FurtherCurvatureLine UV.FurtherCurvatureGraph
open UV.NextCurvatureFull UV.FurtherCurvatureShell

abbrev EndPosition (r p : ℕ) := (Fin r × (Fin 2 × Fin 2)) ⊕ Fin p

def isInteraction {r p : ℕ} : EndPosition r p → Bool
  | .inl _ => true
  | .inr _ => false

/-- Partition a fixed matching into internal edges and edges with a fixed
probe. The slot marked by a probe on each noninternal edge supplies its
fixed signed momentum, real field, and orthonormal color. -/
structure Incidence (r p I J : ℕ) where
  ends : ((Fin I ⊕ Fin J) × Fin 2) ≃ EndPosition r p
  internalInteraction : ∀ i b, isInteraction (ends (.inl i,b)) = true
  probeAt : Fin J → Fin p
  probeSide : Fin J → Fin 2
  probeIdentity : ∀ j, ends (.inr j, probeSide j) = .inr (probeAt j)

abbrev EdgeColors (n I : ℕ) := Fin I → Fin 2 × Fin n

def edgeSlot {n r p I J : ℕ} (g : Incidence r p I J) (probes : Fin p → ModeSlot n)
    (a : Fin I → MeanZeroMode) (colors : EdgeColors n I) : Fin I ⊕ Fin J → ModeSlot n
  | .inl i => (a i, colors i)
  | .inr j => probes (g.probeAt j)

def routedSlot {n r p I J : ℕ} (g : Incidence r p I J) (probes : Fin p → ModeSlot n)
    (a : Fin I → MeanZeroMode) (colors : EdgeColors n I) (e : EndPosition r p) : ModeSlot n :=
  edgeSlot g probes a colors (g.ends.symm e).1

@[simp] theorem routedSlot_end {n r p I J : ℕ} (g : Incidence r p I J)
    (probes : Fin p → ModeSlot n) (a : Fin I → MeanZeroMode) (colors : EdgeColors n I)
    (e : Fin I ⊕ Fin J) (b : Fin 2) :
    routedSlot g probes a colors (g.ends (e,b)) = edgeSlot g probes a colors e := by
  simp [routedSlot]

def routedVertex {n r p I J : ℕ} (g : Incidence r p I J) (probes : Fin p → ModeSlot n)
    (a : Fin I → MeanZeroMode) (colors : EdgeColors n I) (outputs : Fin r → Fin n)
    (v : Fin r) : VertexChoice n :=
  let slot := fun x y => routedSlot g probes a colors (.inl (v,(x,y)))
  let leg := fun x => (((slot x 0).2.2,(slot x 0).1), ((slot x 1).2.2,(slot x 1).1))
  (outputs v,(leg 0,leg 1))

def routingConsistent {n r p I J : ℕ} (g : Incidence r p I J) (probes : Fin p → ModeSlot n)
    (a : Fin I → MeanZeroMode) (colors : EdgeColors n I) : Prop :=
  (∀ v x y, (routedSlot g probes a colors (.inl (v,(x,y)))).2.1 = y) ∧
    (∀ z, routedSlot g probes a colors (.inr z) = probes z)

def routedOccurrence {n r p I J : ℕ} (g : Incidence r p I J) (probes : Fin p → ModeSlot n)
    (a : Fin I → MeanZeroMode) (colors : EdgeColors n I)
    (e : Fin I ⊕ Fin J) (b : Fin 2) : Occurrence n :=
  (isInteraction (g.ends (e,b)), routedSlot g probes a colors (g.ends (e,b)))

theorem external_not_internal {r p I J : ℕ} (g : Incidence r p I J) (j : Fin J) :
    (isInteraction (g.ends (.inr j,0)) && isInteraction (g.ends (.inr j,1))) = false := by
  have h := congrArg isInteraction (g.probeIdentity j)
  change isInteraction (g.ends (.inr j, g.probeSide j)) = false at h
  rcases Fin.eq_zero_or_eq_succ (g.probeSide j) with h0 | ⟨b,hb⟩
  · simp [h0] at h
    simp [h]
  · have hb' : (g.probeSide j) = 1 := by
      have he : b = 0 := Subsingleton.elim _ _
      rw [he] at hb
      exact hb
    simp [hb'] at h
    simp [h]

def externalLine {n r p I J : ℕ} (g : Incidence r p I J) (probes : Fin p → ModeSlot n)
    (ℓ : ℝ) (j : Fin J) : ℝ :=
  occurrenceLine ℓ (probes (g.probeAt j)).1 (isInteraction (g.ends (.inr j,0)))
    (isInteraction (g.ends (.inr j,1)))

private theorem product_edge_covariances {n r p I J : ℕ} (g : Incidence r p I J)
    (probes : Fin p → ModeSlot n) (a : Fin I → MeanZeroMode) (colors : EdgeColors n I) (ℓ : ℝ) :
    (∏ e : Fin I ⊕ Fin J, occurrenceCovariance ℓ (routedOccurrence g probes a colors e 0)
      (routedOccurrence g probes a colors e 1)) =
      (∏ i, curvatureLine ℓ (a i)) * ∏ j, externalLine g probes ℓ j := by
  rw [Fintype.prod_sum_type]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    simp only [occurrence_covariance_eq, routedOccurrence, routedSlot_end, if_true,
      edgeSlot, g.internalInteraction, occurrenceLine]
  · apply Finset.prod_congr rfl
    intro j _
    simp only [occurrence_covariance_eq, routedOccurrence, routedSlot_end, if_true, edgeSlot, externalLine]

def vertexProduct {n r p I J : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (g : Incidence r p I J)
    (probes : Fin p → ModeSlot n) (a : Fin I → MeanZeroMode) (colors : EdgeColors n I)
    (outputs : Fin r → Fin n) : ℝ := by
  classical
  exact if routingConsistent g probes a colors then
    ∏ v, vertexCoefficient B (routedVertex g probes a colors outputs v) else 0

def routedWickTerm {n r p I J : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (g : Incidence r p I J)
    (probes : Fin p → ModeSlot n) (ℓ : ℝ) (a : Fin I → MeanZeroMode) (colors : EdgeColors n I)
    (outputs : Fin r → Fin n) : ℝ :=
  vertexProduct B g probes a colors outputs *
    ∏ e : Fin I ⊕ Fin J, occurrenceCovariance ℓ (routedOccurrence g probes a colors e 0)
      (routedOccurrence g probes a colors e 1)

/-- There is exactly one transferred line per internal edge, including
self-edge contractions, while every noninternal edge contributes a
bounded fixed elementary or mixed line. -/
theorem routedWickTerm_factor {n r p I J : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (g : Incidence r p I J) (probes : Fin p → ModeSlot n) (ℓ : ℝ) (a : Fin I → MeanZeroMode)
    (colors : EdgeColors n I) (outputs : Fin r → Fin n) :
    routedWickTerm B g probes ℓ a colors outputs =
      (vertexProduct B g probes a colors outputs * ∏ j, externalLine g probes ℓ j) *
        ∏ i, curvatureLine ℓ (a i) := by
  rw [routedWickTerm, product_edge_covariances]
  ring

def configuredSlot {n r p : ℕ} (v : Fin r → VertexChoice n)
    (probes : Fin p → ModeSlot n) : EndPosition r p → ModeSlot n
  | .inl (z,(x,y)) =>
    let e := if x = 0 then (v z).2.1 else (v z).2.2
    if y = 0 then leftSlot e else rightSlot e
  | .inr z => probes z

/-- Any nonzero matching of a literal vertex configuration is determined
by one elementary slot per internal edge and the prescribed probes. -/
theorem routedSlot_recovers_matched_configuration {n r p I J : ℕ} (g : Incidence r p I J)
    (v : Fin r → VertexChoice n) (probes : Fin p → ModeSlot n)
    (h : ∀ e, configuredSlot v probes (g.ends (e,0)) = configuredSlot v probes (g.ends (e,1))) :
    let slot := fun i => configuredSlot v probes (g.ends (Sum.inl i,0))
    routedSlot g probes (fun i => (slot i).1) (fun i => (slot i).2) = configuredSlot v probes := by
  dsimp only
  funext x
  obtain ⟨⟨e,b⟩,rfl⟩ := g.ends.surjective x
  rw [routedSlot_end]
  have hb : b = 0 ∨ b = 1 := by omega
  rcases e with i | j
  · rcases hb with rfl | rfl
    · rfl
    · exact h _
  · have hP : edgeSlot g probes
        (fun i => (configuredSlot v probes (g.ends (.inl i,0))).1)
        (fun i => (configuredSlot v probes (g.ends (.inl i,0))).2) (.inr j) =
      configuredSlot v probes (g.ends (.inr j, g.probeSide j)) := by
      rw [g.probeIdentity]
      rfl
    rw [hP]
    have hside : g.probeSide j = 0 ∨ g.probeSide j = 1 := by omega
    rcases hside with h0 | h1 <;> rcases hb with rfl | rfl
    · rw [h0]
    · rw [h0, h]
    · rw [h1, ← h]
    · rw [h1]

end UV.VerifyCurvatureRouting
