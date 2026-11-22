import UV.ContinuationGraph

/-! Assembly of the admissible alternatives for every finite graph of a
declared completed action. -/

noncomputable section
open MeasureTheory Set Real
open scoped BigOperators ENNReal NNReal

namespace UV.ContinuationGraph

/-- A finite simultaneous sector cover on the actual Euclidean graph measure.
The controlled scales permit arbitrary positive stretched-exponential powers. -/
structure RevisedForestGraphData (P X H : Type) [MeasurableSpace X] [Fintype H]
    (A : H → Type) [∀ h, MeasurableSpace (A h)] where
  r : H → ℕ
  ν : ∀ h, Measure (A h)
  finite : ∀ h, IsFiniteMeasure (ν h)
  μ : Measure X
  μIR : Measure X
  σ : ∀ h, ((Fin (r h) → ℝ) × A h) → X
  J : ∀ h, ((Fin (r h) → ℝ) × A h) → ℝ≥0
  controlled : ∀ h, Fin (r h) → Bool
  ω : ∀ h, Fin (r h) → ℝ
  a : ∀ h, Fin (r h) → ℝ
  η : ∀ h, Fin (r h) → ℝ
  C : H → ℝ
  integrand : P → X → ℂ
  measurable : ∀ p, StronglyMeasurable (integrand p)
  sector_measurable : ∀ h, Measurable (σ h)
  jacobian_measurable : ∀ h, Measurable (J h)
  irEnvelope : X → ℝ
  ir_integrable : Integrable irEnvelope μIR
  ir_bound : ∀ p, ∀ᵐ x ∂μIR, ‖integrand p x‖ ≤ irEnvelope x
  scale_test : ∀ h i, if controlled h i then 0 < a h i ∧ 0 < η h i else ω h i < 0
  envelope : ∀ p h, ∀ᵐ x ∂((Measure.pi (fun _ : Fin (r h) =>
    volume.restrict (Ioi (1 : ℝ)))).prod (ν h)),
    ‖J h x • integrand p (σ h x)‖ ≤ C h * ∏ i,
      revisedSectorScale (controlled h i) (ω h i) (a h i) (η h i) (x.1 i)
  cover : μ ≤ μIR + ∑ h, Measure.map (σ h)
    (Measure.withDensity
      ((Measure.pi (fun _ : Fin (r h) => volume.restrict (Ioi (1 : ℝ)))).prod (ν h))
      (fun x => (J h x : ℝ≥0∞)))

/-- The positive measure of sector parameters before the sector Jacobian. -/
def RevisedForestGraphData.sectorMeasure {P X H : Type} [MeasurableSpace X] [Fintype H]
    {A : H → Type} [∀ h, MeasurableSpace (A h)] (g : RevisedForestGraphData P X H A) (h : H) :
    Measure ((Fin (g.r h) → ℝ) × A h) :=
  (Measure.pi (fun _ : Fin (g.r h) => volume.restrict (Ioi (1 : ℝ)))).prod (g.ν h)

def RevisedForestGraphData.sectorMajorant {P X H : Type} [MeasurableSpace X] [Fintype H]
    {A : H → Type} [∀ h, MeasurableSpace (A h)] (g : RevisedForestGraphData P X H A) (h : H)
    (z : (Fin (g.r h) → ℝ) × A h) : ℝ :=
  g.C h * ∏ i, revisedSectorScale (g.controlled h i) (g.ω h i) (g.a h i) (g.η h i) (z.1 i)

/-- Explicit numerical majorant from the IR and sector comparisons. In a
conditional family this is the quantity to average over the sample law. -/
def RevisedForestGraphData.budget {P X H : Type} [MeasurableSpace X] [Fintype H]
    {A : H → Type} [∀ h, MeasurableSpace (A h)] (g : RevisedForestGraphData P X H A) : ℝ :=
  (∫ x, g.irEnvelope x ∂g.μIR) + ∑ h, ∫ z, g.sectorMajorant h z ∂g.sectorMeasure h

/-- The bound is produced by the ordinary IR comparison and the transformed
sector integrals, with their actual Jacobians retained. -/
theorem revisedForestGraph_exact_bound {P X H : Type} [MeasurableSpace X] [Fintype H]
    {A : H → Type} [∀ h, MeasurableSpace (A h)] (g : RevisedForestGraphData P X H A)
    (p : P) : Integrable (g.integrand p) g.μ ∧ (∫ x, ‖g.integrand p x‖ ∂g.μ) ≤ g.budget := by
  classical
  letI := g.finite
  let f := g.integrand p
  let m (h : H) := Measure.map (g.σ h) ((g.sectorMeasure h).withDensity (fun z => (g.J h z : ℝ≥0∞)))
  have he (h : H) : Integrable (g.sectorMajorant h) (g.sectorMeasure h) :=
    revised_sector_envelope_integrable (g.controlled h) (g.ω h) (g.a h) (g.η h) (g.C h) (g.scale_test h)
  have hw (h : H) : Integrable (fun z => g.J h z • f (g.σ h z)) (g.sectorMeasure h) :=
    (he h).mono' ((g.jacobian_measurable h).aestronglyMeasurable.smul
      ((g.measurable p).comp_measurable (g.sector_measurable h)).aestronglyMeasurable) (g.envelope p h)
  have hm (h : H) : Integrable f (m h) :=
    (integrable_map_measure (g.measurable p).aestronglyMeasurable (g.sector_measurable h).aemeasurable).mpr
      ((integrable_withDensity_iff_integrable_smul (g.jacobian_measurable h)).mpr (hw h))
  have hsum : Integrable f (∑ h, m h) := integrable_finset_sum_measure.mpr fun h _ => hm h
  have hir : Integrable f g.μIR :=
    g.ir_integrable.mono' (g.measurable p).aestronglyMeasurable (g.ir_bound p)
  have hm_bound (h : H) : (∫ x, ‖f x‖ ∂m h) ≤ ∫ z, g.sectorMajorant h z ∂g.sectorMeasure h := by
    rw [integral_map_of_stronglyMeasurable (g.sector_measurable h) (g.measurable p).norm,
      integral_withDensity_eq_integral_smul (g.jacobian_measurable h)]
    have heq : (fun z => g.J h z • ‖f (g.σ h z)‖) = (fun z => ‖g.J h z • f (g.σ h z)‖) := by
      funext z
      change (g.J h z : ℝ) * ‖f (g.σ h z)‖ = ‖(g.J h z : ℝ) • f (g.σ h z)‖
      rw [norm_smul, Real.norm_of_nonneg (g.J h z).coe_nonneg]
    rw [heq]
    exact integral_mono_ae (hw h).norm (he h) (g.envelope p h)
  have hv := hir.add_measure hsum
  refine ⟨hv.mono_measure g.cover, ?_⟩
  calc
    _ ≤ ∫ x, ‖f x‖ ∂(g.μIR + ∑ h, m h) :=
      integral_mono_measure g.cover (Filter.Eventually.of_forall fun _ => norm_nonneg _) hv.norm
    _ = (∫ x, ‖f x‖ ∂g.μIR) + ∑ h, ∫ x, ‖f x‖ ∂m h := by
      rw [integral_add_measure hir.norm hsum.norm, integral_finset_sum_measure (fun h _ => (hm h).norm)]
    _ ≤ g.budget := add_le_add (integral_mono_ae hir.norm g.ir_integrable (g.ir_bound p))
      (Finset.sum_le_sum fun h _ => hm_bound h)

theorem revisedForestGraph_bounded {P X H : Type} [MeasurableSpace X] [Fintype H]
    {A : H → Type} [∀ h, MeasurableSpace (A h)] (g : RevisedForestGraphData P X H A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p,
      Integrable (g.integrand p) g.μ ∧ (∫ x, ‖g.integrand p x‖ ∂g.μ) ≤ B := by
  refine ⟨max 0 g.budget, le_max_left _ _, fun p => ?_⟩
  have h := revisedForestGraph_exact_bound g p
  exact ⟨h.1, h.2.trans (le_max_right _ _)⟩

/-- An expanded graph carries one of the source criteria. The original data
remain available through `SourceGraph`. The new constructors contain criterion
hypotheses and graph ingredients. -/
inductive ExpandedSourceGraph (P : Type) : Type 1 where
  | previous (g : SourceGraph P)
  | anisotropic (g : AnisotropicGraphData P)
  | jointHeat {X : Type} [MeasurableSpace X] (g : JointHeatGraphData P X)
  | forest {L : ℕ} {H : Type} [Fintype H] {A : H → Type} [∀ h, MeasurableSpace (A h)]
      (g : RevisedForestGraphData P (EuclideanLoops L) H A)

def ExpandedSourceGraph.Domain {P : Type} (g : ExpandedSourceGraph P) : Type := by
  cases g with
  | previous g => exact g.Domain
  | anisotropic g => exact EuclideanLoops g.loops
  | @jointHeat X _ g => exact X × EuclideanLoops g.loops
  | @forest L _ _ _ _ _ => exact EuclideanLoops L

instance (priority := 100) {P : Type} (g : ExpandedSourceGraph P) : MeasurableSpace g.Domain := by
  cases g <;> dsimp [ExpandedSourceGraph.Domain] <;> infer_instance

def ExpandedSourceGraph.measure {P : Type} (g : ExpandedSourceGraph P) : Measure g.Domain := by
  cases g with
  | previous g => exact g.measure
  | anisotropic g => exact Measure.pi fun _ => volume
  | jointHeat g => exact jointHeatMeasure g
  | forest g => exact g.μ

def ExpandedSourceGraph.integrand {P : Type} (g : ExpandedSourceGraph P) : P → g.Domain → ℂ := by
  cases g with
  | previous g => exact g.integrand
  | anisotropic g => exact anisotropicIntegrand g
  | jointHeat g => exact jointHeatIntegrand g
  | forest g => exact g.integrand

/-- Every alternative discharges absolute convergence through its own bounds
on the full Euclidean graph. -/
theorem ExpandedSourceGraph.bounded {P : Type} (g : ExpandedSourceGraph P) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p,
      Integrable (g.integrand p) g.measure ∧ (∫ x, ‖g.integrand p x‖ ∂g.measure) ≤ B := by
  cases g with
  | previous g => exact g.bounded
  | anisotropic g => exact anisotropicGraph_bounded g
  | jointHeat g => exact jointHeatGraph_bounded g
  | forest g => exact revisedForestGraph_bounded g

def ExpandedSourceGraph.uniformConstant {P : Type} (g : ExpandedSourceGraph P) : ℝ :=
  Classical.choose g.bounded

theorem ExpandedSourceGraph.uniformConstant_nonneg {P : Type} (g : ExpandedSourceGraph P) :
    0 ≤ g.uniformConstant := (Classical.choose_spec g.bounded).1

theorem ExpandedSourceGraph.uniformConstant_spec {P : Type} (g : ExpandedSourceGraph P) (p : P) :
    Integrable (g.integrand p) g.measure ∧ (∫ x, ‖g.integrand p x‖ ∂g.measure) ≤ g.uniformConstant :=
  (Classical.choose_spec g.bounded).2 p

/-- The finite-order graph families are indexed separately at each order.
The result gives a bound for each individual admitted graph. -/
theorem expanded_all_finite_orders {P : Type} {G : ℕ → Type}
    (graph : ∀ n, G n → ExpandedSourceGraph P) :
    ∀ n g, ∃ B : ℝ, 0 ≤ B ∧ ∀ p,
      Integrable ((graph n g).integrand p) (graph n g).measure ∧
      (∫ x, ‖(graph n g).integrand p x‖ ∂(graph n g).measure) ≤ B :=
  fun n g => (graph n g).bounded

/-- Zero-loop contributions are simply their externally defined coefficient.
The domain parameter can be a subtype of admissible external data carrying a
tree boundary prescription. Its declaration is independent of loop estimates. -/
theorem tree_coefficient_without_loop_integral {P : Type} (f : P → ℂ) (p : P) :
    Integrable (fun _ : Unit => f p) (Measure.dirac ()) ∧
      (∫ _ : Unit, f p ∂Measure.dirac ()) = f p := by
  exact ⟨integrable_const _, by simp⟩

/-- A finite selected collection can include different orders and criteria.
Its uniform bound is the finite sum of the derived graph constants. -/
theorem expanded_finite_graph_collection_uniform {P G : Type} [Fintype G]
    (graph : G → ExpandedSourceGraph P) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g p,
      Integrable ((graph g).integrand p) (graph g).measure ∧
      (∫ x, ‖(graph g).integrand p x‖ ∂(graph g).measure) ≤ B := by
  classical
  let B (g : G) := (graph g).uniformConstant
  have hn : ∀ g, 0 ≤ B g := fun g => (graph g).uniformConstant_nonneg
  refine ⟨∑ g, B g, Finset.sum_nonneg (fun g _ => hn g), ?_⟩
  intro g p
  have h := (graph g).uniformConstant_spec p
  exact ⟨h.1, h.2.trans (Finset.single_le_sum (fun g _ => hn g) (Finset.mem_univ g))⟩

/-- The sum over residual labels uses a separate absolutely summable family
of numerical majorants. Each summand's integrability is already derived
from its own criterion, regardless of the total label set. -/
theorem expanded_summable_graph_collection {P I : Type}
    (graph : I → ExpandedSourceGraph P) (A : I → ℝ) (hA : Summable A)
    (hbound : ∀ i p, (∫ x, ‖(graph i).integrand p x‖ ∂(graph i).measure) ≤ A i) :
    ∀ p,
      (∀ i, Integrable ((graph i).integrand p) (graph i).measure) ∧
      Summable (fun i => ∫ x, ‖(graph i).integrand p x‖ ∂(graph i).measure) ∧
      (∑' i, ∫ x, ‖(graph i).integrand p x‖ ∂(graph i).measure) ≤ ∑' i, A i ∧
      Summable (fun i => ‖∫ x, (graph i).integrand p x ∂(graph i).measure‖) ∧
      Summable (fun i => ∫ x, (graph i).integrand p x ∂(graph i).measure) ∧
      ‖∑' i, ∫ x, (graph i).integrand p x ∂(graph i).measure‖ ≤ ∑' i, A i := by
  intro p
  have hn i : 0 ≤ ∫ x, ‖(graph i).integrand p x‖ ∂(graph i).measure :=
    integral_nonneg fun _ => norm_nonneg _
  have ha : Summable (fun i => ∫ x, ‖(graph i).integrand p x‖ ∂(graph i).measure) :=
    hA.of_norm_bounded fun i => by
      rw [Real.norm_of_nonneg (hn i)]
      exact hbound i p
  have hamp i : ‖∫ x, (graph i).integrand p x ∂(graph i).measure‖ ≤ A i :=
    (norm_integral_le_integral_norm _).trans (hbound i p)
  have hamps : Summable (fun i => ‖∫ x, (graph i).integrand p x ∂(graph i).measure‖) :=
    hA.of_norm_bounded fun i => by rw [norm_norm]; exact hamp i
  refine ⟨fun i => ((graph i).uniformConstant_spec p).1, ha, ?_, hamps, hamps.of_norm, ?_⟩
  · exact ha.tsum_le_tsum (fun i => hbound i p) hA
  · exact tsum_of_norm_bounded hA.hasSum hamp

end UV.ContinuationGraph
