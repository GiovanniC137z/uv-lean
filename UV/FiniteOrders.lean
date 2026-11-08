import UV.GlobalAssembly
import UV.RealDegree
import UV.Forest
import Mathlib.Analysis.Normed.Group.InfiniteSum

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal NNReal BigOperators

namespace UV

/-- The sector criterion is uniform in external data when its ordinary and
infrared envelopes are common. Jacobians remain in the covered measures. -/
theorem uniform_forest_convergence
    {P H X : Type*} [Fintype H] [MeasurableSpace X]
    {A : H → Type*} [∀ h, MeasurableSpace (A h)]
    (r : H → ℕ) (ν : ∀ h, Measure (A h)) [∀ h, IsFiniteMeasure (ν h)]
    (μ μIR : Measure X) (σ : ∀ h, ((Fin (r h) → ℝ) × A h) → X)
    (J : ∀ h, ((Fin (r h) → ℝ) × A h) → ℝ≥0)
    (gaussian : ∀ h, Fin (r h) → Bool) (ω a : ∀ h, Fin (r h) → ℝ)
    (C : H → ℝ) (f : P → X → ℂ) (hf : ∀ p, StronglyMeasurable (f p))
    (hσ : ∀ h, Measurable (σ h)) (hJ : ∀ h, Measurable (J h))
    (gIR : X → ℝ) (hgIR : Integrable gIR μIR)
    (hIR : ∀ p, ∀ᵐ x ∂μIR, ‖f p x‖ ≤ gIR x)
    (hscale : ∀ h i, if gaussian h i then 0 < a h i else ω h i < 0)
    (henvelope : ∀ p h, ∀ᵐ x ∂((Measure.pi (fun _ : Fin (r h) =>
      volume.restrict (Ioi (1 : ℝ)))).prod (ν h)),
      ‖J h x • f p (σ h x)‖ ≤ C h * ∏ i,
        sectorScale (gaussian h i) (ω h i) (a h i) (x.1 i))
    (hcover : μ ≤ μIR + ∑ h, Measure.map (σ h)
      (Measure.withDensity
        ((Measure.pi (fun _ : Fin (r h) => volume.restrict (Ioi (1 : ℝ)))).prod (ν h))
        (fun x => (J h x : ℝ≥0∞)))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p, Integrable (f p) μ ∧ (∫ x, ‖f p x‖ ∂μ) ≤ B := by
  classical
  let β h := (Measure.pi (fun _ : Fin (r h) => volume.restrict (Ioi (1 : ℝ)))).prod (ν h)
  let env h (x : (Fin (r h) → ℝ) × A h) :=
    C h * ∏ i, sectorScale (gaussian h i) (ω h i) (a h i) (x.1 i)
  let m h := Measure.map (σ h) ((β h).withDensity (fun x => (J h x : ℝ≥0∞)))
  have he h : Integrable (env h) (β h) :=
    mixed_sector_envelope_integrable (gaussian h) (ω h) (a h) (C h) (hscale h)
  have hw p h : Integrable (fun x => J h x • f p (σ h x)) (β h) :=
    (he h).mono' ((hJ h).aestronglyMeasurable.smul
      ((hf p).comp_measurable (hσ h)).aestronglyMeasurable) (henvelope p h)
  have hm p h : Integrable (f p) (m h) := by
    apply (integrable_map_measure (hf p).aestronglyMeasurable (hσ h).aemeasurable).mpr
    exact (integrable_withDensity_iff_integrable_smul (hJ h)).mpr (hw p h)
  have hsum p : Integrable (f p) (∑ h, m h) :=
    integrable_finset_sum_measure.mpr fun h _ => hm p h
  have hir p : Integrable (f p) μIR :=
    hgIR.mono' (hf p).aestronglyMeasurable (hIR p)
  have hm_bound p h : (∫ x, ‖f p x‖ ∂m h) ≤ ∫ x, env h x ∂β h := by
    rw [integral_map_of_stronglyMeasurable (hσ h) (hf p).norm,
      integral_withDensity_eq_integral_smul (hJ h)]
    have heq : (fun x => J h x • ‖f p (σ h x)‖) =
        (fun x => ‖J h x • f p (σ h x)‖) := by
      funext x
      change (J h x : ℝ) * ‖f p (σ h x)‖ = ‖(J h x : ℝ) • f p (σ h x)‖
      rw [norm_smul, Real.norm_of_nonneg (J h x).coe_nonneg]
    rw [heq]
    exact integral_mono_ae (hw p h).norm (he h) (henvelope p h)
  let B := (∫ x, gIR x ∂μIR) + ∑ h, ∫ x, env h x ∂β h
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro p
  have hv := (hir p).add_measure (hsum p)
  refine ⟨hv.mono_measure hcover, ?_⟩
  calc
    _ ≤ ∫ x, ‖f p x‖ ∂(μIR + ∑ h, m h) :=
      integral_mono_measure hcover (Filter.Eventually.of_forall fun x => norm_nonneg _) hv.norm
    _ = (∫ x, ‖f p x‖ ∂μIR) + ∑ h, ∫ x, ‖f p x‖ ∂m h := by
      rw [integral_add_measure (hir p).norm (hsum p).norm,
        integral_finset_sum_measure (fun h _ => (hm p h).norm)]
    _ ≤ B := add_le_add (integral_mono_ae (hir p).norm hgIR (hIR p))
      (Finset.sum_le_sum fun h _ => hm_bound p h)
    _ ≤ max 0 B := le_max_right _ _

/-- Raw regulated-line data. Integrability of the graph is not a field. -/
structure RegulatedLineData (I : Type) (D : ℝ) where
  ρ : I → Measure ℝ
  finite : ∀ i, IsFiniteMeasure (ρ i)
  positive_support : ∀ i, ρ i (Iio 0) = 0
  control : ∀ i, GapOrEndpoint (ρ i) D
  E : I → ℝ → ℝ
  a : I → ℝ
  α0 : I → ℝ
  K : I → ℝ
  measurable : ∀ i, Measurable (E i)
  proper_time : ∀ i, IntegrableOn (E i) (Ioi 0)
  nonnegative : ∀ i α, 0 < α → 0 ≤ E i α
  near_zero_scale : ∀ i, 0 < α0 i
  near_zero_bound : ∀ i, ∀ α ∈ Ioc 0 (α0 i), E i α ≤ K i
  positive_scale : ∀ i, 0 < a i

structure BoundedLineData (I : Type) where
  Φ : I → ℝ → ℝ
  E : I → ℝ → ℝ
  M : I → ℝ
  multiplier_measurable : ∀ i, Measurable (Φ i)
  multiplier_bound : ∀ i z, 0 ≤ z → ‖Φ i z‖ ≤ M i
  envelope_measurable : ∀ i, Measurable (E i)
  proper_time : ∀ i, IntegrableOn (E i) (Ioi 0)
  nonnegative : ∀ i α, 0 < α → 0 ≤ E i α

structure GlobalGraphData (P : Type) where
  edges : ℕ
  loops : ℕ
  routing : Matrix (Fin edges) (Fin loops) ℝ
  full_rank : routing.rank = loops
  shift : P → Fin edges → LoopMomentum
  B : ℝ
  C : ℝ
  D : ℝ
  nonnegative_B : 0 ≤ B
  nonnegative_C : 0 ≤ C
  nonnegative_D : 0 ≤ D
  shift_bound : ∀ p, ‖shift p‖ ≤ B
  lines : RegulatedLineData (Fin edges) D
  numerator : P → (Fin loops → LoopMomentum) → ℂ
  numerator_measurable : ∀ p, StronglyMeasurable (numerator p)
  numerator_bound : ∀ p k, ‖numerator p k‖ ≤ C * (1 + ‖k‖ ^ D)

structure DampedGraphData (P : Type) where
  remaining : ℕ
  loops : ℕ
  routing : Matrix (Fin loops ⊕ Fin remaining) (Fin loops) ℝ
  selected_rank : Matrix.det (routing.submatrix Sum.inl id) ≠ 0
  shift : P → (Fin loops ⊕ Fin remaining) → LoopMomentum
  B : ℝ
  C : ℝ
  D : ℝ
  nonnegative_B : 0 ≤ B
  nonnegative_C : 0 ≤ C
  nonnegative_D : 0 ≤ D
  shift_bound : ∀ p, ‖shift p‖ ≤ B
  selected : RegulatedLineData (Fin loops) D
  other : BoundedLineData (Fin remaining)
  numerator : P → (Fin loops → LoopMomentum) → ℂ
  numerator_measurable : ∀ p, StronglyMeasurable (numerator p)
  numerator_bound : ∀ p k, ‖numerator p k‖ ≤ C * (1 + ‖k‖ ^ D)

structure ResidualGraphData (P : Type) where
  loops : ℕ
  integrand : P → EuclideanSpace ℝ (Fin (4 * loops)) → ℂ
  residual : P → EuclideanSpace ℝ (Fin (4 * loops)) → ℝ
  quadratic : Bool
  a : ℝ
  B : ℝ
  C : ℝ
  D : ℝ
  positive_a : 0 < a
  nonnegative_C : 0 ≤ C
  nonnegative_D : 0 ≤ D
  measurable : ∀ p, AEStronglyMeasurable (integrand p) volume
  vertex_bound : ∀ p k, ‖integrand p k‖ ≤ C * (1 + ‖k‖ ^ D) * exp (-residual p k)
  coercive : ∀ p k, (if quadratic then a * ‖k‖ ^ 2 else a * ‖k‖) - B ≤ residual p k

structure ForestGraphData (P X H : Type) [MeasurableSpace X] [Fintype H]
    (A : H → Type) [∀ h, MeasurableSpace (A h)] where
  r : H → ℕ
  ν : ∀ h, Measure (A h)
  finite : ∀ h, IsFiniteMeasure (ν h)
  μ : Measure X
  μIR : Measure X
  σ : ∀ h, ((Fin (r h) → ℝ) × A h) → X
  J : ∀ h, ((Fin (r h) → ℝ) × A h) → ℝ≥0
  gaussian : ∀ h, Fin (r h) → Bool
  ω : ∀ h, Fin (r h) → ℝ
  a : ∀ h, Fin (r h) → ℝ
  C : H → ℝ
  integrand : P → X → ℂ
  measurable : ∀ p, StronglyMeasurable (integrand p)
  sector_measurable : ∀ h, Measurable (σ h)
  jacobian_measurable : ∀ h, Measurable (J h)
  irEnvelope : X → ℝ
  ir_integrable : Integrable irEnvelope μIR
  ir_bound : ∀ p, ∀ᵐ x ∂μIR, ‖integrand p x‖ ≤ irEnvelope x
  scale_test : ∀ h i, if gaussian h i then 0 < a h i else ω h i < 0
  envelope : ∀ p h, ∀ᵐ x ∂((Measure.pi (fun _ : Fin (r h) =>
    volume.restrict (Ioi (1 : ℝ)))).prod (ν h)),
    ‖J h x • integrand p (σ h x)‖ ≤ C h * ∏ i,
      sectorScale (gaussian h i) (ω h i) (a h i) (x.1 i)
  cover : μ ≤ μIR + ∑ h, Measure.map (σ h)
    (Measure.withDensity
      ((Measure.pi (fun _ : Fin (r h) => volume.restrict (Ioi (1 : ℝ)))).prod (ν h))
      (fun x => (J h x : ℝ≥0∞)))

/-- An actual graph with one of the four source criteria. Constructors store
routing/line/vertex/sector hypotheses, never the desired graph integrability. -/
inductive SourceGraph (P : Type) : Type 1 where
  | global (g : GlobalGraphData P)
  | damped (g : DampedGraphData P)
  | residual (g : ResidualGraphData P)
  | forest {X H : Type} [MeasurableSpace X] [Fintype H]
      {A : H → Type} [∀ h, MeasurableSpace (A h)] (g : ForestGraphData P X H A)


def SourceGraph.Domain {P : Type} (g : SourceGraph P) : Type := by
  cases g with
  | global g => exact Fin g.loops → LoopMomentum
  | damped g => exact Fin g.loops → LoopMomentum
  | residual g => exact EuclideanSpace ℝ (Fin (4 * g.loops))
  | @forest X H _ _ A _ _ => exact X

instance (priority := 100) {P : Type} (g : SourceGraph P) : MeasurableSpace g.Domain := by
  cases g <;> dsimp [SourceGraph.Domain] <;> infer_instance

def SourceGraph.measure {P : Type} (g : SourceGraph P) : Measure g.Domain := by
  cases g with
  | global g => exact Measure.pi fun _ : Fin g.loops => (volume : Measure LoopMomentum)
  | damped g => exact Measure.pi fun _ : Fin g.loops => (volume : Measure LoopMomentum)
  | residual g => exact (volume : Measure (EuclideanSpace ℝ (Fin (4 * g.loops))))
  | @forest X H hX hH A hA g => exact g.μ

def SourceGraph.integrand {P : Type} (g : SourceGraph P) : P → g.Domain → ℂ := by
  cases g with
  | global g =>
    exact fun p k => (∏ i, schwingerLine (g.lines.ρ i) (g.lines.E i) (g.lines.a i)
      (rectangularMomentum g.routing g.shift i p k)) • g.numerator p k
  | damped g =>
    exact fun p k =>
      ((∏ j, schwingerLine (g.selected.ρ j) (g.selected.E j) (g.selected.a j)
        (rectangularMomentum g.routing g.shift (Sum.inl j) p k)) *
        (∏ u, boundedCovariance (g.other.Φ u) (g.other.E u)
          (rectangularMomentum g.routing g.shift (Sum.inr u) p k))) • g.numerator p k
  | residual g => exact g.integrand
  | @forest X H hX hH A hA g => exact g.integrand

/-- Every graph carrying actual source criterion data has a derived uniform
finite bound. Graph integrability is a conclusion in each constructor case. -/
theorem SourceGraph.bounded {P : Type} (g : SourceGraph P) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p,
      Integrable (g.integrand p) g.measure ∧ (∫ x, ‖g.integrand p x‖ ∂g.measure) ≤ B := by
  cases g with
  | global g =>
    letI := g.lines.finite
    obtain ⟨B, hB, h⟩ := global_uv_rectangular g.routing g.full_rank g.shift
      g.nonnegative_B g.nonnegative_C g.nonnegative_D g.shift_bound
      g.lines.ρ g.lines.positive_support g.lines.control
      g.lines.E g.lines.a g.lines.α0 g.lines.K g.lines.measurable g.lines.proper_time
      g.lines.nonnegative g.lines.near_zero_scale g.lines.near_zero_bound g.lines.positive_scale
      g.numerator g.numerator_measurable g.numerator_bound
    exact ⟨B, hB, fun p => ⟨(h p).1, (h p).2.1⟩⟩
  | damped g =>
    letI := g.selected.finite
    exact damped_basis_rectangular g.routing g.selected_rank g.shift
      g.nonnegative_B g.nonnegative_C g.nonnegative_D g.shift_bound
      g.selected.ρ g.selected.positive_support g.selected.control
      g.selected.E g.selected.a g.selected.α0 g.selected.K g.selected.measurable
      g.selected.proper_time g.selected.nonnegative g.selected.near_zero_scale
      g.selected.near_zero_bound g.selected.positive_scale
      g.other.Φ g.other.E g.other.M g.other.multiplier_measurable g.other.multiplier_bound
      g.other.envelope_measurable g.other.proper_time g.other.nonnegative
      g.numerator g.numerator_measurable g.numerator_bound
  | residual g =>
    let S : EuclideanSpace ℝ (Fin (4 * g.loops)) → ℝ := fun k =>
      if g.quadratic then g.a * ‖k‖ ^ 2 else g.a * ‖k‖
    let W : EuclideanSpace ℝ (Fin (4 * g.loops)) → ℝ :=
      fun k => (1 + ‖k‖ ^ g.D) * exp (-S k)
    have hiW : Integrable W volume := by
      cases hq : g.quadratic with
      | false => simpa only [W, S, hq, Bool.false_eq_true, ite_false] using
          (integrable_real_degree_exp (E := EuclideanSpace ℝ (Fin (4 * g.loops)))
            (μ := volume) g.positive_a g.nonnegative_D)
      | true => simpa only [W, S, hq, ite_true] using
          (integrable_real_degree_gaussian (E := EuclideanSpace ℝ (Fin (4 * g.loops)))
            (μ := volume) g.positive_a g.nonnegative_D)
    let H : EuclideanSpace ℝ (Fin (4 * g.loops)) → ℝ :=
      fun k => (g.C * exp g.B) * W k
    have hiH : Integrable H volume := hiW.const_mul _
    have hb p k : ‖g.integrand p k‖ ≤ H k := by
      have hs : S k - g.B ≤ g.residual p k := g.coercive p k
      calc
        _ ≤ g.C * (1 + ‖k‖ ^ g.D) * exp (-g.residual p k) := g.vertex_bound p k
        _ ≤ g.C * (1 + ‖k‖ ^ g.D) * exp (g.B - S k) := by
          apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith))
          exact mul_nonneg g.nonnegative_C (by positivity)
        _ = H k := by dsimp [H, W]; rw [exp_sub, exp_neg]; ring
    refine ⟨max 0 (∫ k, H k), le_max_left _ _, ?_⟩
    intro p
    have hi := hiH.mono' (g.measurable p) (Filter.Eventually.of_forall (hb p))
    exact ⟨hi, (integral_mono_ae hi.norm hiH (Filter.Eventually.of_forall (hb p))).trans
      (le_max_right _ _)⟩
  | @forest X H hX hH A hA g =>
    letI := g.finite
    exact uniform_forest_convergence g.r g.ν g.μ g.μIR g.σ g.J g.gaussian g.ω g.a g.C
      g.integrand g.measurable g.sector_measurable g.jacobian_measurable
      g.irEnvelope g.ir_integrable g.ir_bound g.scale_test g.envelope g.cover


/-- Finite-order meaning of all orders: every graph in every finite-order
index family is finite because its actual source criterion data prove it.
There is no uniform-in-order constant or infinite graph sum in this statement. -/
theorem all_finite_orders {P : Type} {G : ℕ → Type}
    (data : ∀ n, G n → SourceGraph P) :
    ∀ n g, ∃ B : ℝ, 0 ≤ B ∧ ∀ p,
      Integrable ((data n g).integrand p) (data n g).measure ∧
        (∫ x, ‖(data n g).integrand p x‖ ∂(data n g).measure) ≤ B :=
  fun n g => (data n g).bounded

/-- A finite collection of source-admissible graphs has a uniform bound even
when the graphs have different loop numbers, line sets, and integration spaces. -/
theorem finite_graph_collection_uniform {P G : Type} [Fintype G]
    (data : G → SourceGraph P) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g p,
      Integrable ((data g).integrand p) (data g).measure ∧
        (∫ x, ‖(data g).integrand p x‖ ∂(data g).measure) ≤ B := by
  classical
  choose B hB hb using fun g => (data g).bounded
  refine ⟨∑ g, B g, Finset.sum_nonneg (fun g _ => hB g), ?_⟩
  intro g p
  exact ⟨(hb g p).1, (hb g p).2.trans
    (Finset.single_le_sum (fun g _ => hB g) (Finset.mem_univ g))⟩

/-- The uniform constant chosen from the proved source criterion, rather than
an integrability hypothesis supplied by a graph-family caller. -/
def SourceGraph.uniformConstant {P : Type} (g : SourceGraph P) : ℝ :=
  Classical.choose g.bounded

theorem SourceGraph.uniformConstant_nonneg {P : Type} (g : SourceGraph P) :
    0 ≤ g.uniformConstant := (Classical.choose_spec g.bounded).1

theorem SourceGraph.uniformConstant_spec {P : Type} (g : SourceGraph P) (p : P) :
    Integrable (g.integrand p) g.measure ∧
      (∫ x, ‖g.integrand p x‖ ∂g.measure) ≤ g.uniformConstant :=
  (Classical.choose_spec g.bounded).2 p

/-- Absolutely summable derived graph majorants justify a summed label family.
This is an additional summability assumption on that family, not an assertion
of convergence in perturbative order or of an unrestricted infinite graph sum. -/
theorem summable_graph_collection {P I : Type}
    (data : I → SourceGraph P)
    (hmajorants : Summable (fun i => (data i).uniformConstant)) :
    ∀ p,
      (∀ i, Integrable ((data i).integrand p) (data i).measure) ∧
      Summable (fun i => ∫ x, ‖(data i).integrand p x‖ ∂(data i).measure) ∧
      (∑' i, ∫ x, ‖(data i).integrand p x‖ ∂(data i).measure) ≤
        ∑' i, (data i).uniformConstant ∧
      Summable (fun i => ‖∫ x, (data i).integrand p x ∂(data i).measure‖) ∧
      Summable (fun i => ∫ x, (data i).integrand p x ∂(data i).measure) ∧
      ‖∑' i, ∫ x, (data i).integrand p x ∂(data i).measure‖ ≤
        ∑' i, (data i).uniformConstant := by
  intro p
  have hi i := (data i).uniformConstant_spec p
  have hn i : 0 ≤ ∫ x, ‖(data i).integrand p x‖ ∂(data i).measure :=
    integral_nonneg fun x => norm_nonneg _
  have ha : Summable (fun i => ∫ x, ‖(data i).integrand p x‖ ∂(data i).measure) :=
    hmajorants.of_norm_bounded fun i => by
      rw [Real.norm_of_nonneg (hn i)]
      exact (hi i).2
  have hamp i : ‖∫ x, (data i).integrand p x ∂(data i).measure‖ ≤
      (data i).uniformConstant := (norm_integral_le_integral_norm _).trans (hi i).2
  have hamps : Summable (fun i => ‖∫ x, (data i).integrand p x ∂(data i).measure‖) :=
    hmajorants.of_norm_bounded fun i => by rw [norm_norm]; exact hamp i
  refine ⟨fun i => (hi i).1, ha, ?_, hamps, hamps.of_norm, ?_⟩
  · exact ha.tsum_le_tsum (fun i => (hi i).2) hmajorants
  · exact tsum_of_norm_bounded hmajorants.hasSum hamp

/-- The summed-label clause also accepts any proved summable numerical graph
majorants, rather than only the particular constants selected above. Each
individual graph's integrability still follows from its actual source data. -/
theorem summable_graph_collection_of_majorants {P I : Type}
    (data : I → SourceGraph P) (A : I → ℝ) (hA : Summable A)
    (hbound : ∀ i p, (∫ x, ‖(data i).integrand p x‖ ∂(data i).measure) ≤ A i) :
    ∀ p,
      (∀ i, Integrable ((data i).integrand p) (data i).measure) ∧
      Summable (fun i => ∫ x, ‖(data i).integrand p x‖ ∂(data i).measure) ∧
      (∑' i, ∫ x, ‖(data i).integrand p x‖ ∂(data i).measure) ≤ ∑' i, A i ∧
      Summable (fun i => ‖∫ x, (data i).integrand p x ∂(data i).measure‖) ∧
      Summable (fun i => ∫ x, (data i).integrand p x ∂(data i).measure) ∧
      ‖∑' i, ∫ x, (data i).integrand p x ∂(data i).measure‖ ≤ ∑' i, A i := by
  intro p
  have hn i : 0 ≤ ∫ x, ‖(data i).integrand p x‖ ∂(data i).measure :=
    integral_nonneg fun x => norm_nonneg _
  have ha : Summable (fun i => ∫ x, ‖(data i).integrand p x‖ ∂(data i).measure) :=
    hA.of_norm_bounded fun i => by
      rw [Real.norm_of_nonneg (hn i)]
      exact hbound i p
  have hamp i : ‖∫ x, (data i).integrand p x ∂(data i).measure‖ ≤ A i :=
    (norm_integral_le_integral_norm _).trans (hbound i p)
  have hamps : Summable (fun i => ‖∫ x, (data i).integrand p x ∂(data i).measure‖) :=
    hA.of_norm_bounded fun i => by rw [norm_norm]; exact hamp i
  refine ⟨fun i => ((data i).uniformConstant_spec p).1, ha, ?_, hamps, hamps.of_norm, ?_⟩
  · exact ha.tsum_le_tsum (fun i => hbound i p) hA
  · exact tsum_of_norm_bounded hA.hasSum hamp

end UV
