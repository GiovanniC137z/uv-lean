import UV.ContinuumBVAction
import UV.ContinuumLegendreST

/-! The conditional continuum source-to-effective-action pipeline. Data
describe an invariant admitted differentiation domain, canonical generator
laws and actual exponential/logarithm convergence inside that domain.
No partition, connected or effective-action Ward identity is a data field. -/

noncomputable section
open MeasureTheory

namespace UV

variable {X A B C : Type*} [MeasurableSpace X]
  [Ring A] [Algebra ℚ A] [Algebra ℝ A] [TopologicalSpace A]
  [IsTopologicalRing A] [ContinuousSMul ℝ A] [T2Space A] [SeparatingDual ℝ A]
  [Ring B] [Algebra ℚ B] [Algebra ℝ B] [Algebra ℂ B] [TopologicalSpace B]
  [IsTopologicalRing B] [ContinuousSMul ℝ B] [T2Space B] [SeparatingDual ℝ B]

def continuumBVExponent (μ : Measure X) {σ : GradingInvolution A}
    (s : ClosedBRST σ) (ε : X → Bool) (S0 Ψ : A) (φ af J : X → A) : A :=
  -continuumBVAction μ s ε S0 Ψ φ af + continuumSourcePairing μ J φ

/-- Explicit common-domain hypotheses of the conditional BRST theorem.
The continuous maps act on a locally convex functional algebra; the algebra
is not required to carry a Banach norm with bounded canonical derivatives. -/
structure AdmittedContinuumBRST (μ : Measure X)
    (σA : GradingInvolution A) (σB : GradingInvolution B) (ε : X → Bool) where
  brst : ClosedBRST σA
  sourceWard : GradedDerivative σA true
  connectedWard : GradedDerivative σB true
  brstCLM : A →L[ℝ] A
  sourceCLM : A →L[ℝ] A
  parityCLM : A →L[ℝ] A
  brstCLM_apply : ∀ f, brstCLM f = brst.derivative.d f
  sourceCLM_apply : ∀ f, sourceCLM f = sourceWard.d f
  parityCLM_apply : ∀ f, parityCLM f = σA.parity f
  connected_continuous : Continuous connectedWard.d
  connected_parity_continuous : Continuous σB.parity
  invariantAction : A
  gaugeFermion : A
  field : X → A
  antifield : X → A
  source : X → A
  invariant_action_brst : brst.derivative.d invariantAction = 0
  antifield_brst : ∀ x, brst.derivative.d (antifield x) = 0
  source_brst : ∀ x, brst.derivative.d (source x) = 0
  action_af_independent : sourceWard.d invariantAction = 0
  gauge_af_independent : sourceWard.d (brst.derivative.d gaugeFermion) = 0
  canonical_af_shift : ∀ x, sourceWard.d (antifield x) = source x
  variation_af_independent : ∀ x, sourceWard.d (brst.derivative.d (field x)) = 0
  source_af_independent : ∀ x, sourceWard.d (source x) = 0
  field_af_independent : ∀ x, sourceWard.d (field x) = 0
  action_even : σA.parity invariantAction = invariantAction
  gauge_odd : σA.parity gaugeFermion = -gaugeFermion
  field_parity : ∀ x, σA.parity (field x) = koszulSign (ε x) • field x
  antifield_parity : ∀ x, σA.parity (antifield x) = koszulSign (!(ε x)) • antifield x
  source_parity : ∀ x, σA.parity (source x) = koszulSign (ε x) • source x
  antifield_integrable : WeakIntegrable μ (fun x => koszulSign (ε x) •
    (antifield x * brst.derivative.d (field x)))
  source_pair_integrable : WeakIntegrable μ (fun x => source x * field x)
  expectation : A →ₗ[ℚ] B
  expectation_invariant : ∀ f, expectation (brst.derivative.d f) = 0
  expectation_differentiation : ∀ f,
    connectedWard.d (expectation f) = expectation (sourceWard.d f)
  expectation_parity : ∀ f, σB.parity (expectation f) = expectation (σA.parity f)
  scalar_inert : ∀ z : ℂ, connectedWard.d (algebraMap ℂ B z) = 0
  scalar_even : ∀ z : ℂ, σB.parity (algebraMap ℂ B z) = algebraMap ℂ B z
  logarithm_center : ℂ
  logarithm_center_ne_zero : logarithm_center ≠ 0
  exponential_admitted : Summable (formalExpCoefficient
    (continuumBVExponent μ brst ε invariantAction gaugeFermion field antifield source))
  logarithm_admitted : Summable (localBodyLogTerm logarithm_center
    (completedBRSTPartition expectation
      (continuumBVExponent μ brst ε invariantAction gaugeFermion field antifield source)))

def admittedContinuumPartition {μ : Measure X} {σA : GradingInvolution A}
    {σB : GradingInvolution B} {ε : X → Bool}
    (d : AdmittedContinuumBRST μ σA σB ε) : B :=
  completedBRSTPartition d.expectation
    (continuumBVExponent μ d.brst ε d.invariantAction d.gaugeFermion d.field d.antifield d.source)

def admittedContinuumConnected {μ : Measure X} {σA : GradingInvolution A}
    {σB : GradingInvolution B} {ε : X → Bool}
    (d : AdmittedContinuumBRST μ σA σB ε) : B :=
  localBodyLog d.logarithm_center (admittedContinuumPartition d)

omit [ContinuousSMul ℝ A] [Algebra ℝ B] [IsTopologicalRing B]
  [ContinuousSMul ℝ B] [SeparatingDual ℝ B] in
theorem admitted_continuum_connected_ward {μ : Measure X} {σA : GradingInvolution A}
    {σB : GradingInvolution B} {ε : X → Bool}
    (d : AdmittedContinuumBRST μ σA σB ε) :
    d.connectedWard.d (admittedContinuumConnected d) = 0 := by
  have hX := continuum_bv_exponent_opposite_derivatives μ d.brst d.sourceWard
    d.brstCLM d.sourceCLM d.brstCLM_apply d.sourceCLM_apply ε
    d.invariantAction d.gaugeFermion d.field d.antifield d.source
    d.invariant_action_brst d.antifield_brst d.source_brst d.source_parity
    d.action_af_independent d.gauge_af_independent d.canonical_af_shift
    d.variation_af_independent d.source_af_independent d.field_af_independent
    d.antifield_integrable d.source_pair_integrable
  have hQ : Continuous d.sourceWard.d :=
    d.sourceCLM.continuous.congr d.sourceCLM_apply
  have hs : Continuous d.brst.derivative.d :=
    d.brstCLM.continuous.congr d.brstCLM_apply
  exact completed_partition_connected_ward d.brst d.sourceWard d.connectedWard
    d.expectation _ hX d.expectation_invariant d.expectation_differentiation
    hQ hs d.connected_continuous d.scalar_inert d.exponential_admitted d.logarithm_admitted

omit [IsTopologicalRing A] [ContinuousSMul ℝ A] [Algebra ℝ B]
  [IsTopologicalRing B] [ContinuousSMul ℝ B] [SeparatingDual ℝ B] in
theorem admitted_continuum_connected_even {μ : Measure X} {σA : GradingInvolution A}
    {σB : GradingInvolution B} {ε : X → Bool}
    (d : AdmittedContinuumBRST μ σA σB ε) :
    σB.parity (admittedContinuumConnected d) = admittedContinuumConnected d := by
  have hX := continuum_bv_exponent_even μ d.brst d.parityCLM d.parityCLM_apply ε
    d.invariantAction d.gaugeFermion d.field d.antifield d.source
    d.action_even d.gauge_odd d.source_parity d.field_parity d.antifield_parity
    d.antifield_integrable d.source_pair_integrable
  have hσ : Continuous σA.parity := d.parityCLM.continuous.congr d.parityCLM_apply
  exact completed_partition_connected_even d.expectation hX hσ
    d.connected_parity_continuous d.exponential_admitted d.expectation_parity
    d.scalar_even d.logarithm_admitted

variable [Ring C] [Algebra ℚ C] [Algebra ℝ C] [TopologicalSpace C]
  [IsTopologicalRing C] [ContinuousSMul ℝ C] [T2Space C] [SeparatingDual ℝ C]

omit [ContinuousSMul ℝ A] [IsTopologicalRing B] [SeparatingDual ℝ B] in
/-- The entire constructed continuum action/expectation/logarithm/Legendre
chain yields the actual effective-action master equation. The matching is
between the source differentiation operators for this same functional. -/
theorem conditional_continuum_slavnov_taylor
    {μ : Measure X} {σA : GradingInvolution A} {σB : GradingInvolution B}
    {σC : GradingInvolution C} {ε : X → Bool} {G : Type*} {T : Bool → Type*}
    (d : AdmittedContinuumBRST μ σA σB ε)
    (c : WeakContinuumLegendreDomain μ σB σC ε (admittedContinuumConnected d) G T)
    (hmatch : c.sourceWard = d.connectedWard) :
    let p := weakEffectiveActionGradients c (admitted_continuum_connected_even d)
    (1/2 : ℚ) • weakCanonicalAntibracket c p p = 0 := by
  apply weak_continuum_legendre_slavnov_taylor c (admitted_continuum_connected_even d)
  rw [hmatch]
  exact admitted_continuum_connected_ward d

end UV
