import UV.ConditionalST
import UV.ContinuumFormalST
import UV.CompletedGraphAction

/-! Conditional exact ST for the same completed graph action.
The invariant BV/exponential/logarithm construction derives connected Ward
closure, the continuum Legendre construction derives effective ST, and the
actual profile integral identifies its genuine formal loop convolution.
Both character components use the same reconstructed graph coefficient data. -/

noncomputable section
open MeasureTheory
open scoped BigOperators PowerSeries.WithPiTopology

namespace UV

variable {X A S B : Type*} [MeasurableSpace X]
  [Ring A] [Algebra ℚ A] [Algebra ℝ A] [TopologicalSpace A]
  [IsTopologicalRing A] [ContinuousSMul ℝ A] [T2Space A] [SeparatingDual ℝ A]
  [Ring S] [Algebra ℚ S] [Algebra ℝ S] [Algebra ℂ S] [TopologicalSpace S]
  [IsTopologicalRing S] [ContinuousSMul ℝ S] [T2Space S] [SeparatingDual ℝ S]
  [Ring B] [Algebra ℚ B] [Algebra ℝ B] [TopologicalSpace B]
  [IsTopologicalRing B] [ContinuousSMul ℝ B] [T2Space B] [SeparatingDual ℝ B]
  {μ : Measure X} {σA : GradingInvolution A} {σS : GradingInvolution S}
  {σB : GradingInvolution B} {ε : X → Bool} {G₀ G : Type*} {T : Bool → Type*}

omit [ContinuousSMul ℝ A] [IsTopologicalRing S] [SeparatingDual ℝ S] in
/-- No connected or effective Ward identity is an input: they follow from
the constructed continuum BV action and its invariant admitted expectation. -/
theorem conditional_formal_continuum_ST
    (d : AdmittedContinuumBRST μ σA σS ε)
    {W₀ : S} (c₀ : WeakContinuumLegendreDomain μ σS σB ε W₀ G₀ T)
    (c : WeakContinuumLegendreDomain μ σS (formalGrading σB) ε
      (admittedContinuumConnected d) G T)
    (hmatch : c.sourceWard = d.connectedWard)
    {U : Subalgebra ℚ B} (v : WeakRegularGradientCalculus c₀ U) (Γ : PowerSeries U)
    (hfield : ∀ δ t, c.fieldD δ t = formalGradedDerivative (c₀.fieldD δ t))
    (haf : ∀ δ t, c.antifieldD δ t = formalGradedDerivative (c₀.antifieldD δ t))
    (htest : ∀ δ t, c.test δ t = c₀.test δ t)
    (hR : ∀ δ t, WeakIntegrable μ (fun x => c₀.test δ t x • weakFormalRightProfile v Γ x))
    (hL : ∀ δ t, WeakIntegrable μ (fun x => c₀.test δ t x • weakFormalLeftProfile v Γ x))
    (hI : WeakIntegrable μ (fun x => weakProfilePair (formalGrading σB) (ε x)
      (weakFormalRightProfile v Γ x) (weakFormalLeftProfile v Γ x)
      (weakFormalRightProfile v Γ x) (weakFormalLeftProfile v Γ x)))
    (hΓ : weakEffectiveAction c = PowerSeries.map U.val.toRingHom Γ) :
    formalMasterSeries (weakRegularBracket v) Γ = 0 := by
  apply continuum_formal_master_from_legendre c₀ c v Γ hfield haf htest hR hL hI hΓ
    (admitted_continuum_connected_even d)
  rw [hmatch]
  exact admitted_continuum_connected_ward d

/-- A common model stores the actual action/measure/domain data, fixed
canonical coefficient frame and exact formal action identification. It has
no Ward, ST, graph convergence or loop equation field. -/
structure CompletedContinuumSTModel
    (μ : Measure X) (σA : GradingInvolution A) (σS : GradingInvolution S)
    (σB : GradingInvolution B) (ε : X → Bool) (U : Subalgebra ℚ B)
    (G₀ G : Type*) (T : Bool → Type*) where
  admitted : AdmittedContinuumBRST μ σA σS ε
  baseConnected : S
  baseDomain : WeakContinuumLegendreDomain μ σS σB ε baseConnected G₀ T
  regular : WeakRegularGradientCalculus baseDomain U
  domain : WeakContinuumLegendreDomain μ σS (formalGrading σB) ε
    (admittedContinuumConnected admitted) G T
  source_operator : domain.sourceWard = admitted.connectedWard
  action : PowerSeries U
  field_frame : ∀ δ t, domain.fieldD δ t = formalGradedDerivative (baseDomain.fieldD δ t)
  antifield_frame : ∀ δ t, domain.antifieldD δ t = formalGradedDerivative (baseDomain.antifieldD δ t)
  test_frame : ∀ δ t, domain.test δ t = baseDomain.test δ t
  right_integrable : ∀ δ t, WeakIntegrable μ
    (fun x => baseDomain.test δ t x • weakFormalRightProfile regular action x)
  left_integrable : ∀ δ t, WeakIntegrable μ
    (fun x => baseDomain.test δ t x • weakFormalLeftProfile regular action x)
  bracket_integrable : WeakIntegrable μ (fun x => weakProfilePair (formalGrading σB) (ε x)
    (weakFormalRightProfile regular action x) (weakFormalLeftProfile regular action x)
    (weakFormalRightProfile regular action x) (weakFormalLeftProfile regular action x))
  action_identification : weakEffectiveAction domain = PowerSeries.map U.val.toRingHom action

omit [ContinuousSMul ℝ A] [IsTopologicalRing S] [SeparatingDual ℝ S] in
theorem CompletedContinuumSTModel.master
    {U : Subalgebra ℚ B}
    (m : CompletedContinuumSTModel μ σA σS σB ε U G₀ G T) :
    formalMasterSeries (weakRegularBracket m.regular) m.action = 0 :=
  conditional_formal_continuum_ST m.admitted m.baseDomain m.domain m.source_operator
    m.regular m.action m.field_frame m.antifield_frame m.test_frame
    m.right_integrable m.left_integrable m.bracket_integrable m.action_identification

omit [ContinuousSMul ℝ A] [IsTopologicalRing S] [SeparatingDual ℝ S] in
theorem CompletedContinuumSTModel.loop_convolution
    {U : Subalgebra ℚ B}
    (m : CompletedContinuumSTModel μ σA σS σB ε U G₀ G T) (n : ℕ) :
    ∑ j ∈ Finset.range (n+1), weakRegularBracket m.regular
      (PowerSeries.coeff j m.action) (PowerSeries.coeff (n-j) m.action) = 0 :=
  formal_master_convolution_zero m.master n

section Carrier

variable {U : Type*} [Ring U] [Algebra ℚ U]

def pairedRegularBracket (β₀ β₁ : U →ₗ[ℚ] U →ₗ[ℚ] U) :
    (U × U) →ₗ[ℚ] (U × U) →ₗ[ℚ] (U × U) where
  toFun F :=
    { toFun := fun H => (β₀ F.1 H.1, β₁ F.2 H.2)
      map_add' H K := by simp
      map_smul' r H := by simp }
  map_add' F H := by ext K <;> simp
  map_smul' r F := by ext H <;> simp

def pairedFormalAction (Γ₀ Γ₁ : PowerSeries U) : PowerSeries (U × U) :=
  PowerSeries.mk (fun n => (PowerSeries.coeff n Γ₀, PowerSeries.coeff n Γ₁))

theorem paired_formal_master_zero {β₀ β₁ : U →ₗ[ℚ] U →ₗ[ℚ] U}
    {Γ₀ Γ₁ : PowerSeries U} (h₀ : formalMasterSeries β₀ Γ₀ = 0)
    (h₁ : formalMasterSeries β₁ Γ₁ = 0) :
    formalMasterSeries (pairedRegularBracket β₀ β₁) (pairedFormalAction Γ₀ Γ₁) = 0 := by
  apply PowerSeries.ext
  intro n
  apply Prod.ext
  · have h := congrArg (PowerSeries.coeff n) h₀
    simpa [formalMasterSeries, formalBilinear_coeff_range, pairedFormalAction,
      pairedRegularBracket, Prod.fst_sum] using h
  · have h := congrArg (PowerSeries.coeff n) h₁
    simpa [formalMasterSeries, formalBilinear_coeff_range, pairedFormalAction,
      pairedRegularBracket, Prod.snd_sum] using h

end Carrier

omit [ContinuousSMul ℝ A] [IsTopologicalRing S] [SeparatingDual ℝ S] in
/-- The conditional exact ST theorem and its same-action UV-finite graph
application. Every displayed graph/insertion is the one reconstructing the
constructed effective action, in both character components simultaneously. -/
theorem completed_graph_conditional_slavnov_taylor
    {P I : Type} {U : Subalgebra ℚ B}
    (a : CompletedGraphAction P I)
    (m : Bool → CompletedContinuumSTModel μ σA σS σB ε U G₀ G T)
    (r : CompletedGraphRealization a (fun k => (m k).action)) :
    (∀ k, formalMasterSeries (weakRegularBracket (m k).regular) (m k).action = 0) ∧
    (∀ k n, ∑ j ∈ Finset.range (n+1), weakRegularBracket (m k).regular
      (r.reconstruct (completedGraphCoefficient a j k))
      (r.reconstruct (completedGraphCoefficient a (n-j) k)) = 0) ∧
    (∀ n k i g p, Integrable ((a.graph n k i g).integrand p) (a.graph n k i g).measure) ∧
    (∀ n k i p, ‖r.insertion (PowerSeries.coeff n (m k).action) i p‖ ≤ completedGraphBudget a n k i) ∧
    formalMasterSeries (pairedRegularBracket
      (weakRegularBracket (m false).regular) (weakRegularBracket (m true).regular))
      (pairedFormalAction (m false).action (m true).action) = 0 := by
  refine ⟨fun k => (m k).master, ?_, completedGraph_integrable a, ?_,
    paired_formal_master_zero (m false).master (m true).master⟩
  · intro k n
    have h := (m k).loop_convolution n
    simpa only [r.coefficient] using h
  · intro n k i p
    exact completedGraphRealization_insertion_norm_le r k n i p

end UV
