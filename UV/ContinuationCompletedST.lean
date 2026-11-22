import UV.ContinuationGraphFixed
import UV.CompletedGraphST

/-! Same-action coefficient reconstruction and insertions for the expanded
UV criteria. The measured graph belongs to a fixed action and character. -/

noncomputable section
open MeasureTheory UV.ContinuationGraph
open scoped BigOperators PowerSeries.WithPiTopology

namespace UV.ContinuationCompleted

/-- A complete finite graph family at every loop order, character and
required insertion. The external parameter type can be an admitted compact
set. Coupling, symmetry and ordering coefficients are retained explicitly. -/
structure ExpandedCompletedGraphAction (P I : Type) where
  Graph : ℕ → Bool → I → Type
  finite : ∀ n k i, Fintype (Graph n k i)
  graph : ∀ n k i, Graph n k i → ExpandedSourceGraph P
  weight : ∀ n k i, Graph n k i → ℂ

instance {P I : Type} (a : ExpandedCompletedGraphAction P I) (n : ℕ) (k : Bool) (i : I) :
    Fintype (a.Graph n k i) := a.finite n k i

def completedGraphIntegral {P I : Type} (a : ExpandedCompletedGraphAction P I)
    (n : ℕ) (k : Bool) (i : I) (g : a.Graph n k i) (p : P) : ℂ :=
  ∫ x, (a.graph n k i g).integrand p x ∂(a.graph n k i g).measure

def completedGraphCoefficient {P I : Type} (a : ExpandedCompletedGraphAction P I)
    (n : ℕ) (k : Bool) (i : I) (p : P) : ℂ :=
  ∑ g, a.weight n k i g * completedGraphIntegral a n k i g p

/-- This budget uses the constants obtained by the proved source criteria,
not an assumed bound or an assumed value of the completed coefficient. -/
def completedGraphBudget {P I : Type} (a : ExpandedCompletedGraphAction P I)
    (n : ℕ) (k : Bool) (i : I) : ℝ :=
  ∑ g, ‖a.weight n k i g‖ * (a.graph n k i g).uniformConstant

theorem completedGraph_integrable {P I : Type} (a : ExpandedCompletedGraphAction P I)
    (n : ℕ) (k : Bool) (i : I) (g : a.Graph n k i) (p : P) :
    Integrable ((a.graph n k i g).integrand p) (a.graph n k i g).measure :=
  ((a.graph n k i g).uniformConstant_spec p).1

theorem completedGraph_integral_norm_le {P I : Type} (a : ExpandedCompletedGraphAction P I)
    (n : ℕ) (k : Bool) (i : I) (g : a.Graph n k i) (p : P) :
    ‖completedGraphIntegral a n k i g p‖ ≤ (a.graph n k i g).uniformConstant :=
  (norm_integral_le_integral_norm _).trans ((a.graph n k i g).uniformConstant_spec p).2

/-- Actual weighted graph terms are integrable before any coefficient sum. -/
theorem completedGraph_weighted_integrable {P I : Type} (a : ExpandedCompletedGraphAction P I)
    (n : ℕ) (k : Bool) (i : I) (g : a.Graph n k i) (p : P) :
    Integrable (fun x => a.weight n k i g * (a.graph n k i g).integrand p x)
      (a.graph n k i g).measure :=
  (completedGraph_integrable a n k i g p).const_mul _

theorem completedGraph_weighted_integral {P I : Type} (a : ExpandedCompletedGraphAction P I)
    (n : ℕ) (k : Bool) (i : I) (g : a.Graph n k i) (p : P) :
    (∫ x, a.weight n k i g * (a.graph n k i g).integrand p x
      ∂(a.graph n k i g).measure) =
      a.weight n k i g * completedGraphIntegral a n k i g p := by
  exact integral_const_mul _ _

theorem completedGraphBudget_nonneg {P I : Type} (a : ExpandedCompletedGraphAction P I)
    (n : ℕ) (k : Bool) (i : I) : 0 ≤ completedGraphBudget a n k i :=
  Finset.sum_nonneg (fun g _ => mul_nonneg (norm_nonneg (a.weight n k i g))
    (ExpandedSourceGraph.uniformConstant_nonneg (a.graph n k i g)))

/-- All weighted absolute graph integrals have one finite uniform budget. -/
theorem completedGraph_absolute_sum_le {P I : Type} (a : ExpandedCompletedGraphAction P I)
    (n : ℕ) (k : Bool) (i : I) (p : P) :
    (∑ g, ∫ x, ‖a.weight n k i g * (a.graph n k i g).integrand p x‖
      ∂(a.graph n k i g).measure) ≤ completedGraphBudget a n k i := by
  apply Finset.sum_le_sum
  intro g _
  simp_rw [norm_mul]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left ((a.graph n k i g).uniformConstant_spec p).2 (norm_nonneg _)

theorem completedGraphCoefficient_norm_le {P I : Type} (a : ExpandedCompletedGraphAction P I)
    (n : ℕ) (k : Bool) (i : I) (p : P) :
    ‖completedGraphCoefficient a n k i p‖ ≤ completedGraphBudget a n k i := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro g _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (completedGraph_integral_norm_le a n k i g p) (norm_nonneg _)

/-- The finite-order statement has no bound uniform in loop order. Every
required insertion and both characters use their own actual graph family. -/
theorem completed_action_all_finite_orders {P I : Type} (a : ExpandedCompletedGraphAction P I) :
    ∀ n k i, ∃ B : ℝ, 0 ≤ B ∧
      (∀ g p, Integrable ((a.graph n k i g).integrand p) (a.graph n k i g).measure) ∧
      ∀ p, ‖completedGraphCoefficient a n k i p‖ ≤ B := by
  intro n k i
  exact ⟨completedGraphBudget a n k i, completedGraphBudget_nonneg a n k i,
    completedGraph_integrable a n k i, completedGraphCoefficient_norm_le a n k i⟩

def completedGraphCarrierCoefficient {P I : Type} (a : ExpandedCompletedGraphAction P I)
    (n : ℕ) (i : I) (p : P) : Carrier.Algebra :=
  (completedGraphCoefficient a n false i p, completedGraphCoefficient a n true i p)

theorem completedGraphCarrierCoefficient_norm_le {P I : Type} (a : ExpandedCompletedGraphAction P I)
    (n : ℕ) (i : I) (p : P) :
    ‖completedGraphCarrierCoefficient a n i p‖ ≤
      max (completedGraphBudget a n false i) (completedGraphBudget a n true i) := by
  rw [Prod.norm_def]
  exact max_le_max (completedGraphCoefficient_norm_le a n false i p)
    (completedGraphCoefficient_norm_le a n true i p)

/-- A common-action realization identifies the actual effective-action
coefficients with the same graph integrals. This is graph bookkeeping, not
a Ward identity, master equation, or graph integrability assumption. -/
structure ExpandedCompletedGraphRealization {P I : Type} {A : Type*} [Ring A] [Algebra ℚ A]
    (a : ExpandedCompletedGraphAction P I) (Γ : Bool → PowerSeries A) where
  reconstruct : (I → P → ℂ) →ₗ[ℚ] A
  insertion : A →ₗ[ℚ] (I → P → ℂ)
  coefficient : ∀ k n, PowerSeries.coeff n (Γ k) =
    reconstruct (completedGraphCoefficient a n k)
  insertion_reconstruct : ∀ k n,
    insertion (reconstruct (completedGraphCoefficient a n k)) =
      completedGraphCoefficient a n k

/-- The declared insertion maps recover the actual scalar graph integrals.
This prevents a reconstruction from silently discarding nonzero graph
coefficients while representing an unrelated effective action. -/
theorem completedGraphRealization_actual_insertions
    {P I : Type} {A : Type*} [Ring A] [Algebra ℚ A]
    {a : ExpandedCompletedGraphAction P I} {Γ : Bool → PowerSeries A}
    (h : ExpandedCompletedGraphRealization a Γ) (k : Bool) (n : ℕ) (i : I) (p : P) :
    h.insertion (PowerSeries.coeff n (Γ k)) i p =
      ∑ g, a.weight n k i g *
        ∫ x, (a.graph n k i g).integrand p x ∂(a.graph n k i g).measure := by
  rw [h.coefficient, h.insertion_reconstruct]
  rfl

/-- UV finiteness applies to the required insertions of that very formal
effective action. There is no integral-convergence or symmetry premise. -/
theorem completedGraphRealization_insertion_norm_le
    {P I : Type} {A : Type*} [Ring A] [Algebra ℚ A]
    {a : ExpandedCompletedGraphAction P I} {Γ : Bool → PowerSeries A}
    (h : ExpandedCompletedGraphRealization a Γ) (k : Bool) (n : ℕ) (i : I) (p : P) :
    ‖h.insertion (PowerSeries.coeff n (Γ k)) i p‖ ≤ completedGraphBudget a n k i := by
  rw [h.coefficient, h.insertion_reconstruct]
  exact completedGraphCoefficient_norm_le a n k i p

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
/-- The conditional exact ST theorem and its same-action UV-finite graph
application. Every displayed graph/insertion is the one reconstructing the
constructed effective action, in both character components simultaneously. -/
theorem expanded_graph_conditional_slavnov_taylor
    {P I : Type} {U : Subalgebra ℚ B}
    (a : ExpandedCompletedGraphAction P I)
    (m : Bool → CompletedContinuumSTModel μ σA σS σB ε U G₀ G T)
    (r : ExpandedCompletedGraphRealization a (fun k => (m k).action)) :
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

end UV.ContinuationCompleted
