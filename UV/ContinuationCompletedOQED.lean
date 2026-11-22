import UV.ContinuationCompletedST
import UV.OQEDGraph

/-! Revised O–QED forest bounds for the literal kernel graph on the actual
Euclidean chart, ready for the common completed-action coefficient family. -/

noncomputable section
open MeasureTheory UV.ContinuationGraph
open scoped BigOperators

namespace UV.ContinuationCompleted

/-- The declared O–QED coefficient with its literal line kernels, covariances,
complete numerator and finite-dimensional loop normalization. -/
def oqedEuclideanIntegrand {I P : Type} [Fintype I] {L : ℕ}
    (C : Matrix I (Fin L) ℝ) (R : P → I → LoopMomentum) (a M : I → ℝ)
    (cov : I → LoopMomentum → ℝ) (N : P → EuclideanLoops L → ℂ)
    (p : P) (k : EuclideanLoops L) : ℂ :=
  (fourierLoopFactor L)⁻¹ • ((∏ i,
    cov i (rectangularMomentum C R i p k) * kernel (a i) (M i) (‖rectangularMomentum C R i p k‖ ^ 2)) • N p k)

/-- The revised arbitrary-power forest applies directly to the declared
O–QED integrand. The stated identification keeps the same coefficient in
both the forest certificate and the action's insertion reconstruction. -/
theorem oqed_revised_forest_graph {I P H : Type} [Fintype I] [Fintype H] {L : ℕ}
    {A : H → Type} [∀ h, MeasurableSpace (A h)]
    (g : RevisedForestGraphData P (EuclideanLoops L) H A)
    (C : Matrix I (Fin L) ℝ) (R : P → I → LoopMomentum) (a M : I → ℝ)
    (cov : I → LoopMomentum → ℝ) (N : P → EuclideanLoops L → ℂ)
    (hmeasure : g.μ = Measure.pi fun _ => volume)
    (hactual : g.integrand = oqedEuclideanIntegrand C R a M cov N) :
    (∀ p, Integrable (oqedEuclideanIntegrand C R a M cov N p) (Measure.pi fun _ => volume) ∧
      (∫ k, ‖oqedEuclideanIntegrand C R a M cov N p k‖ ∂(Measure.pi fun _ => volume)) ≤ g.budget) ∧
    (ExpandedSourceGraph.forest g).integrand = oqedEuclideanIntegrand C R a M cov N := by
  refine ⟨fun p => ?_, hactual⟩
  simpa only [hactual, hmeasure] using revisedForestGraph_exact_bound g p

end UV.ContinuationCompleted
