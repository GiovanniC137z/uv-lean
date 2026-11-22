import UV.ContinuationGraphOrders

/-! Passing a conditional forest estimate through the common sample law. -/

noncomputable section
open MeasureTheory Set Real Filter
open scoped BigOperators ENNReal NNReal

namespace UV.ContinuationGraph

/-- A complete conditional forest bound can be averaged over its common sample
law. Each slice is checked using its actual transformed coefficient, Jacobian,
IR envelope and degree or gap tests. Integrability of the explicit numerical
budget is the extra hypothesis needed for this averaging step. -/
theorem conditional_forest_joint_bound
    {T P H : Type} [MeasurableSpace T] [Fintype H] {L : ℕ}
    {A : H → Type} [∀ h, MeasurableSpace (A h)]
    (ρ : Measure T) [IsFiniteMeasure ρ]
    (g : T → RevisedForestGraphData P (EuclideanLoops L) H A)
    (hμ : ∀ t, (g t).μ = Measure.pi fun _ => volume)
    (hb : Integrable (fun t => (g t).budget) ρ)
    (hf : ∀ p, StronglyMeasurable (fun z : T × EuclideanLoops L => (g z.1).integrand p z.2)) :
    ∀ p, let μ := Measure.pi fun _ : Fin L => (volume : Measure LoopMomentum)
    let f := fun z : T × EuclideanLoops L => (g z.1).integrand p z.2
    Integrable f (ρ.prod μ) ∧ (∫ z, ‖f z‖ ∂(ρ.prod μ)) ≤ ∫ t, (g t).budget ∂ρ ∧
      (∫ t, (∫ k, f (t, k) ∂μ) ∂ρ) = ∫ k, (∫ t, f (t, k) ∂ρ) ∂μ := by
  intro p μ f
  have hm : AEStronglyMeasurable f (ρ.prod μ) := (hf p).aestronglyMeasurable
  have hi (t : T) : Integrable (fun k => f (t, k)) μ ∧
      (∫ k, ‖f (t, k)‖ ∂μ) ≤ (g t).budget := by
    simpa only [f, μ, hμ] using revisedForestGraph_exact_bound (g t) p
  have hi' : Integrable f (ρ.prod μ) := by
    apply (integrable_prod_iff hm).mpr
    refine ⟨Eventually.of_forall fun t => (hi t).1, ?_⟩
    apply hb.mono' hm.norm.integral_prod_right'
    apply Eventually.of_forall
    intro t
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact (hi t).2
  refine ⟨hi', ?_, (integral_prod _ hi').symm.trans (integral_prod_symm _ hi')⟩
  rw [integral_prod _ hi'.norm]
  exact integral_mono (integrable_prod_iff hm |>.mp hi').2 hb (fun t => (hi t).2)

end UV.ContinuationGraph
