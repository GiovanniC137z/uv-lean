import UV.ContinuationGraph
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! Selecting a controlling routing after the common width sample is drawn. -/

noncomputable section
open MeasureTheory Set Filter Real
open scoped BigOperators

namespace UV.ContinuationGraph

/-- A candidate controlling routing on a fixed Euclidean loop chart. It stores
criteria for every sample and allows the complete remainder to depend on the
sample. There is no requirement that this candidate's budget be integrable. -/
structure HeatRoutingChoice (P X : Type) [MeasurableSpace X] (L : ℕ) where
  terms : ℕ
  C : Matrix (Fin L) (Fin L) ℝ
  e : EuclideanLoops L ≃L[ℝ] EuclideanLoops L
  representation : LinearMap.toMatrix (loopProductBasis (Fin L)) (loopProductBasis (Fin L)) e.toLinearMap =
    Matrix.kronecker C (1 : Matrix (Fin 4) (Fin 4) ℝ)
  shift : P → EuclideanLoops L
  lapse : Fin L → X → ℝ
  lapse_measurable : ∀ j, Measurable (lapse j)
  mass : Fin L → ℝ
  degree : Fin terms → Fin L → ℝ
  coeff : Fin terms → X → ℝ
  degree_nonneg : ∀ i j, 0 ≤ degree i j
  coeff_nonneg : ∀ i x, 0 ≤ coeff i x
  coeff_measurable : ∀ i, Measurable (coeff i)
  remainder : P → X → EuclideanLoops L → ℂ
  remainder_measurable : ∀ p x, StronglyMeasurable (remainder p x)
  remainder_bound : ∀ p x q, ‖remainder p x q‖ ≤ ∑ i, coeff i x * ∏ j, (1 + ‖q j‖ ^ degree i j)

def HeatRoutingChoice.integrand {P X : Type} [MeasurableSpace X] {L : ℕ}
    (g : HeatRoutingChoice P X L) (p : P) (z : X × EuclideanLoops L) : ℂ :=
  (fourierLoopFactor L)⁻¹ • RevisionJointHeat.heatGraph g.lapse g.mass g.e g.shift g.remainder p z

def HeatRoutingChoice.budget {P X : Type} [MeasurableSpace X] {L : ℕ}
    (g : HeatRoutingChoice P X L) (x : X) : ℝ :=
  |Matrix.det g.C| ^ (-4 : ℝ) / fourierLoopFactor L * RevisionJointHeat.jointBudget g.lapse g.degree g.coeff x

theorem HeatRoutingChoice.budget_measurable {P X : Type} [MeasurableSpace X] {L : ℕ}
    (g : HeatRoutingChoice P X L) : Measurable g.budget := by
  unfold HeatRoutingChoice.budget RevisionJointHeat.jointBudget RevisionJointHeat.gaussianBudget
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  apply (g.coeff_measurable i).mul
  apply Finset.measurable_prod
  intro j _
  have hm := g.lapse_measurable j
  fun_prop

theorem HeatRoutingChoice.bound_at_sample {P X : Type} [MeasurableSpace X] {L : ℕ}
    (g : HeatRoutingChoice P X L) (p : P) (x : X) (hwidth : ∀ j, 0 < g.lapse j x) :
    let μ := Measure.pi fun _ : Fin L => (volume : Measure LoopMomentum)
    Integrable (fun k => g.integrand p (x, k)) μ ∧ (∫ k, ‖g.integrand p (x, k)‖ ∂μ) ≤ g.budget x := by
  intro μ
  have h := RevisionJointHeat.conditionalHeatGraph_bound g.lapse g.mass g.degree g.coeff
    g.degree_nonneg g.coeff_nonneg g.C g.e g.representation g.shift g.remainder
    (fun p x => (g.remainder_measurable p x).aestronglyMeasurable) g.remainder_bound p x hwidth
  refine ⟨h.1.smul _, ?_⟩
  simp_rw [HeatRoutingChoice.integrand, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (fourierLoopFactor_pos _).le), ← div_eq_inv_mul]
  simpa only [HeatRoutingChoice.budget, RevisionJointHeat.jointBudget, fourierLoopFactor, Fintype.card_fin] using h.2

/-- The measurable minimum of the candidate budgets controls one actual
coefficient on a fixed loop chart. The identifications `hmatch` keep every
choice attached to the same conditional graph, rather than to distinct graphs
with independently averaged widths. Only the minimum is averaged. -/
theorem joint_graph_of_best_selected_routing
    {P X H : Type} [MeasurableSpace X] [Fintype H] [Nonempty H] {L : ℕ}
    (ρ : Measure X) [IsFiniteMeasure ρ]
    (g : H → HeatRoutingChoice P X L) (f : P → X × EuclideanLoops L → ℂ)
    (hf : ∀ p, StronglyMeasurable (f p))
    (hwidth : ∀ h, ∀ᵐ x ∂ρ, ∀ j, 0 < (g h).lapse j x)
    (hmatch : ∀ p h, ∀ᵐ x ∂ρ, ∀ k, f p (x, k) = (g h).integrand p (x, k))
    (hb : Integrable (fun x => ⨅ h, (g h).budget x) ρ) :
    Measurable (fun x => ⨅ h, (g h).budget x) ∧
    ∀ p, let μ := Measure.pi fun _ : Fin L => (volume : Measure LoopMomentum)
    Integrable (f p) (ρ.prod μ) ∧
    (∫ z, ‖f p z‖ ∂(ρ.prod μ)) ≤ ∫ x, (⨅ h, (g h).budget x) ∂ρ ∧
    (∫ x, (∫ k, f p (x, k) ∂μ) ∂ρ) = ∫ k, (∫ x, f p (x, k) ∂ρ) ∂μ := by
  refine ⟨Measurable.iInf fun h => (g h).budget_measurable, ?_⟩
  intro p μ
  have hm : AEStronglyMeasurable (f p) (ρ.prod μ) := (hf p).aestronglyMeasurable
  have hchoice : ∀ᵐ x ∂ρ, ∀ h,
      Integrable (fun k => f p (x, k)) μ ∧ (∫ k, ‖f p (x, k)‖ ∂μ) ≤ (g h).budget x := by
    apply ae_all_iff.mpr
    intro h
    filter_upwards [hwidth h, hmatch p h] with x hx he
    simp_rw [he]
    exact (g h).bound_at_sample p x hx
  have h0 : ∀ᵐ x ∂ρ, (∫ k, ‖f p (x, k)‖ ∂μ) ≤ ⨅ h, (g h).budget x := by
    filter_upwards [hchoice] with x hx
    exact le_ciInf fun h => (hx h).2
  have hi : Integrable (f p) (ρ.prod μ) := by
    apply (integrable_prod_iff hm).mpr
    refine ⟨hchoice.mono fun x hx => (hx (Classical.choice ‹Nonempty H›)).1, ?_⟩
    apply hb.mono' hm.norm.integral_prod_right'
    filter_upwards [h0] with x hx
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact hx
  refine ⟨hi, ?_, (integral_prod _ hi).symm.trans (integral_prod_symm _ hi)⟩
  rw [integral_prod _ hi.norm]
  exact integral_mono_ae (integrable_prod_iff hm |>.mp hi).2 hb h0

end UV.ContinuationGraph
