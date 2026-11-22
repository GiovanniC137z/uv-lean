import UV.RevisionJointHeat
import UV.RevisionLegacyForest

/-! The expanded source graph alternatives. Each new constructor retains the
actual loop coefficient, its measure and the criterion that controls it. -/

noncomputable section
open MeasureTheory Set Real
open scoped BigOperators ENNReal NNReal

namespace UV.ContinuationGraph

/-- The Euclidean loop chart uses four intrinsic coordinates for each loop.
No ambient geometric-time vector serves as a loop variable. -/
abbrev EuclideanLoops (L : ℕ) := Fin L → LoopMomentum

/-- Fourier normalization for the Euclidean loop measure. -/
def fourierLoopFactor (L : ℕ) : ℝ := (2 * π) ^ (4 * L)

theorem fourierLoopFactor_pos (L : ℕ) : 0 < fourierLoopFactor L := by
  unfold fourierLoopFactor
  positivity

/-- The selected-line representation of an independent-line graph. The full
anisotropic envelope includes every remaining interaction and covariance. -/
structure AnisotropicGraphData (P : Type) where
  loops : ℕ
  terms : ℕ
  C : Matrix (Fin loops) (Fin loops) ℝ
  det_ne_zero : C.det ≠ 0
  shift : P → EuclideanLoops loops
  law : Fin loops → Measure ℝ
  law_finite : ∀ j, IsFiniteMeasure (law j)
  law_nonnegative : ∀ j, law j (Iio 0) = 0
  law_no_zero : ∀ j, law j {0} = 0
  scale : Fin loops → ℝ
  scale_pos : ∀ j, 0 < scale j
  mass : Fin loops → ℝ
  degree : Fin terms → Fin loops → ℝ
  maxDegree : Fin loops → ℝ
  coeff : Fin terms → ℝ
  degree_nonneg : ∀ i j, 0 ≤ degree i j
  degree_le_max : ∀ i j, degree i j ≤ maxDegree j
  coeff_nonneg : ∀ i, 0 ≤ coeff i
  line_budget : ∀ j, inverseMoment (law j) (1 + maxDegree j / 2) < ⊤
  remainder : P → EuclideanLoops loops → ℂ
  remainder_measurable : ∀ p, StronglyMeasurable (remainder p)
  remainder_bound : ∀ p q, ‖remainder p q‖ ≤ ∑ i, coeff i * ∏ j, (1 + ‖q j‖ ^ degree i j)

private def route {L : ℕ} (C : Matrix (Fin L) (Fin L) ℝ) (h : C.det ≠ 0) :
    EuclideanLoops L ≃L[ℝ] EuclideanLoops L := Classical.choose (exists_selected_routing C h)

private theorem route_matrix {L : ℕ} (C : Matrix (Fin L) (Fin L) ℝ) (h : C.det ≠ 0) :
    LinearMap.toMatrix (loopProductBasis (Fin L)) (loopProductBasis (Fin L)) (route C h).toLinearMap =
      Matrix.kronecker C (1 : Matrix (Fin 4) (Fin 4) ℝ) :=
  Classical.choose_spec (exists_selected_routing C h)

/-- The chosen continuous equivalence acts by the actual selected matrix on
each of the four Euclidean coordinates. -/
theorem selected_route_coordinate {L : ℕ} (C : Matrix (Fin L) (Fin L) ℝ) (h : C.det ≠ 0)
    (k : EuclideanLoops L) (i : Fin L) (ν : Fin 4) :
    route C h k i ν = ∑ j, C i j * k j ν :=
  selected_routing_apply C (route C h) (route_matrix C h) k i ν

private def anisotropicUnrouted {P : Type} (g : AnisotropicGraphData P)
    (p : P) (q : EuclideanLoops g.loops) : ℂ :=
  (∏ j, selectedLine (g.law j) (g.scale j) (g.mass j) (q j)) • g.remainder p q

def anisotropicIntegrand {P : Type} (g : AnisotropicGraphData P)
    (p : P) (k : EuclideanLoops g.loops) : ℂ :=
  (fourierLoopFactor g.loops)⁻¹ • anisotropicUnrouted g p (route g.C g.det_ne_zero k + g.shift p)

/-- On the fixed graph the independent-line criterion proves integrability of
the complete graph and its actual normalization. -/
theorem anisotropicGraph_bounded {P : Type} (g : AnisotropicGraphData P) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p,
      Integrable (anisotropicIntegrand g p) (Measure.pi fun _ => volume) ∧
      (∫ k, ‖anisotropicIntegrand g p k‖ ∂(Measure.pi fun _ => volume)) ≤ B := by
  letI := g.law_finite
  have hf : ∀ p, AEStronglyMeasurable (anisotropicUnrouted g p) (Measure.pi fun _ => volume) := by
    intro p
    unfold anisotropicUnrouted
    apply AEStronglyMeasurable.smul _ (g.remainder_measurable p).aestronglyMeasurable
    apply Measurable.aestronglyMeasurable
    exact Finset.measurable_prod _ fun j _ =>
      (selectedLine_measurable (g.law j) (g.scale j) (g.mass j)).comp (measurable_pi_apply j)
  have hb : ∀ p q, ‖anisotropicUnrouted g p q‖ ≤ ∑ i, g.coeff i * ∏ j,
      ((1 + ‖q j‖ ^ g.degree i j) * laplace (g.law j) ((g.scale j) ^ 2 * ‖q j‖ ^ 2) /
        (‖q j‖ ^ 2 + (g.mass j) ^ 2)) := by
    intro p q
    simpa only [anisotropicUnrouted, selectedWeight_eq_full_laplace (g.law _)
      (g.law_nonnegative _) (g.law_no_zero _)] using
        complete_envelope_selected_bound g.law g.scale g.mass g.degree g.coeff q
          (g.remainder p q) (g.remainder_bound p q)
  have hi := optimized_selected_lines g.law g.law_nonnegative g.law_no_zero g.scale g.mass g.maxDegree
    g.degree g.coeff g.scale_pos g.degree_nonneg g.degree_le_max g.coeff_nonneg g.line_budget g.C
    (loopProductBasis (Fin g.loops)) (route g.C g.det_ne_zero) (route_matrix g.C g.det_ne_zero)
    g.shift (anisotropicUnrouted g) hf hb
  let B := |Matrix.det g.C| ^ (-4 : ℝ) / fourierLoopFactor g.loops *
    ∑ i, g.coeff i * ∏ j, (lineMomentBound (g.law j) (g.scale j) 0 +
      lineMomentBound (g.law j) (g.scale j) (g.degree i j))
  refine ⟨max 0 B, le_max_left _ _, fun p => ⟨(hi p).1.smul _, ?_⟩⟩
  have he : (fun k => ‖anisotropicIntegrand g p k‖) =
      (fun k => ‖anisotropicUnrouted g p (route g.C g.det_ne_zero k + g.shift p)‖ /
        (2 * π) ^ (4 * Fintype.card (Fin g.loops))) := by
    ext k
    rw [anisotropicIntegrand, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (fourierLoopFactor_pos _).le)]
    simp only [fourierLoopFactor, Fintype.card_fin, div_eq_inv_mul]
  rw [he]
  exact (by simpa only [B, fourierLoopFactor, Fintype.card_fin] using (hi p).2 : _ ≤ B).trans
    (le_max_right _ _)

/-- The actual common geometric sample and all correlated heat lapse values
stay in the same coefficient. `budget` is the scalar moment hypothesis. -/
structure JointHeatGraphData (P X : Type) [MeasurableSpace X] where
  loops : ℕ
  terms : ℕ
  C : Matrix (Fin loops) (Fin loops) ℝ
  det_ne_zero : C.det ≠ 0
  shift : P → EuclideanLoops loops
  law : Measure X
  finite : IsFiniteMeasure law
  lapse : Fin loops → X → ℝ
  lapse_pos : ∀ᵐ x ∂law, ∀ j, 0 < lapse j x
  lapse_measurable : ∀ j, Measurable (lapse j)
  mass : Fin loops → ℝ
  degree : Fin terms → Fin loops → ℝ
  coeff : Fin terms → X → ℝ
  degree_nonneg : ∀ i j, 0 ≤ degree i j
  coeff_nonneg : ∀ i x, 0 ≤ coeff i x
  budget : Integrable (RevisionJointHeat.jointBudget lapse degree coeff) law
  remainder : P → X → EuclideanLoops loops → ℂ
  remainder_measurable : ∀ p, StronglyMeasurable (Function.uncurry (remainder p))
  remainder_bound : ∀ p x q, ‖remainder p x q‖ ≤ ∑ i, coeff i x * ∏ j, (1 + ‖q j‖ ^ degree i j)

def jointHeatMeasure {P X : Type} [MeasurableSpace X] (g : JointHeatGraphData P X) :
    Measure (X × EuclideanLoops g.loops) := g.law.prod (Measure.pi fun _ => volume)

def jointHeatIntegrand {P X : Type} [MeasurableSpace X] (g : JointHeatGraphData P X)
    (p : P) (z : X × EuclideanLoops g.loops) : ℂ :=
  (fourierLoopFactor g.loops)⁻¹ • RevisionJointHeat.heatGraph g.lapse g.mass
    (route g.C g.det_ne_zero) g.shift g.remainder p z

/-- The absolute product integral is obtained by applying the conditional
bound to the actual graph and integrating the joint budget. -/
theorem jointHeatGraph_bounded {P X : Type} [MeasurableSpace X] (g : JointHeatGraphData P X) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p,
      Integrable (jointHeatIntegrand g p) (jointHeatMeasure g) ∧
      (∫ z, ‖jointHeatIntegrand g p z‖ ∂jointHeatMeasure g) ≤ B := by
  letI := g.finite
  let B := (|Matrix.det g.C| ^ (-4 : ℝ) / fourierLoopFactor g.loops) *
    ∫ x, RevisionJointHeat.jointBudget g.lapse g.degree g.coeff x ∂g.law
  have hi := RevisionJointHeat.joint_heat_selected_lines g.law g.lapse g.mass g.degree g.coeff
    g.lapse_pos g.lapse_measurable g.degree_nonneg g.coeff_nonneg g.C (route g.C g.det_ne_zero)
    (route_matrix g.C g.det_ne_zero) g.shift g.remainder g.remainder_measurable g.remainder_bound g.budget
  refine ⟨max 0 B, le_max_left _ _, fun p => ?_⟩
  have hi' : Integrable (jointHeatIntegrand g p) (jointHeatMeasure g) := (hi p).1.smul _
  refine ⟨hi', ?_⟩
  unfold jointHeatMeasure
  rw [integral_prod _ hi'.norm]
  have h : ∀ z, ‖jointHeatIntegrand g p z‖ =
      ‖RevisionJointHeat.heatGraph g.lapse g.mass (route g.C g.det_ne_zero) g.shift g.remainder p z‖ /
        (2 * π) ^ (4 * Fintype.card (Fin g.loops)) := by
    intro z
    rw [jointHeatIntegrand, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (fourierLoopFactor_pos _).le)]
    simp only [fourierLoopFactor, Fintype.card_fin, div_eq_inv_mul]
  simp_rw [h]
  exact (by simpa only [B, fourierLoopFactor, Fintype.card_fin] using (hi p).2.1 : _ ≤ B).trans
    (le_max_right _ _)

end UV.ContinuationGraph
