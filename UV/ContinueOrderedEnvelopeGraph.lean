import UV.ContinueOrderedEnvelopeMeasurable

/-! Actual graph integrals of the two Coulomb-gauge line currents of fixed
ordered paths. Free photon momenta are integrated on a conserved incidence
routing and opposite external transfers are inserted at the marked paths. -/

noncomputable section

open MeasureTheory Filter UV.SectorPlane

namespace UV

variable {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}
variable (src dst : E → Option (Fin n)) (B : WilsonIncidenceBasis (groundedNetworkIncidence src dst).row)
    (kind : E → SectorPlane.OrderedPhotonKind) (P : Option (Fin n) → SectorPlane.OrderedTwoBandPath)

def orderedGraphPathCost : ℝ :=
  ∏ e, (kind e).pathCost (P (src e)) * (kind e).pathCost (P (dst e))

omit [DecidableEq E] in
theorem orderedGraphPathCost_nonneg : 0 ≤ orderedGraphPathCost src dst kind P :=
  Finset.prod_nonneg fun e _ => mul_nonneg ((kind e).pathCost_nonneg _) ((kind e).pathCost_nonneg _)

/-- One charged path at each graph vertex, with the same path used for every
mark on that vertex, including both ends of a self-contraction. -/
def orderedGraphSewing (a : ℝ) (b : Fin n → OSFourSpace) (q : B.Chord → OSFourSpace) : ℂ :=
  ∏ e, (kind e).sewn a (P (src e)) (P (dst e)) (orderedPhotonChart (B.flow b q e))

theorem measurable_orderedGraphSewing (a : ℝ) (b : Fin n → OSFourSpace) :
    Measurable (orderedGraphSewing src dst B kind P a b) :=
  Finset.measurable_prod _ fun e _ => ((kind e).measurable_sewn _ _ _).comp
    (orderedPhotonChart.measurable.comp (B.measurable_flow b e))

theorem ordered_graph_sewing_bound {a : ℝ} (ha : 0 ≤ a) (b : Fin n → OSFourSpace) (q : B.Chord → OSFourSpace) :
    ‖orderedGraphSewing src dst B kind P a b q‖ ≤
      orderedGraphPathCost src dst kind P * ∏ c : B.Chord, (kind c).envelope a (q c) := by
  rw [orderedGraphSewing,norm_prod]
  calc
    _ ≤ ∏ e, (((kind e).pathCost (P (src e)) * (kind e).pathCost (P (dst e))) *
        (kind e).envelope a (B.flow b q e)) :=
      Finset.prod_le_prod (fun e _ => norm_nonneg _) (fun e _ => (kind e).sewn_bound _ _ _ _)
    _ ≤ _ := by
      rw [Finset.prod_mul_distrib]
      exact mul_le_mul_of_nonneg_left (B.ordered_product_bound kind ha b q)
        (orderedGraphPathCost_nonneg src dst kind P)

theorem ordered_graph_sewing_integrable {a : ℝ} (ha : 0 < a) (b : Fin n → OSFourSpace) :
    Integrable (orderedGraphSewing src dst B kind P a b) (Measure.pi (fun _ : B.Chord => volume)) :=
  ((Integrable.fintype_prod (fun c : B.Chord => (kind c).integrable ha)).const_mul
    (orderedGraphPathCost src dst kind P)).mono' (measurable_orderedGraphSewing src dst B kind P a b).aestronglyMeasurable
    (ae_of_all _ (ordered_graph_sewing_bound src dst B kind P ha.le b))

/-- Integrating the absolute value gives a finite constant uniform in every
external injection. Tree lines cost at most one after their path factors. -/
theorem ordered_graph_absolute_cost {a : ℝ} (ha : 0 < a) (b : Fin n → OSFourSpace) :
    (∫ q, ‖orderedGraphSewing src dst B kind P a b q‖ ∂Measure.pi (fun _ : B.Chord => volume)) ≤
      orderedGraphPathCost src dst kind P * ∏ c : B.Chord, ∫ x, (kind c).envelope a x := by
  have h := (Integrable.fintype_prod (fun c : B.Chord => (kind c).integrable ha)).const_mul
    (orderedGraphPathCost src dst kind P)
  apply (integral_mono (ordered_graph_sewing_integrable src dst B kind P ha b).norm h
    (ordered_graph_sewing_bound src dst B kind P ha.le b)).trans_eq
  rw [integral_const_mul,integral_fintype_prod_eq_prod]

/-- Uniform quadratic soft bound for the integrated two-point graph of
arbitrary fixed paths, at opposite external transfers and unit polarizations.
It includes each external harmonic readout. -/
theorem ordered_graph_two_point_soft {a : ℝ} (ha : 0 < a)
    (s t : Option (Fin n)) (e f : UnitVector Spatial) (k : OSFourSpace) :
    let z := orderedPhotonChart k
    let b := fun i => wilsonExternalPair s t k (some i)
    let external : ℂ := (Real.exp (-(2*a*‖z.2‖)) : ℂ) *
      ((P s).spatialCurrent z.1 z.2 e.val * (P t).spatialCurrent (-z.1) (-z.2) f.val)
    ‖∫ q, external * orderedGraphSewing src dst B kind P a b q ∂Measure.pi (fun _ : B.Chord => volume)‖ ≤
      ((3*(1+(P s).length)^2) * (3*(1+(P t).length)^2)) *
        (z.1^2+‖z.2‖^2) * (orderedGraphPathCost src dst kind P * ∏ c : B.Chord, ∫ x, (kind c).envelope a x) := by
  intro z b external
  rw [integral_const_mul,norm_mul]
  apply mul_le_mul _ ((norm_integral_le_integral_norm _).trans (ordered_graph_absolute_cost src dst B kind P ha b))
    (norm_nonneg _) (by positivity)
  unfold external
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))).trans
  exact (P s).two_external_bound (P t) z.1 z.2 e f

end UV
