import UV.ContinueWilsonReturnCurrent
import UV.ContinueWilsonGraphTwoPoint

/-! Two external conserved currents and every internally sewn photon on
a finite collection of closed polygons. The absolute envelope counts the
two powers of perimeter at each incidence of each vertex. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set UV.SectorPlane
open scoped Topology RealInnerProductSpace BigOperators

namespace UV

variable {V C D : Type*} [Fintype V] [DecidableEq V] [Fintype C] [Fintype D]

structure WilsonCurrentGraph (V C D : Type*) where
  first : V
  second : V
  chord : C → V × V
  tree : D → V × V

def WilsonCurrentGraph.edge (P : V → WilsonClosedPolygon) (i : V × V) : WilsonPolygonEdge := ⟨P i.1,P i.2⟩

def wilsonVertexExponent (v j : V) : ℕ := if j = v then 2 else 0

def WilsonCurrentGraph.degree (G : WilsonCurrentGraph V C D) (v : V) : ℕ :=
  wilsonVertexExponent G.first v + wilsonVertexExponent G.second v +
  (∑ i, (wilsonVertexExponent (G.chord i).1 v + wilsonVertexExponent (G.chord i).2 v)) +
  ∑ j, (wilsonVertexExponent (G.tree j).1 v + wilsonVertexExponent (G.tree j).2 v)

private theorem wilson_one_incidence (p : V → ℝ) (v : V) : ∏ j, p j ^ wilsonVertexExponent v j = p v ^ 2 := by
  classical
  simp [wilsonVertexExponent]

private theorem wilson_edge_powers {J : Type*} [Fintype J] (edges : J → V × V) (p : V → ℝ) :
    (∏ v, p v ^ (∑ j, (wilsonVertexExponent (edges j).1 v + wilsonVertexExponent (edges j).2 v))) =
      ∏ j, (p (edges j).1)^2 * (p (edges j).2)^2 := by
  simp_rw [←Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  simp only [pow_add,Finset.prod_mul_distrib,wilson_one_incidence]

theorem WilsonCurrentGraph.perimeter_factors (G : WilsonCurrentGraph V C D) (P : V → WilsonClosedPolygon) :
    (∏ v, (P v).perimeter ^ G.degree v) = (P G.first).perimeter^2*(P G.second).perimeter^2 *
      wilsonRoutedPhotonCost (fun i => WilsonCurrentGraph.edge P (G.chord i)) (fun i => WilsonCurrentGraph.edge P (G.tree i)) := by
  simp only [degree,pow_add,Finset.prod_mul_distrib,wilson_one_incidence,wilson_edge_powers,
    wilsonRoutedPhotonCost,edge,WilsonPolygonEdge.cost,mul_assoc]

def WilsonCurrentGraph.kernel (G : WilsonCurrentGraph V C D) (χ : OSFourSpace → ℂ) (P : V → WilsonClosedPolygon)
    (b : OSFourSpace → D → OSFourSpace) (a : D → C → ℝ) (y : OSFourSpace) (q : C → OSFourSpace) : ℂ :=
  wilsonRoutedPhotonProduct χ (fun i => WilsonCurrentGraph.edge P (G.chord i)) (fun e => WilsonCurrentGraph.edge P (G.tree e))
    (fun k e => wilsonAffineTransfer (b y e) (a e) k) q

def WilsonCurrentGraph.twoPoint (G : WilsonCurrentGraph V C D) (χ : OSFourSpace → ℂ) (P : V → WilsonClosedPolygon)
    (b : OSFourSpace → D → OSFourSpace) (a : D → C → ℝ) (u v w : UnitVector OSFourSpace) (r : ℝ) : ℂ :=
  ∫ q, (P G.first).softMark χ u v r * (P G.second).softMark χ (wilsonOppositeDirection u) w r *
    G.kernel χ P b a (r • u.val) q ∂Measure.pi (fun _ : C => volume)

def WilsonCurrentGraph.coefficient (G : WilsonCurrentGraph V C D) (χ : OSFourSpace → ℂ) (P : V → WilsonClosedPolygon)
    (b : OSFourSpace → D → OSFourSpace) (a : D → C → ℝ) (u v w : UnitVector OSFourSpace) : ℂ :=
  ∫ q, (P G.first).softCoefficient u v * (P G.second).softCoefficient (wilsonOppositeDirection u) w *
    G.kernel χ P b a 0 q ∂Measure.pi (fun _ : C => volume)

variable {ι : Type*} [Fintype ι]

def wilsonChordBudget (C : Type*) [Fintype C] (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) : ℝ :=
  ∫ q, ∏ i : C, ‖wilsonShellPhotonForm L T (q i)‖^2 ∂Measure.pi (fun _ : C => volume)

theorem wilson_chord_budget_nonneg (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) : 0 ≤ wilsonChordBudget C L T :=
  integral_nonneg (fun _ => Finset.prod_nonneg fun _ _ => sq_nonneg _)

theorem WilsonCurrentGraph.twoPoint_bound (G : WilsonCurrentGraph V C D) {L : ℝ} (hL : 0 < L)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (P : V → WilsonClosedPolygon) (b : OSFourSpace → D → OSFourSpace)
    (a : D → C → ℝ) (u v w : UnitVector OSFourSpace) (r : ℝ) :
    ‖G.twoPoint (wilsonShellPhotonForm L T) P b a u v w r‖ ≤ wilsonChordBudget C L T * ∏ j, (P j).perimeter ^ G.degree j := by
  let χ := wilsonShellPhotonForm L T
  let R := fun q : C → OSFourSpace => ∏ i, ‖χ (q i)‖^2
  let K := wilsonRoutedPhotonCost (fun i => WilsonCurrentGraph.edge P (G.chord i)) (fun e => WilsonCurrentGraph.edge P (G.tree e))
  let A := (P G.first).perimeter^2 * (P G.second).perimeter^2
  have hI : Integrable R (Measure.pi (fun _ : C => volume)) := Integrable.fintype_prod (fun _ => wilson_actual_shell_square_integrable hL T)
  rw [G.perimeter_factors]
  unfold twoPoint
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) ((hI.mul_const K).const_mul A) ?_).trans_eq
  · rw [integral_const_mul,integral_mul_const]
    change A * (wilsonChordBudget C L T * K) = _
    ring
  · apply Eventually.of_forall fun q => ?_
    dsimp only
    rw [norm_mul,norm_mul]
    exact mul_le_mul (mul_le_mul ((P G.first).softMark_bound (wilson_shell_form_le_one L T) _ _ _)
      ((P G.second).softMark_bound (wilson_shell_form_le_one L T) _ _ _) (norm_nonneg _) (sq_nonneg _))
      (wilson_routed_product_bound L T _ _ _ _) (norm_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))

omit [Fintype V] [DecidableEq V] in
theorem WilsonCurrentGraph.twoPoint_tendsto (G : WilsonCurrentGraph V C D) {L : ℝ} (hL : 0 < L)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (P : V → WilsonClosedPolygon) (b : OSFourSpace → D → OSFourSpace)
    (hb : ∀ e, ContinuousAt (b · e) 0) (a : D → C → ℝ) (ha : ∀ e, ∃ j, a e j ≠ 0) (u v w : UnitVector OSFourSpace) :
    Tendsto (G.twoPoint (wilsonShellPhotonForm L T) P b a u v w) (𝓝[≠] 0)
      (𝓝 (G.coefficient (wilsonShellPhotonForm L T) P b a u v w)) :=
  wilson_fixed_polygon_two_point_limit hL T _ _ _ hb _ ha _ _ u v w

end UV
