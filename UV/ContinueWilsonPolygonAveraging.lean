import UV.ContinueWilsonGraphCurrent
import Mathlib.Analysis.Normed.Group.Tannery

/-! Dominated convergence over the relative displacements and all positive
hopping lengths of the closed components in a routed two-point graph.
The coefficient is computed along a specified unit direction. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set UV.SectorPlane
open scoped Topology BigOperators

namespace UV

private theorem wilson_edge_wave_joint {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {p x d : X → OSFourSpace} (hp : Continuous p) (hx : Continuous x) (hd : Continuous d) :
    Continuous (fun z => wilsonEdgeWave (p z) (x z) (d z)) := by
  apply intervalIntegral.continuous_of_dominated_interval (bound := fun _ => 1)
  · intro z
    exact (show Continuous (fun s : ℝ => thinPlaneWave (p z) (x z+s • d z)) by unfold thinPlaneWave; fun_prop).aestronglyMeasurable
  · intro z
    exact Eventually.of_forall (fun s _ => (wilson_wave_norm _ _).le)
  · exact (continuous_const (y := (1:ℝ))).intervalIntegrable (μ := volume) 0 1
  · exact Eventually.of_forall (fun s _ => by unfold thinPlaneWave; fun_prop)

private theorem wilson_polygon_joint {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {n : ℕ} {p : X → OSFourSpace} (hp : Continuous p) {d : X → Fin n → OSFourSpace} (hd : Continuous d) :
    Continuous (fun z => wilsonPolygonCurrent (wilsonReturnPolygon (d z)).displacement (n+1) (p z)) := by
  have hstep (k : ℕ) : Continuous (fun z => (wilsonReturnPolygon (d z)).displacement k) := by
    by_cases h : k < n+1
    · simpa only [wilsonReturnPolygon,wilsonExtendSteps,dif_pos h] using (wilson_return_step_continuous ⟨k,h⟩).comp hd
    · simpa only [wilsonReturnPolygon,wilsonExtendSteps,dif_neg h] using (continuous_const (y := (0:OSFourSpace)) : Continuous (fun _ : X => (0:OSFourSpace)))
  apply continuous_finset_sum
  intro k _
  apply (wilson_edge_wave_joint hp (continuous_finset_sum _ fun j _ => hstep j) (hstep k)).smul
  exact wilsonCarrierInclusion.continuous_of_finiteDimensional.comp (hstep k)

private theorem wilson_return_sewing_measurable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {n m : ℕ}
    {p : X → OSFourSpace} (hp : Continuous p) {d : X → Fin n → OSFourSpace} (hd : Continuous d)
    {e : X → Fin m → OSFourSpace} (he : Continuous e) {χ : OSFourSpace → ℂ} (hc : Continuous χ) :
    Measurable (fun z => (WilsonPolygonEdge.mk (wilsonReturnPolygon (d z)) (wilsonReturnPolygon (e z))).sewing χ (p z)) := by
  simp only [WilsonPolygonEdge.formula]
  apply Measurable.div
  · exact ((Complex.continuous_ofReal.comp ((hc.comp hp).norm.pow 2)).mul
      ((wilson_polygon_joint hp he).inner (𝕜 := ℂ) (wilson_polygon_joint hp hd))).measurable
  · exact (Complex.continuous_ofReal.comp (hp.norm.pow 2)).measurable

variable {V C D ι : Type*} [Fintype V] [DecidableEq V] [Fintype C] [Fintype D] [Fintype ι]

abbrev WilsonGraphDisplacements (n : V → ℕ) := (j : V) → Fin (n j) → OSFourSpace

def wilsonGraphReturnMeasure (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (n : V → ℕ) :
    Measure (WilsonGraphDisplacements n) := Measure.pi (fun j => Measure.pi (fun _ : Fin (n j) => wilsonDisplacementMeasure L T))

instance (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (n : V → ℕ) :
    IsProbabilityMeasure (wilsonGraphReturnMeasure L T n) := Measure.pi.instIsProbabilityMeasure _

def wilsonGraphReturnWeight (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) {n : V → ℕ}
    (d : WilsonGraphDisplacements n) : ℂ := ∏ j, wilsonReturnWeight L T (d j)

omit [DecidableEq V] in
theorem wilson_graph_return_weight_continuous {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (n : V → ℕ) : Continuous (wilsonGraphReturnWeight (n := n) L T) :=
  continuous_finset_prod _ (fun j _ => (wilson_return_weight_continuous hL T).comp (continuous_apply j))

omit [DecidableEq V] in
theorem WilsonCurrentGraph.twoPoint_measurable (G : WilsonCurrentGraph V C D) {χ : OSFourSpace → ℂ} (hχ : Continuous χ)
    (n : V → ℕ) (b : OSFourSpace → D → OSFourSpace) (a : D → C → ℝ) (u v w : UnitVector OSFourSpace) (r : ℝ) :
    Measurable (fun d : WilsonGraphDisplacements n => G.twoPoint χ (fun j => wilsonReturnPolygon (d j)) b a u v w r) := by
  let X := WilsonGraphDisplacements n × (C → OSFourSpace)
  let P := fun (z : X) j => wilsonReturnPolygon (z.1 j)
  let H := fun (z : X) => (P z G.first).softMark χ u v r * (P z G.second).softMark χ (wilsonOppositeDirection u) w r *
    G.kernel χ (P z) b a (r • u.val) z.2
  have dd (j : V) : Continuous (fun z : X => z.1 j) := (continuous_apply j).comp continuous_fst
  have hext (j : V) (l t : UnitVector OSFourSpace) : Measurable (fun z : X => (P z j).softMark χ l t r) := by
    apply measurable_const.mul
    apply Measurable.div_const
    exact (continuous_const.inner (𝕜 := ℂ) (wilson_polygon_joint (p := fun _ => r • l.val) continuous_const (dd j))).measurable
  have hH : Measurable H := by
    apply ((hext _ u v).mul (hext _ _ w)).mul
    apply Measurable.mul
    · apply Finset.measurable_prod
      intro i _
      exact wilson_return_sewing_measurable ((continuous_apply i).comp continuous_snd) (dd _) (dd _) hχ
    · apply Finset.measurable_prod
      intro j _
      exact wilson_return_sewing_measurable ((wilson_affine_transfer_continuous _ _).comp continuous_snd) (dd _) (dd _) hχ
  exact (hH.stronglyMeasurable.integral_prod_right' (ν := Measure.pi (fun _ : C => (volume : Measure OSFourSpace)))).measurable

def wilsonMomentIntegral (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (a n : ℕ) : ℝ :=
  ∫ d, ‖wilsonReturnWeight L T d‖ * (wilsonReturnPerimeter d)^a ∂Measure.pi (fun _ : Fin n => wilsonDisplacementMeasure L T)

theorem wilson_moment_integral_nonneg (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (a n : ℕ) :
    0 ≤ wilsonMomentIntegral L T a n := integral_nonneg fun _ => mul_nonneg (norm_nonneg _)
      (pow_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) _)

def WilsonCurrentGraph.envelope (G : WilsonCurrentGraph V C D) (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    {n : V → ℕ} (d : WilsonGraphDisplacements n) : ℝ :=
  wilsonChordBudget C L T * ∏ j, ‖wilsonReturnWeight L T (d j)‖ * (wilsonReturnPerimeter (d j))^(G.degree j)

theorem WilsonCurrentGraph.envelope_bound (G : WilsonCurrentGraph V C D) {L : ℝ} (hL : 0 < L)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) {n : V → ℕ} (d : WilsonGraphDisplacements n)
    (b : OSFourSpace → D → OSFourSpace) (a : D → C → ℝ) (u v w : UnitVector OSFourSpace) (r : ℝ) :
    ‖wilsonGraphReturnWeight L T d * G.twoPoint (wilsonShellPhotonForm L T) (fun j => wilsonReturnPolygon (d j)) b a u v w r‖ ≤
      G.envelope L T d := by
  rw [norm_mul,wilsonGraphReturnWeight,norm_prod]
  apply (mul_le_mul_of_nonneg_left (G.twoPoint_bound hL T _ b a u v w r) (Finset.prod_nonneg fun _ _ => norm_nonneg _)).trans_eq
  simp only [envelope,wilson_return_polygon_perimeter,Finset.prod_mul_distrib]
  ring

theorem WilsonCurrentGraph.envelope_integrable (G : WilsonCurrentGraph V C D) {L : ℝ} (hL : 0 < L)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (n : V → ℕ) :
    Integrable (G.envelope L T) (wilsonGraphReturnMeasure L T n) := by
  obtain ⟨K,hK,h⟩ := wilson_continuous_density_bounded hL T
  exact (Integrable.fintype_prod_dep (𝕜 := ℝ) (fun j => (wilson_return_moment_integral hL T hK h (G.degree j) (n j)).1)).const_mul _

theorem WilsonCurrentGraph.envelope_integral (G : WilsonCurrentGraph V C D) (L : ℝ)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (n : V → ℕ) :
    (∫ d, G.envelope L T d ∂wilsonGraphReturnMeasure L T n) =
      wilsonChordBudget C L T * ∏ j, wilsonMomentIntegral L T (G.degree j) (n j) := by
  unfold envelope wilsonGraphReturnMeasure wilsonMomentIntegral
  rw [integral_const_mul,integral_fintype_prod_eq_prod (fun j d => ‖wilsonReturnWeight L T d‖ * (wilsonReturnPerimeter d)^(G.degree j))]

/-- Includes arbitrarily many free relative displacements at each charged
vertex. Two external attachments on the same vertex contribute their separate
powers of perimeter to its single charged spin trace. -/
theorem WilsonCurrentGraph.averaged_twoPoint_limit (G : WilsonCurrentGraph V C D) {L : ℝ} (hL : 0 < L)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (n : V → ℕ)
    (b : OSFourSpace → D → OSFourSpace) (hb : ∀ e, ContinuousAt (b · e) 0)
    (a : D → C → ℝ) (ha : ∀ e, ∃ j, a e j ≠ 0) (u v w : UnitVector OSFourSpace) :
    let χ := wilsonShellPhotonForm L T
    let P := fun (d : WilsonGraphDisplacements n) j => wilsonReturnPolygon (d j)
    let μ := wilsonGraphReturnMeasure L T n
    Tendsto (fun r => ∫ d, wilsonGraphReturnWeight L T d * G.twoPoint χ (P d) b a u v w r ∂μ) (𝓝[≠] 0)
      (𝓝 (∫ d, wilsonGraphReturnWeight L T d * G.coefficient χ (P d) b a u v w ∂μ)) := by
  dsimp only
  apply tendsto_integral_filter_of_dominated_convergence (G.envelope L T) _ _ (G.envelope_integrable hL T n)
  · exact Eventually.of_forall (fun d => (G.twoPoint_tendsto hL T _ b hb a ha u v w).const_mul _)
  · exact Eventually.of_forall (fun r => ((wilson_graph_return_weight_continuous hL T n).measurable.mul
      (G.twoPoint_measurable (wilson_shell_form_continuous L T) n b a u v w r)).aestronglyMeasurable)
  · exact Eventually.of_forall (fun r => Eventually.of_forall (fun d => G.envelope_bound hL T d b a u v w r))

end UV
