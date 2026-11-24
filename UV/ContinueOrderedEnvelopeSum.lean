import UV.ContinueOrderedEnvelopeJoint
import UV.ContinueOrderedCurrentGrowth
import UV.ContinueWilsonGraphHopSum

/-! Summing and integrating the signed charged paths and mixed photon
currents for each labelled connected routing. The same constant controls
all external momenta after extracting the two transverse soft factors. -/

noncomputable section

open MeasureTheory UV.SectorPlane Filter

namespace UV

variable {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}

def OrderedGraphProbe.degree (probe : OrderedGraphProbe n) (edgeCount : ℕ) : ℕ :=
  match probe with
  | .vacuum => 2*edgeCount
  | .pair .. => 2*edgeCount+2

omit [DecidableEq E] in
private theorem ordered_joint_path_cost (src dst : E → OrderedGraphVertices n) (kind : E → OrderedPhotonKind)
    (probe : OrderedGraphProbe n) (N : OrderedGraphVertices n → ℕ) (d : OrderedGraphHops N) :
    let P := fun v => OrderedTwoBandPath.returnPath (d v)
    probe.cost P * orderedGraphPathCost src dst kind P ≤
      ∏ v, (orderedVertexCost (d v))^(probe.degree (Fintype.card E)) := by
  intro P
  cases probe with
  | vacuum =>
    simpa only [OrderedGraphProbe.cost,one_mul,OrderedGraphProbe.degree,orderedGraphPathCost,P] using
      ordered_edges_growth src dst kind N d
  | pair s t e f =>
    exact ordered_external_edges_growth src dst kind N d s t

def orderedVertexLogCost {j : ℕ} (r : ℕ) (m σ g : ℝ) (φ : OrderedHopPhases j)
    (d : Fin j → OrderedHopStep) : ℝ := (orderedVertexCost d)^r * ‖orderedHopLogWord m σ g φ d‖

theorem ordered_vertex_log_cost_nonneg {j : ℕ} (r : ℕ) (m σ g : ℝ) (φ : OrderedHopPhases j)
    (d : Fin j → OrderedHopStep) : 0 ≤ orderedVertexLogCost r m σ g φ d := by
  have hL := orderedHop_path_length_nonneg d
  unfold orderedVertexLogCost orderedVertexCost
  positivity

variable (src dst : E → OrderedGraphVertices n) (B : WilsonIncidenceBasis (groundedNetworkIncidence src dst).row)
    (kind : E → OrderedPhotonKind) (probe : OrderedGraphProbe n)

theorem ordered_joint_graph_pointwise {N : OrderedGraphVertices n → ℕ}
    (φ : (v : OrderedGraphVertices n) → OrderedHopPhases (N v)) (m σ g : ℝ) {a : ℝ}
    (ha : 0 ≤ a) (k : OSFourSpace) (z : OrderedGraphHops N × (B.Chord → OSFourSpace)) :
    ‖orderedJointGraph src dst B kind probe φ m σ g a k z‖ ≤ probe.soft k *
      ((∏ v, orderedVertexLogCost (probe.degree (Fintype.card E)) m σ g (φ v) (z.1 v)) *
        ∏ c : B.Chord, (kind c).envelope a (z.2 c)) := by
  let P := fun v => OrderedTwoBandPath.returnPath (z.1 v)
  let W := ∏ v, ‖orderedHopLogWord m σ g (φ v) (z.1 v)‖
  let H := ∏ c : B.Chord, (kind c).envelope a (z.2 c)
  let K := fun v => (orderedVertexCost (z.1 v))^(probe.degree (Fintype.card E))
  have hH : 0 ≤ H := Finset.prod_nonneg fun c _ => (kind c).nonneg _ _
  have hW : 0 ≤ W := Finset.prod_nonneg fun v _ => norm_nonneg _
  have hP := probe.factor_bound P ha k
  have hG := ordered_graph_sewing_bound src dst B kind P ha (probe.injection k) z.2
  unfold orderedJointGraph
  rw [norm_mul,norm_prod,norm_mul]
  calc
    _ ≤ W*((probe.cost P*probe.soft k)*(orderedGraphPathCost src dst kind P*H)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hP hG (norm_nonneg _) ((norm_nonneg _).trans hP)) hW
    _ = (probe.cost P * orderedGraphPathCost src dst kind P) * (probe.soft k*(W*H)) := by ring
    _ ≤ (∏ v, K v) * (probe.soft k*(W*H)) := mul_le_mul_of_nonneg_right
      (ordered_joint_path_cost src dst kind probe N z.1) (mul_nonneg (probe.soft_nonneg _) (mul_nonneg hW hH))
    _ = _ := by simp only [orderedVertexLogCost,Finset.prod_mul_distrib]; dsimp only [K,W,H]; ring

def orderedGraphMass {N : OrderedGraphVertices n → ℕ}
    (φ : (v : OrderedGraphVertices n) → OrderedHopPhases (N v)) (m σ g a : ℝ) :=
  (∏ v, ∫ x, orderedVertexLogCost (probe.degree (Fintype.card E)) m σ g (φ v) x) *
    ∏ c : B.Chord, ∫ x, (kind c).envelope a x

/-- Absolute integration in all based path and independent photon variables
at fixed hop counts. The bound is uniform in all external transfers. -/
theorem ordered_joint_graph_integral {N : OrderedGraphVertices n → ℕ}
    (φ : (v : OrderedGraphVertices n) → (j : ℕ) → OrderedHopPhases j) (hφ : ∀ v j i s, Measurable (φ v j i s))
    {m σ g a : ℝ} (hσ : 0 < σ) (hg : 2*|g| < m) (ha : 0 < a) (k : OSFourSpace) :
    let F := orderedJointGraph src dst B kind probe (fun v => φ v (N v)) m σ g a k
    Integrable F ∧ (∫ z, ‖F z‖) ≤ probe.soft k * orderedGraphMass src dst B kind probe (fun v => φ v (N v)) m σ g a := by
  intro F
  let r := probe.degree (Fintype.card E)
  let V := fun (d : OrderedGraphHops N) => ∏ v, orderedVertexLogCost r m σ g (φ v (N v)) (d v)
  let H := fun q : B.Chord → OSFourSpace => ∏ c : B.Chord, (kind c).envelope a (q c)
  have hV : Integrable V := Integrable.fintype_prod_dep (fun v : OrderedGraphVertices n =>
    (orderedVertexCost_log_summable hσ hg r (φ v) (hφ v)).1 (N v))
  have hH : Integrable H := Integrable.fintype_prod (fun c : B.Chord => (kind c).integrable ha)
  have hBound := ordered_joint_graph_pointwise src dst B kind probe (fun v => φ v (N v)) m σ g ha.le k
  have hDom := (hV.mul_prod hH).const_mul (probe.soft k)
  have hF : Integrable F := hDom.mono' (measurable_orderedJointGraph src dst B kind probe _ (fun v => hφ v (N v))
    m σ g a k).aestronglyMeasurable (ae_of_all _ hBound)
  refine ⟨hF,(integral_mono hF.norm hDom hBound).trans_eq ?_⟩
  rw [integral_const_mul,Measure.volume_eq_prod,integral_prod_mul V H]
  simp only [V,H,orderedGraphMass,integral_fintype_prod_volume_eq_prod,r]

/-- All independent positive hop counts at all charged vertices are summed
absolutely, after the joint Lebesgue integrations. For a two-point graph the
same finite constant multiplies the squared full external four-momentum. -/
theorem ordered_joint_graph_all_lengths
    (φ : (v : OrderedGraphVertices n) → (j : ℕ) → OrderedHopPhases j) (hφ : ∀ v j i s, Measurable (φ v j i s))
    {m σ g a : ℝ} (hσ : 0 < σ) (hg : 2*|g| < m) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : OSFourSpace,
      let F := fun (N : OrderedGraphVertices n → ℕ) =>
        orderedJointGraph src dst B kind probe (fun v => φ v (N v)) m σ g a k
      (∀ N, Integrable (F N)) ∧ Summable (fun N => ∫ z, ‖F N z‖) ∧
        (∑' N, ∫ z, ‖F N z‖) ≤ probe.soft k * C := by
  let M := fun N : OrderedGraphVertices n → ℕ => orderedGraphMass src dst B kind probe
    (fun v => φ v (N v)) m σ g a
  have hm (N) : 0 ≤ M N := mul_nonneg (Finset.prod_nonneg fun v _ => integral_nonneg fun _ =>
    ordered_vertex_log_cost_nonneg _ _ _ _ _ _) (Finset.prod_nonneg fun c _ => integral_nonneg fun _ => (kind c).nonneg _ _)
  have hs : Summable M := (wilson_summable_independent_lengths
    (g := fun v j => ∫ d, orderedVertexLogCost (probe.degree (Fintype.card E)) m σ g (φ v j) d)
    (fun v j => integral_nonneg fun d => ordered_vertex_log_cost_nonneg _ _ _ _ _ d)
    (fun v => (orderedVertexCost_log_summable hσ hg _ (φ v) (hφ v)).2)).mul_right _
  refine ⟨∑' N, M N,tsum_nonneg hm, fun k => ?_⟩
  intro F
  have hb := fun N => ordered_joint_graph_integral src dst B kind probe (N := N) φ hφ hσ hg ha k
  have hAbs : Summable (fun N => ∫ z, ‖F N z‖) := Summable.of_nonneg_of_le
    (fun N => integral_nonneg fun z => norm_nonneg _) (fun N => (hb N).2) (hs.mul_left (probe.soft k))
  exact ⟨fun N => (hb N).1,hAbs,(hAbs.tsum_le_tsum (fun N => (hb N).2)
    (hs.mul_left (probe.soft k))).trans_eq (tsum_mul_left ..)⟩

/-- Quadratic softness of the complex two-point amplitude after both the
integrations and the infinite sum over the internal charged hop counts. -/
theorem ordered_summed_two_point_bound
    (s t : OrderedGraphVertices n) (e f : UnitVector Spatial)
    (φ : (v : OrderedGraphVertices n) → (j : ℕ) → OrderedHopPhases j)
    (hφ : ∀ v j i b, Measurable (φ v j i b))
    {m σ g a : ℝ} (hσ : 0 < σ) (hg : 2*|g| < m) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : OSFourSpace,
      let F := fun (N : OrderedGraphVertices n → ℕ) =>
        orderedJointGraph src dst B kind (.pair s t e f) (fun v => φ v (N v)) m σ g a k
      Summable (fun N => ∫ z, F N z) ∧
      ‖∑' N, ∫ z, F N z‖ ≤ C * ((orderedPhotonChart k).1^2 + ‖(orderedPhotonChart k).2‖^2) := by
  obtain ⟨C,hC,h⟩ := ordered_joint_graph_all_lengths src dst B kind (.pair s t e f) φ hφ hσ hg ha
  refine ⟨C,hC,fun k => ?_⟩
  intro F
  obtain ⟨_,hs,hb⟩ := h k
  have hf : Summable (fun N => ‖∫ z, F N z‖) := Summable.of_nonneg_of_le
    (fun N => norm_nonneg _) (fun N => norm_integral_le_integral_norm _) hs
  exact ⟨hf.of_norm,(norm_tsum_le_tsum_norm hf).trans
    ((hf.tsum_le_tsum (fun N => norm_integral_le_integral_norm _) hs).trans
      (hb.trans_eq (mul_comm _ _)))⟩

end UV
