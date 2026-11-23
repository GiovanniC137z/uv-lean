import UV.RevisionBoundaryDensity
import UV.VerifyVisitCyclic
import UV.ContinueVisitCutoffLimit

/-! A closed normal path can carry its actual starting position as a
mark. The relative return is then the pushforward of the single
weighted law of the starting and measured positions. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace UV.ContinueVisitMarkedHardy

open UV.RevisionBoundary UV.VerifyVisitCyclic UV.ContinueVisitCutoffLimit

/-- The mark law is ν(dr) times the conditional position density of
the actual fiber state. -/
def markedBasepointLaw (ν : Measure ℝ) (φ : ℝ → ℝ → ℂ) : Measure (ℝ × ℝ) :=
  (ν.prod volume).withDensity (fun p => bornDensity (φ p.1) p.2)

def basepointKineticEnergy (ν : Measure ℝ) (g : ℝ → ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ r, ∫⁻ y : ℝ, ENNReal.ofReal (‖g r y‖ ^ (2 : ℕ)) ∂volume ∂ν

private theorem marked_basepoint_density_measurable {φ : ℝ → ℝ → ℂ}
    (hφ : Measurable (Function.uncurry φ)) :
    Measurable (fun p : ℝ × ℝ => bornDensity (φ p.1) p.2) :=
  (hφ.norm.pow_const 2).ennreal_ofReal

theorem marked_basepoint_lintegral (ν : Measure ℝ) [SFinite ν] {φ : ℝ → ℝ → ℂ}
    (hφ : Measurable (Function.uncurry φ)) {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p, f p ∂markedBasepointLaw ν φ) =
      ∫⁻ r, ∫⁻ y : ℝ, bornDensity (φ r) y * f (r, y) ∂volume ∂ν := by
  have hd := marked_basepoint_density_measurable hφ
  rw [markedBasepointLaw, lintegral_withDensity_eq_lintegral_mul _ hd hf]
  exact lintegral_prod _ (hd.mul hf).aemeasurable

theorem marked_basepoint_law_mass (ν : Measure ℝ) [SFinite ν] {φ : ℝ → ℝ → ℂ}
    (hφ : Measurable (Function.uncurry φ)) :
    markedBasepointLaw ν φ univ = ∫⁻ r, ∫⁻ y : ℝ, bornDensity (φ r) y ∂volume ∂ν := by
  have h := marked_basepoint_lintegral ν hφ (f := fun _ => 1) measurable_const
  simpa only [lintegral_const, one_mul, mul_one] using h

theorem marked_basepoint_law_isFinite_of_normalized (ν : Measure ℝ) [IsFiniteMeasure ν]
    {φ : ℝ → ℝ → ℂ} (hφ : Measurable (Function.uncurry φ))
    (hnorm : ∀ᵐ r ∂ν, (∫⁻ y : ℝ, bornDensity (φ r) y) = 1) :
    IsFiniteMeasure (markedBasepointLaw ν φ) := by
  refine ⟨?_⟩
  rw [marked_basepoint_law_mass ν hφ, lintegral_congr_ae hnorm, lintegral_const, one_mul]
  exact measure_lt_top ν univ

theorem marked_basepoint_diagonal_null (ν : Measure ℝ) (φ : ℝ → ℝ → ℂ) :
    markedBasepointLaw ν φ {p | p.2 = p.1} = 0 := by
  apply withDensity_absolutelyContinuous
  rw [Measure.prod_apply (measurableSet_eq_fun measurable_snd measurable_fst)]
  have hs (r : ℝ) : Prod.mk r ⁻¹' {p : ℝ × ℝ | p.2 = p.1} = ({r} : Set ℝ) := rfl
  simp_rw [hs, measure_singleton, lintegral_zero]

/-- Translate each fiber while preserving the joint dependence of
the absolute and relative positions. -/
theorem marked_relative_lintegral (ν : Measure ℝ) [SFinite ν] {φ : ℝ → ℝ → ℂ}
    (hφ : Measurable (Function.uncurry φ)) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ d, f d ∂(markedBasepointLaw ν φ).map relativeNormal) =
      ∫⁻ r, ∫⁻ d : ℝ, bornDensity (fun s => φ r (r + s)) d * f d ∂volume ∂ν := by
  have hr : Measurable relativeNormal := by unfold relativeNormal; fun_prop
  rw [lintegral_map hf hr]
  change (∫⁻ p, (f ∘ relativeNormal) p ∂markedBasepointLaw ν φ) = _
  rw [marked_basepoint_lintegral ν hφ (hf.comp hr)]
  apply lintegral_congr
  intro r
  let F := fun y : ℝ => bornDensity (φ r) y * f (y - r)
  have hF : Measurable F := by
    unfold F
    have hφr : Measurable (φ r) := hφ.of_uncurry_left
    have hd : Measurable (bornDensity (φ r)) := (hφr.norm.pow_const 2).ennreal_ofReal
    exact hd.mul (hf.comp (measurable_id.sub_const r))
  change (∫⁻ y, F y) = _
  rw [← (measurePreserving_add_left (volume : Measure ℝ) r).lintegral_comp hF]
  simp [F, bornDensity]

theorem marked_relative_cyclic_return (ν : Measure ℝ) [IsFiniteMeasure ν]
    {T : ℝ} (hT : 0 < T) {φ : ℝ → ℝ → ℂ} (hφ : Measurable (Function.uncurry φ)) :
    cyclicJointReturn T (markedBasepointLaw ν φ) =
      ∫⁻ r, densityReturn T (bornDensity (fun s => φ r (r + s))) ∂ν := by
  letI : SigmaFinite (markedBasepointLaw ν φ) := by
    unfold markedBasepointLaw bornDensity
    infer_instance
  have hr : Measurable relativeNormal := by unfold relativeNormal; fun_prop
  letI : SFinite ((markedBasepointLaw ν φ).map relativeNormal) := by infer_instance
  rw [cyclic_joint_return_eq, ← uncut_visit_first_moment hT,
    marked_relative_lintegral ν hφ (uncut_visit_measurable T)]
  apply lintegral_congr
  intro r
  unfold uncutVisit densityReturn
  simp_rw [mul_left_comm (bornDensity (fun s => φ r (r + s)) _) (ENNReal.ofReal (1 / (2 * Real.pi)))]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The normal derivative is shifted by the same amount as the
state, so its observably relevant energy norm is preserved. -/
theorem translated_nodal_state_return_bound {T : ℝ} (hT : 0 < T) (r : ℝ)
    {φ g : ℝ → ℂ} (hφc : Continuous φ) (hg : MemLp g 2 volume) (h0 : φ r = 0)
    (hrep : ∀ y, φ y - φ r = ∫ t in r..y, g t) :
    densityReturn T (bornDensity (fun s => φ (r + s))) ≤
      ENNReal.ofReal (2 / Real.pi) * ∫⁻ y, ENNReal.ofReal (‖g y‖ ^ (2 : ℕ)) := by
  let C := fun d => φ (r + d)
  let G := fun s => g (r + s)
  have hC : Continuous C := by unfold C; fun_prop
  have hG : MemLp G 2 volume :=
    hg.comp_measurePreserving (measurePreserving_add_left (volume : Measure ℝ) r)
  have hGrep (d : ℝ) : C d = ∫ s in (0 : ℝ)..d, G s := by
    unfold C G
    rw [intervalIntegral.integral_comp_add_left, add_zero, ← hrep, h0, sub_zero]
  have hB := nodal_state_return_bound hT hC hG hGrep
  have hEmb : MeasurableEmbedding (fun s : ℝ => r + s) :=
    (Homeomorph.addLeft r).measurableEmbedding
  have hE := (measurePreserving_add_left (volume : Measure ℝ) r).lintegral_comp_emb hEmb
    (fun y => ENNReal.ofReal (‖g y‖ ^ (2 : ℕ)))
  change densityReturn T (bornDensity C) ≤ _
  rwa [show (∫⁻ y, ENNReal.ofReal (‖G y‖ ^ (2 : ℕ))) = _ from hE] at hB

/-- A translated Hardy inequality applied at each retained basepoint
bounds the actual correlated return by its integrated normal kinetic
energy. The same law appears on the left and in the disintegration. -/
theorem marked_relative_hardy_bound (ν : Measure ℝ) [IsFiniteMeasure ν]
    {T : ℝ} (hT : 0 < T) {φ g : ℝ → ℝ → ℂ} (hφ : Measurable (Function.uncurry φ))
    (hFibers : ∀ᵐ r ∂ν, Continuous (φ r) ∧ MemLp (g r) 2 volume ∧ φ r r = 0 ∧
      ∀ y, φ r y - φ r r = ∫ t in r..y, g r t) :
    cyclicJointReturn T (markedBasepointLaw ν φ) ≤
      ENNReal.ofReal (2 / Real.pi) * basepointKineticEnergy ν g := by
  rw [marked_relative_cyclic_return ν hT hφ, basepointKineticEnergy, ← lintegral_const_mul' _ _
    ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hFibers] with r hr
  exact translated_nodal_state_return_bound hT r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2

theorem marked_relative_hardy_finite (ν : Measure ℝ) [IsFiniteMeasure ν]
    {T : ℝ} (hT : 0 < T) {φ g : ℝ → ℝ → ℂ} (hφ : Measurable (Function.uncurry φ))
    (hFibers : ∀ᵐ r ∂ν, Continuous (φ r) ∧ MemLp (g r) 2 volume ∧ φ r r = 0 ∧
      ∀ y, φ r y - φ r r = ∫ t in r..y, g r t)
    (hK : basepointKineticEnergy ν g ≠ ⊤) :
    cyclicJointReturn T (markedBasepointLaw ν φ) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK)
    (marked_relative_hardy_bound ν hT hφ hFibers)

private theorem marked_relative_fiber_cost_measurable (T : ℝ) {φ : ℝ → ℝ → ℂ}
    (hφ : Measurable (Function.uncurry φ)) :
    Measurable (fun r => densityReturn T (bornDensity (fun s => φ r (r + s)))) := by
  have hR : Measurable (fun p : ℝ × ℝ => (p.1, p.1 + p.2)) :=
    measurable_fst.prodMk (measurable_fst.add measurable_snd)
  have hState : Measurable (fun p : ℝ × ℝ => φ p.1 (p.1 + p.2)) := hφ.comp hR
  have hD : Measurable (fun p : ℝ × ℝ => bornDensity (φ p.1) (p.1 + p.2)) :=
    (hState.norm.pow_const 2).ennreal_ofReal
  have hCost : Measurable (returnCost T) := by
    unfold returnCost
    exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)
  have hF : Measurable (Function.uncurry (fun r s =>
      bornDensity (φ r) (r + s) * returnCost T s)) := hD.mul (hCost.comp measurable_snd)
  unfold densityReturn
  exact measurable_const.mul (hF.lintegral_prod_right (ν := (volume : Measure ℝ)))

/-- A finite marked cost forces nodes at almost every retained
starting point when the fiber states are continuous. -/
theorem finite_marked_relative_return_ae_node (ν : Measure ℝ) [IsFiniteMeasure ν]
    {T : ℝ} (hT : 0 < T) {φ : ℝ → ℝ → ℂ} (hφ : Measurable (Function.uncurry φ))
    (hCont : ∀ᵐ r ∂ν, Continuous (φ r))
    (hFin : cyclicJointReturn T (markedBasepointLaw ν φ) ≠ ⊤) :
    ∀ᵐ r ∂ν, φ r r = 0 := by
  rw [marked_relative_cyclic_return ν hT hφ] at hFin
  have hF := ae_lt_top (marked_relative_fiber_cost_measurable T hφ) hFin
  filter_upwards [hCont, hF] with r hr hf
  by_contra hn
  have hcr : Continuous (fun s : ℝ => φ r (r + s)) := hr.comp (continuous_const.add continuous_id)
  have hnr : (fun s : ℝ => φ r (r + s)) 0 ≠ 0 := by simpa only [add_zero] using hn
  exact hf.ne (nonnodal_state_return_diverges hT hcr hnr)

theorem marked_relative_return_finite_iff_ae_node (ν : Measure ℝ) [IsFiniteMeasure ν]
    {T : ℝ} (hT : 0 < T) {φ g : ℝ → ℝ → ℂ} (hφ : Measurable (Function.uncurry φ))
    (hFibers : ∀ᵐ r ∂ν, Continuous (φ r) ∧ MemLp (g r) 2 volume ∧
      ∀ y, φ r y - φ r r = ∫ t in r..y, g r t)
    (hK : basepointKineticEnergy ν g ≠ ⊤) :
    cyclicJointReturn T (markedBasepointLaw ν φ) ≠ ⊤ ↔ ∀ᵐ r ∂ν, φ r r = 0 := by
  constructor
  · exact finite_marked_relative_return_ae_node ν hT hφ (hFibers.mono fun _ h => h.1)
  · intro hNode
    apply marked_relative_hardy_finite ν hT hφ _ hK
    filter_upwards [hFibers, hNode] with r hf hn
    exact ⟨hf.1, hf.2.1, hn, hf.2.2⟩

end UV.ContinueVisitMarkedHardy
