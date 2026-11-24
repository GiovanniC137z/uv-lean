import UV.ContinueOrderedEnvelopeGraph
import UV.ContinueOrderedCurrentReturn
import UV.ContinueOrderedHopTrace

/-! The signed log traces, all endpoint currents and the actual affine photon
routing in one function of all independent durations, displacements and chords. -/

noncomputable section

open MeasureTheory UV.SectorPlane

namespace UV

abbrev OrderedGraphVertices (n : ℕ) := Option (Fin n)
abbrev OrderedGraphHops {n : ℕ} (N : OrderedGraphVertices n → ℕ) :=
  (v : OrderedGraphVertices n) → Fin (N v) → OrderedHopStep

inductive OrderedGraphProbe (n : ℕ)
  | vacuum
  | pair (src dst : OrderedGraphVertices n) (inPol outPol : UnitVector Spatial)

/-- Unit polarizations mark the two external legs. -/
def OrderedGraphProbe.factor {n : ℕ} (probe : OrderedGraphProbe n)
    (P : OrderedGraphVertices n → OrderedTwoBandPath) (a : ℝ) (k : OSFourSpace) : ℂ :=
  match probe with
  | .vacuum => 1
  | .pair s t e f => let z := orderedPhotonChart k
    (Real.exp (-(2*a*‖z.2‖)) : ℂ) *
      ((P s).spatialCurrent z.1 z.2 e.val * (P t).spatialCurrent (-z.1) (-z.2) f.val)

def OrderedGraphProbe.injection {n : ℕ} (probe : OrderedGraphProbe n) (k : OSFourSpace) (v : Fin n) : OSFourSpace :=
  match probe with
  | .vacuum => 0
  | .pair s t _ _ => wilsonExternalPair s t k (some v)

def OrderedGraphProbe.soft {n : ℕ} (probe : OrderedGraphProbe n) (k : OSFourSpace) : ℝ :=
  match probe with
  | .vacuum => 1
  | .pair .. => (orderedPhotonChart k).1^2+‖(orderedPhotonChart k).2‖^2

def OrderedGraphProbe.cost {n : ℕ} (probe : OrderedGraphProbe n) (P : OrderedGraphVertices n → OrderedTwoBandPath) : ℝ :=
  match probe with
  | .vacuum => 1
  | .pair s t _ _ => (3*(1+(P s).length)^2) * (3*(1+(P t).length)^2)

theorem OrderedGraphProbe.soft_nonneg {n : ℕ} (probe : OrderedGraphProbe n) (k : OSFourSpace) :
    0 ≤ probe.soft k := by cases probe <;> unfold soft <;> positivity

theorem OrderedGraphProbe.factor_bound {n : ℕ} (probe : OrderedGraphProbe n) (P : OrderedGraphVertices n → OrderedTwoBandPath)
    {a : ℝ} (ha : 0 ≤ a) (k : OSFourSpace) : ‖probe.factor P a k‖ ≤ probe.cost P * probe.soft k := by
  cases probe with
  | vacuum => simp [factor,cost,soft]
  | pair s t e f =>
    unfold factor soft cost
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_nonneg _)]
    apply (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))).trans
    exact (P s).two_external_bound (P t) _ _ e f

/-- Joint measurability includes the exceptional spatial origin of the projector. -/
theorem ordered_sewn_return_measurable {n₁ n₂ : ℕ} (kind : OrderedPhotonKind) (a : ℝ) :
    Measurable (fun z : ((Fin n₁ → OrderedHopStep) × (Fin n₂ → OrderedHopStep)) × (ℝ × Spatial) =>
      kind.sewn a (OrderedTwoBandPath.returnPath z.1.1) (OrderedTwoBandPath.returnPath z.1.2) z.2) := by
  let X := ((Fin n₁ → OrderedHopStep) × (Fin n₂ → OrderedHopStep)) × (ℝ × Spatial)
  let f := fun z : X => (z.1.1,z.2)
  let g := fun z : X => (z.1.2,(-z.2.1,-z.2.2))
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  cases kind with
  | coulomb =>
    apply (Complex.continuous_ofReal.measurable.comp (show Measurable
      (fun z : X => Real.exp (-(2*a*‖z.2.2‖))/‖z.2.2‖^2) by fun_prop)).mul
    exact ((OrderedTwoBandPath.continuous_return_density.comp hf).mul
      (OrderedTwoBandPath.continuous_return_density.comp hg)).measurable
  | transverse =>
    apply (Complex.continuous_ofReal.measurable.comp (show Measurable
      (fun z : X => Real.exp (-(2*a*‖z.2.2‖))/(z.2.1^2+‖z.2.2‖^2)) by fun_prop)).mul
    apply Finset.measurable_sum
    intro ij _
    apply (Complex.continuous_ofReal.measurable.comp ((measurable_orderedSpatialProjector _ _).comp
      (measurable_snd.comp measurable_snd))).mul
    exact (((OrderedTwoBandPath.continuous_return_spatialCurrent _).comp hf).mul
      ((OrderedTwoBandPath.continuous_return_spatialCurrent _).comp hg)).measurable

theorem OrderedGraphProbe.measurable_return_factor {n : ℕ} (probe : OrderedGraphProbe n) (a : ℝ) (k : OSFourSpace)
    {N : OrderedGraphVertices n → ℕ} :
    Measurable (fun d : OrderedGraphHops N => probe.factor (fun v => OrderedTwoBandPath.returnPath (d v)) a k) := by
  cases probe with
  | vacuum => exact measurable_const
  | pair s t e f =>
    let z := orderedPhotonChart k
    let pos := fun d : OrderedGraphHops N => (d s,z)
    let neg := fun d : OrderedGraphHops N => (d t,(-z.1,-z.2))
    have hp : Measurable pos := (measurable_pi_apply s).prodMk measurable_const
    have hn : Measurable neg := (measurable_pi_apply t).prodMk measurable_const
    have hpos := (OrderedTwoBandPath.continuous_return_spatialCurrent (n := N s) e.val).measurable.comp hp
    have hneg := (OrderedTwoBandPath.continuous_return_spatialCurrent (n := N t) f.val).measurable.comp hn
    have hab := hpos.mul hneg
    have hfac := hab.const_mul (Real.exp (-(2*a*‖z.2‖)) : ℂ)
    exact hfac

variable {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}
variable (src dst : E → OrderedGraphVertices n) (B : WilsonIncidenceBasis (groundedNetworkIncidence src dst).row)
    (kind : E → OrderedPhotonKind) (probe : OrderedGraphProbe n)

def orderedJointGraph {N : OrderedGraphVertices n → ℕ}
    (φ : (v : OrderedGraphVertices n) → OrderedHopPhases (N v)) (m σ g a : ℝ) (k : OSFourSpace)
    (z : OrderedGraphHops N × (B.Chord → OSFourSpace)) : ℂ :=
  let P := fun v => OrderedTwoBandPath.returnPath (z.1 v)
  (∏ v, orderedHopLogWord m σ g (φ v) (z.1 v)) *
    (probe.factor P a k * orderedGraphSewing src dst B kind P a (probe.injection k) z.2)

theorem measurable_orderedJointGraph {N : OrderedGraphVertices n → ℕ}
    (φ : (v : OrderedGraphVertices n) → OrderedHopPhases (N v)) (hφ : ∀ v j s, Measurable (φ v j s))
    (m σ g a : ℝ) (k : OSFourSpace) :
    Measurable (orderedJointGraph src dst B kind probe φ m σ g a k) := by
  let X := OrderedGraphHops N × (B.Chord → OSFourSpace)
  let D := fun (v : OrderedGraphVertices n) (z : X) => z.1 v
  have hd (v : OrderedGraphVertices n) : Measurable (D v) := (measurable_pi_apply v).comp measurable_fst
  have he (e : E) : Measurable (fun z : X => orderedPhotonChart (B.flow (probe.injection k) z.2 e)) :=
    orderedPhotonChart.measurable.comp ((B.measurable_flow _ _).comp measurable_snd)
  apply (Finset.measurable_prod _ (fun v _ => (orderedHop_log_word_measurable m σ g (hφ v)).comp (hd v))).mul
  apply Measurable.mul
  · exact (probe.measurable_return_factor a k (N := N)).comp measurable_fst
  · apply Finset.measurable_prod
    intro e _
    have hdPair := (hd (src e)).prodMk (hd (dst e))
    have hinput := hdPair.prodMk (he e)
    have hm := (ordered_sewn_return_measurable (n₁ := N (src e)) (n₂ := N (dst e)) (kind e) a).comp hinput
    exact hm

end UV
