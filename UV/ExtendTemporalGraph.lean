import UV.ExtendTemporalRouting
import Mathlib.LinearAlgebra.Determinant

/-! The frequency bound on the actual conservation chart of a connected
finite time-local graph on a single fixed sector plane. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace UV.SectorPlane
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
variable {root : V} {src dst : E → V}

abbrev GraphFrequency (root : V) (E : Type*) [Fintype E] [DecidableEq V] :=
  FrequencyCoordinates (incidenceFrequencyDimension root E)

private def frequencyChordRelabel (t : FrequencyIncidenceBasis root src dst) :
    (FrequencyChord t → ℝ) ≃ₗ[ℝ] GraphFrequency root E where
  toFun := fun q j => q (frequencyChordIndex t j)
  invFun := fun q e => q ((frequencyChordIndex t).symm e)
  left_inv := by
    intro q
    funext e
    simp only [Equiv.apply_symm_apply]
  right_inv := by
    intro q
    funext j
    simp only [Equiv.symm_apply_apply]
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

def frequencyIncidenceChartFin (t : FrequencyIncidenceBasis root src dst) :
    (E → ℝ) ≃ₗ[ℝ] (FrequencyVertex root → ℝ) × GraphFrequency root E :=
  (frequencyIncidenceChart t).trans
    (LinearEquiv.prodCongr (LinearEquiv.refl ℝ _) (frequencyChordRelabel t))

theorem frequencyIncidenceChartFin_apply (t : FrequencyIncidenceBasis root src dst) (w : E → ℝ) :
    frequencyIncidenceChartFin t w =
      (frequencyVertexSum root src dst w, fun j => w (frequencyChordIndex t j).val) := rfl

theorem frequencyIncidenceChartFin_change (s t : FrequencyIncidenceBasis root src dst)
    (v : FrequencyVertex root → ℝ) (q : GraphFrequency root E) :
    (frequencyIncidenceChartFin t ((frequencyIncidenceChartFin s).symm (v, q))).1 = v := by
  rw [frequencyIncidenceChartFin_apply, ← show
      (frequencyIncidenceChartFin s ((frequencyIncidenceChartFin s).symm (v, q))).1 =
        frequencyVertexSum root src dst ((frequencyIncidenceChartFin s).symm (v, q)) from rfl,
    (frequencyIncidenceChartFin s).apply_symm_apply]

/-- The entire nonconstant part of an affine change of chord coordinates. -/
def frequencyIncidenceChange (s t : FrequencyIncidenceBasis root src dst) :
    GraphFrequency root E ≃ₗ[ℝ] GraphFrequency root E where
  toFun := fun q => (frequencyIncidenceChartFin t ((frequencyIncidenceChartFin s).symm (0, q))).2
  invFun := fun q => (frequencyIncidenceChartFin s ((frequencyIncidenceChartFin t).symm (0, q))).2
  left_inv := by
    intro q
    let w := (frequencyIncidenceChartFin s).symm (0, q)
    have he : (0, (frequencyIncidenceChartFin t w).2) = frequencyIncidenceChartFin t w :=
      Prod.ext (frequencyIncidenceChartFin_change s t 0 q).symm rfl
    change (frequencyIncidenceChartFin s ((frequencyIncidenceChartFin t).symm
      (0, (frequencyIncidenceChartFin t w).2))).2 = q
    rw [he, LinearEquiv.symm_apply_apply]
    exact congrArg Prod.snd ((frequencyIncidenceChartFin s).apply_symm_apply (0, q))
  right_inv := by
    intro q
    let w := (frequencyIncidenceChartFin t).symm (0, q)
    have he : (0, (frequencyIncidenceChartFin s w).2) = frequencyIncidenceChartFin s w :=
      Prod.ext (frequencyIncidenceChartFin_change t s 0 q).symm rfl
    change (frequencyIncidenceChartFin t ((frequencyIncidenceChartFin s).symm
      (0, (frequencyIncidenceChartFin s w).2))).2 = q
    rw [he, LinearEquiv.symm_apply_apply]
    exact congrArg Prod.snd ((frequencyIncidenceChartFin t).apply_symm_apply (0, q))
  map_add' := by
    intro q₁ q₂
    change _ = (frequencyIncidenceChartFin t _).2 + (frequencyIncidenceChartFin t _).2
    rw [show ((0 : FrequencyVertex root → ℝ), q₁ + q₂) = (0, q₁) + (0, q₂) by simp, map_add, map_add, Prod.snd_add]
  map_smul' := by
    intro c q
    change _ = c • (frequencyIncidenceChartFin t _).2
    rw [show ((0 : FrequencyVertex root → ℝ), c • q) = c • (0, q) by simp, map_smul, map_smul]
    rfl

/-- The edge frequencies in the chart chosen for the independent
integration variables. -/
def frequencyGraphRouting (s : FrequencyIncidenceBasis root src dst)
    (v : FrequencyVertex root → ℝ) (q : GraphFrequency root E) : E → ℝ :=
  (frequencyIncidenceChartFin s).symm (v, q)

theorem frequencyGraphRouting_conservation (s : FrequencyIncidenceBasis root src dst)
    (v : FrequencyVertex root → ℝ) (q : GraphFrequency root E) :
    frequencyVertexSum root src dst (frequencyGraphRouting s v q) = v :=
  congrArg Prod.fst ((frequencyIncidenceChartFin s).apply_symm_apply (v, q))

/-- The exact real affine transition between any two chord charts. -/
theorem frequencyGraphRouting_affine (s t : FrequencyIncidenceBasis root src dst)
    (v : FrequencyVertex root → ℝ) (q : GraphFrequency root E) :
    (fun j => frequencyGraphRouting s v q (frequencyChordIndex t j).val) =
      (LinearMap.toMatrix' (frequencyIncidenceChange s t).toLinearMap).mulVec q +
        (fun j => frequencyGraphRouting s v 0 (frequencyChordIndex t j).val) := by
  rw [LinearMap.toMatrix'_mulVec]
  change (frequencyIncidenceChartFin t ((frequencyIncidenceChartFin s).symm (v, q))).2 =
    (frequencyIncidenceChartFin t ((frequencyIncidenceChartFin s).symm (0, q))).2 +
    (frequencyIncidenceChartFin t ((frequencyIncidenceChartFin s).symm (v, 0))).2
  rw [show (v, q) = (0, q) + (v, 0) by simp, map_add, map_add, Prod.snd_add]

theorem frequencyIncidenceChange_det_ne_zero (s t : FrequencyIncidenceBasis root src dst) :
    (LinearMap.toMatrix' (frequencyIncidenceChange s t).toLinearMap).det ≠ 0 := by
  rw [LinearMap.det_toMatrix', ← LinearEquiv.coe_det]
  exact Units.ne_zero _

variable [DecidableEq E]

/-- The manuscript's absolute carrier-frequency bound for time-local graphs.
The statement uses the independent chord coordinates of an arbitrary
reference incidence basis and all the edges of the actual graph. Only
self-loops require a strictly higher exponent. -/
theorem time_local_graph_absolute_carrier_frequency {G X : Type*} [Norm G]
    (diamond : Plane G) (root : V) (src dst : E → V)
    (hconn : ∀ v, Relation.ReflTransGen (frequencyAdjacent src dst) root v)
    (s : FrequencyIncidenceBasis root src dst)
    (external : X → (FrequencyVertex root → ℝ))
    (a D : E → ℝ) (ha : ∀ e, 1 ≤ a e) (hD : ∀ e, 0 ≤ D e)
    (hself : ∀ e, src e = dst e → 1 < a e)
    (W : ℝ) (hW : 0 ≤ W)
    (K : Plane G → X → GraphFrequency root E → ℂ)
    (hK : ∀ x, AEStronglyMeasurable (K diamond x) volume)
    (hbound : ∀ x q, ‖K diamond x q‖ ≤ W * ∏ e,
      D e * frequencyEnvelope (a e) (frequencyGraphRouting s (external x) q e)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, Integrable (K diamond x) volume ∧
      (∫ q, ‖K diamond x q‖) ≤ C * (∏ e, D e) * W := by
  let T := FrequencyIncidenceBasis root src dst
  letI : Nonempty T := ⟨s⟩
  let L := incidenceFrequencyDimension root E
  let r (t : T) (j : Fin L) : E := (frequencyChordIndex t j).val
  let M (t : T) := LinearMap.toMatrix' (frequencyIncidenceChange s t).toLinearMap
  let shift (t : T) (x : X) (j : Fin L) := frequencyGraphRouting s (external x) 0 (r t j)
  let u (_ : Plane G) (x : X) (q : GraphFrequency root E) := frequencyGraphRouting s (external x) q
  have hU (x : X) (e : E) : Measurable (fun q => u diamond x q e) := by
    apply Continuous.measurable
    change Continuous (fun q => (frequencyIncidenceChartFin s).symm (external x, q) e)
    have hc := (frequencyIncidenceChartFin s).symm.toLinearMap.continuous_of_finiteDimensional
    exact (continuous_apply e).comp (hc.comp (continuous_const.prodMk continuous_id))
  have hAlways (e : E) (h : ∀ t, e ∈ frequencyChords r t) : 1 < a e := by
    apply hself
    by_contra hn
    obtain ⟨t, ht⟩ := frequency_incidence_nonloop_in_basis root src dst hconn e hn
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (h t)
    have hj' : (frequencyChordIndex t j).val = e := hj
    rw [← hj'] at ht
    exact (frequencyChordIndex t j).property ht
  have h := frequency_tree_graph_integrable diamond u hU r
    (fun t => Subtype.val_injective.comp (frequencyChordIndex t).injective)
    M (frequencyIncidenceChange_det_ne_zero s) shift
    (fun t x q => frequencyGraphRouting_affine s t (external x) q)
    a D ha hD hAlways W hW K hK hbound
  refine ⟨(frequency_tree_budget r M a).toReal, ENNReal.toReal_nonneg, fun x => ⟨(h x).1, ?_⟩⟩
  exact (h x).2.trans_eq (by ring)

end UV.SectorPlane
