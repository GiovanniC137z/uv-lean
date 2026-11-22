import UV.ExtendTemporalIncidence
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Solving vertex conservation in each incidence-basis chart. -/

noncomputable section
open MeasureTheory Set Module
open scoped BigOperators ENNReal Topology

namespace UV.SectorPlane
variable {V E : Type*} [Fintype E] [DecidableEq V]
variable {root : V} {src dst : E → V}

noncomputable instance : Fintype (FrequencyIncidenceBasis root src dst) := Fintype.ofFinite _

abbrev FrequencyChord (t : FrequencyIncidenceBasis root src dst) := {e : E // e ∉ t.val}
abbrev FrequencyTreeEdge (t : FrequencyIncidenceBasis root src dst) := {e : E // e ∈ t.val}

noncomputable instance (t : FrequencyIncidenceBasis root src dst) : Fintype (FrequencyChord t) := by
  classical
  exact Subtype.fintype (fun e => e ∉ t.val)

noncomputable instance (t : FrequencyIncidenceBasis root src dst) : Fintype (FrequencyTreeEdge t) := by
  classical
  exact Subtype.fintype (fun e => e ∈ t.val)

def frequencyIncidenceColumnBasis (t : FrequencyIncidenceBasis root src dst) :
    Basis (FrequencyTreeEdge t) ℝ (FrequencyVertex root → ℝ) :=
  Basis.mk t.property.1 (by
    rw [show (Set.range fun x : FrequencyTreeEdge t => frequencyIncidence root src dst x.val) =
        frequencyIncidence root src dst '' t.val from (Set.image_eq_range _ _).symm]
    exact t.property.2.ge)

omit [Fintype E] in
@[simp] theorem frequencyIncidenceColumnBasis_apply (t : FrequencyIncidenceBasis root src dst)
    (e : FrequencyTreeEdge t) :
    frequencyIncidenceColumnBasis t e = frequencyIncidence root src dst e.val := by
  unfold frequencyIncidenceColumnBasis
  exact Basis.mk_apply _ _ _

/-- The actual reduced vertex conservation map on the complete edge frequencies. -/
def frequencyVertexSum (root : V) (src dst : E → V) :
    (E → ℝ) →ₗ[ℝ] (FrequencyVertex root → ℝ) where
  toFun := fun x => ∑ e, x e • frequencyIncidence root src dst e
  map_add' := by
    intro x y
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro k x
    simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, smul_eq_mul, RingHom.id_apply]

/-- Extract the reduced vertex constraints and the chords of a chosen
incidence basis, in one linear map. -/
def frequencyIncidenceChartMap (t : FrequencyIncidenceBasis root src dst) :
    (E → ℝ) →ₗ[ℝ] (FrequencyVertex root → ℝ) × (FrequencyChord t → ℝ) where
  toFun := fun x => (frequencyVertexSum root src dst x, fun e => x e.val)
  map_add' := by
    intro x y
    exact Prod.ext ((frequencyVertexSum root src dst).map_add x y) rfl
  map_smul' := by
    intro k x
    exact Prod.ext ((frequencyVertexSum root src dst).map_smul k x) rfl

private theorem frequencyVertexSum_split (t : FrequencyIncidenceBasis root src dst) (x : E → ℝ) :
    frequencyVertexSum root src dst x =
      (∑ e : FrequencyTreeEdge t, x e.val • frequencyIncidenceColumnBasis t e) +
      ∑ e : FrequencyChord t, x e.val • frequencyIncidence root src dst e.val := by
  classical
  unfold frequencyVertexSum
  simp only [LinearMap.coe_mk, AddHom.coe_mk, frequencyIncidenceColumnBasis_apply]
  exact (Fintype.sum_subtype_add_sum_subtype (fun e => e ∈ t.val)
    (fun e => x e • frequencyIncidence root src dst e)).symm

/-- Every independent chord tuple and reduced external frequency vector
extends to a unique solution of the actual conservation equations. -/
theorem frequencyIncidenceChartMap_bijective (t : FrequencyIncidenceBasis root src dst) :
    Function.Bijective (frequencyIncidenceChartMap t) := by
  classical
  constructor
  · intro x y hxy
    have hV := congrArg Prod.fst hxy
    have hC := congrArg Prod.snd hxy
    change frequencyVertexSum root src dst x = frequencyVertexSum root src dst y at hV
    change (fun e : FrequencyChord t => x e.val) = fun e => y e.val at hC
    rw [frequencyVertexSum_split t, frequencyVertexSum_split t] at hV
    have hc : (∑ e : FrequencyChord t, x e.val • frequencyIncidence root src dst e.val) =
        ∑ e : FrequencyChord t, y e.val • frequencyIncidence root src dst e.val := by
      apply Finset.sum_congr rfl
      intro e _
      rw [congrFun hC e]
    rw [hc] at hV
    have hv := (frequencyIncidenceColumnBasis t).equivFun.symm.injective (by
      simpa only [Basis.equivFun_symm_apply] using add_right_cancel hV)
    funext e
    by_cases he : e ∈ t.val
    · exact congrFun hv ⟨e, he⟩
    · exact congrFun hC ⟨e, he⟩
  · rintro ⟨v, q⟩
    let b := frequencyIncidenceColumnBasis t
    let residual := v - ∑ e : FrequencyChord t, q e • frequencyIncidence root src dst e.val
    let x (e : E) : ℝ := if he : e ∈ t.val then b.equivFun residual ⟨e, he⟩ else q ⟨e, he⟩
    have hC (e : FrequencyChord t) : x e.val = q e := by
      unfold x
      simp only [dif_neg e.property]
    have hB (e : FrequencyTreeEdge t) : x e.val = b.equivFun residual e := by
      unfold x
      simp only [dif_pos e.property]
    refine ⟨x, Prod.ext ?_ (funext hC)⟩
    change frequencyVertexSum root src dst x = v
    rw [frequencyVertexSum_split t]
    simp_rw [hB, hC]
    change (∑ e, b.equivFun residual e • b e) + _ = v
    rw [b.sum_equivFun]
    exact sub_add_cancel _ _

/-- The exact frequency chart given by the independent chord slots. -/
def frequencyIncidenceChart (t : FrequencyIncidenceBasis root src dst) :
    (E → ℝ) ≃ₗ[ℝ] (FrequencyVertex root → ℝ) × (FrequencyChord t → ℝ) :=
  LinearEquiv.ofBijective (frequencyIncidenceChartMap t) (frequencyIncidenceChartMap_bijective t)

theorem frequencyIncidenceChart_apply (t : FrequencyIncidenceBasis root src dst) (x : E → ℝ) :
    frequencyIncidenceChart t x = (frequencyVertexSum root src dst x, fun e => x e.val) := rfl

theorem frequencyIncidenceChart_symm_conservation (t : FrequencyIncidenceBasis root src dst)
    (v : FrequencyVertex root → ℝ) (q : FrequencyChord t → ℝ) :
    frequencyVertexSum root src dst ((frequencyIncidenceChart t).symm (v, q)) = v :=
  congrArg Prod.fst ((frequencyIncidenceChart t).apply_symm_apply (v, q))

theorem frequencyIncidenceChart_symm_chords (t : FrequencyIncidenceBasis root src dst)
    (v : FrequencyVertex root → ℝ) (q : FrequencyChord t → ℝ) :
    (fun e : FrequencyChord t => (frequencyIncidenceChart t).symm (v, q) e.val) = q :=
  congrArg Prod.snd ((frequencyIncidenceChart t).apply_symm_apply (v, q))

variable [Fintype V]

/-- The number of independent frequencies is the number of internal
edges less the number of independent vertex constraints. -/
abbrev incidenceFrequencyDimension (root : V) (E : Type*) [Fintype E] [DecidableEq V] : ℕ :=
  Fintype.card E - Fintype.card (FrequencyVertex root)

theorem frequencyChord_card (t : FrequencyIncidenceBasis root src dst) :
    Fintype.card (FrequencyChord t) = incidenceFrequencyDimension root E := by
  classical
  have hcard := (Module.finrank_eq_card_basis (frequencyIncidenceColumnBasis t)).symm
  rw [Module.finrank_fintype_fun_eq_card] at hcard
  change Fintype.card {e : E // e ∉ t.val} = _
  rw [Fintype.card_subtype_compl (fun e => e ∈ t.val)]
  exact congrArg (Fintype.card E - ·) hcard

def frequencyChordIndex (t : FrequencyIncidenceBasis root src dst) :
    Fin (incidenceFrequencyDimension root E) ≃ FrequencyChord t :=
  ((Fintype.equivFin (FrequencyChord t)).trans (finCongr (frequencyChord_card t))).symm

end UV.SectorPlane
