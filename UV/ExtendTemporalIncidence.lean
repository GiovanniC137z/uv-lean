import UV.ExtendTemporalFrequencyBound
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

/-! Reduced incidence on a connected finite oriented multigraph.
The edge labels are independent of the endpoints, so loops and parallel
edges remain distinct. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace UV.SectorPlane

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

abbrev FrequencyVertex (root : V) := {v : V // v ≠ root}

def frequencyVertexVector (root : V) (v : V) : FrequencyVertex root → ℝ :=
  fun i => if i.val = v then 1 else 0

def frequencyIncidence (root : V) (src dst : E → V) (e : E) : FrequencyVertex root → ℝ :=
  frequencyVertexVector root (dst e) - frequencyVertexVector root (src e)

/-- Adjacent vertices can be joined along either orientation of one
labelled edge. -/
def frequencyAdjacent (src dst : E → V) (v w : V) : Prop :=
  ∃ e, (src e = v ∧ dst e = w) ∨ (src e = w ∧ dst e = v)

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem frequencyIncidence_eq_zero_iff (root : V) (src dst : E → V) (e : E) :
    frequencyIncidence root src dst e = 0 ↔ src e = dst e := by
  constructor
  · intro h
    by_contra hne
    by_cases hroot : dst e = root
    · have hs : src e ≠ root := fun h' => hne (h'.trans hroot.symm)
      have hi := congrFun h ⟨src e, hs⟩
      simp [frequencyIncidence, frequencyVertexVector, hne] at hi
    · have hi := congrFun h ⟨dst e, hroot⟩
      simp [frequencyIncidence, frequencyVertexVector, Ne.symm hne] at hi
  · intro h
    simp [frequencyIncidence, h]

omit [Fintype E] [DecidableEq E] in
/-- Connectedness makes the columns span the complete reduced vertex
space, including the one-vertex zero-dimensional case. -/
theorem frequencyIncidence_span (root : V) (src dst : E → V)
    (hconn : ∀ v, Relation.ReflTransGen (frequencyAdjacent src dst) root v) :
    Submodule.span ℝ (Set.range (frequencyIncidence root src dst)) = ⊤ := by
  let S := Submodule.span ℝ (Set.range (frequencyIncidence root src dst))
  have hg (v w : V) (ha : frequencyAdjacent src dst v w) :
      frequencyVertexVector root w - frequencyVertexVector root v ∈ S := by
    obtain ⟨e, (⟨h₁,h₂⟩ | ⟨h₁,h₂⟩)⟩ := ha
    · simpa only [← h₁, ← h₂] using
        (Submodule.subset_span (Set.mem_range_self e) : frequencyIncidence root src dst e ∈ S)
    · have hh : frequencyIncidence root src dst e ∈ S := Submodule.subset_span (Set.mem_range_self e)
      simpa only [frequencyIncidence, h₁, h₂, neg_sub] using S.neg_mem hh
  have hroot : frequencyVertexVector root root = 0 := by
    ext i
    simp [frequencyVertexVector, i.property]
  have hv (v : V) : frequencyVertexVector root v ∈ S := by
    induction hconn v with
    | refl => simpa only [hroot] using S.zero_mem
    | @tail w z _ hw hwmem =>
        have hs := S.add_mem (hg w z hw) hwmem
        simpa only [sub_add_cancel] using hs
  apply top_unique
  intro q _
  have hdecomp : q = ∑ i : FrequencyVertex root, q i • frequencyVertexVector root i.val := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, frequencyVertexVector]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      have hji : j.val ≠ i.val := fun h => hij (Subtype.ext h.symm)
      simp [hji]
    · simp
  rw [hdecomp]
  exact S.sum_mem fun i _ => S.smul_mem _ (hv i.val)

/-- All bases selected from the labelled reduced incidence columns. The
complements supply chord coordinates. A bridge occurs in every basis. -/
def FrequencyIncidenceBasis (root : V) (src dst : E → V) :=
  {s : Set E // LinearIndepOn ℝ (frequencyIncidence root src dst) s ∧
    Submodule.span ℝ (frequencyIncidence root src dst '' s) = ⊤}

instance (root : V) (src dst : E → V) : Finite (FrequencyIncidenceBasis root src dst) := by
  unfold FrequencyIncidenceBasis
  infer_instance

omit [Fintype E] [DecidableEq E] in
theorem frequency_incidence_nonloop_in_basis (root : V) (src dst : E → V)
    (hconn : ∀ v, Relation.ReflTransGen (frequencyAdjacent src dst) root v)
    (e : E) (hne : src e ≠ dst e) :
    ∃ t : FrequencyIncidenceBasis root src dst, e ∈ t.val := by
  let cols := frequencyIncidence root src dst
  have hn : cols e ≠ 0 := fun h => hne ((frequencyIncidence_eq_zero_iff root src dst e).mp h)
  have hli : LinearIndepOn ℝ cols {e} := LinearIndepOn.singleton ℝ hn
  let t := hli.extend (subset_univ {e})
  have ht := hli.linearIndepOn_extend (subset_univ {e})
  have hs : Submodule.span ℝ (cols '' t) = ⊤ := by
    rw [hli.span_image_extend_eq_span_image (subset_univ {e}), Set.image_univ]
    exact frequencyIncidence_span root src dst hconn
  exact ⟨⟨t, ht, hs⟩, hli.subset_extend (subset_univ {e}) (mem_singleton e)⟩

omit [Fintype E] [DecidableEq E] in
theorem frequency_incidence_basis_nonempty (root : V) (src dst : E → V)
    (hconn : ∀ v, Relation.ReflTransGen (frequencyAdjacent src dst) root v) :
    Nonempty (FrequencyIncidenceBasis root src dst) := by
  let cols := frequencyIncidence root src dst
  have hli : LinearIndepOn ℝ cols ∅ := linearIndepOn_empty _ _
  let t := hli.extend (subset_univ ∅)
  have ht := hli.linearIndepOn_extend (subset_univ ∅)
  have hs : Submodule.span ℝ (cols '' t) = ⊤ := by
    rw [hli.span_image_extend_eq_span_image (subset_univ ∅), Set.image_univ]
    exact frequencyIncidence_span root src dst hconn
  exact ⟨⟨t, ht, hs⟩⟩

end UV.SectorPlane
