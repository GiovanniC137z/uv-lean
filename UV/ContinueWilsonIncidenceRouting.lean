import UV.ContinueWilsonAffineRoute
import UV.ContinueNetworkGaussian
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Independent edge coordinates for the conservation equations of a finite
connected contracted photon multigraph. The grounded incidence is computed
from the actual oriented endpoints, allowing parallel edges and self-loops. -/

noncomputable section

open Set Submodule MeasureTheory
open scoped BigOperators Matrix

namespace UV

variable {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}

/-- The tree rows are a basis of the grounded vertex space. The other
edges are genuine free momenta in this coordinate system. -/
structure WilsonIncidenceBasis (A : E → Fin n → ℝ) where
  tree : Finset E
  basis : Module.Basis tree ℝ (Fin n → ℝ)
  edge_eq : ∀ j : tree, basis j = A j

omit [DecidableEq E] in
theorem wilson_incidence_spans (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n))
    (hc : G.Connected) (hcover : NetworkOrientationCovers G src dst) :
    span ℝ (range (groundedNetworkIncidence src dst).row) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [←Matrix.rank_eq_finrank_span_row]
  exact LinearMap.finrank_range_of_inj (groundedNetworkIncidence_injective G src dst hc hcover)

omit [DecidableEq E] in
theorem wilson_incidence_basis_exists (A : E → Fin n → ℝ) (hA : span ℝ (range A) = ⊤) :
    Nonempty (WilsonIncidenceBasis A) := by
  classical
  obtain ⟨S,_,_,hspan,hli⟩ := exists_linearIndepOn_extension (linearIndepOn_empty ℝ A) (Set.empty_subset (univ : Set E))
  let s := S.toFinset
  have hs : (s : Set E) = S := Set.coe_toFinset _
  have hr : range (fun j : s => A j) = A '' S := by rw [←hs,Set.image_eq_range]; rfl
  have hh : ⊤ ≤ span ℝ (range (fun j : s => A j)) := by
    rw [hr,←hA]
    apply Submodule.span_le.mpr
    simpa only [image_univ] using hspan
  have hli' : LinearIndependent ℝ (fun j : s => A j) := by
    change LinearIndepOn ℝ A (s : Set E)
    rwa [hs]
  exact ⟨⟨s,Module.Basis.mk hli' hh,Module.Basis.mk_apply _ _⟩⟩

omit [DecidableEq E] in
theorem wilson_connected_routing_exists (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n))
    (hc : G.Connected) (hcover : NetworkOrientationCovers G src dst) :
    Nonempty (WilsonIncidenceBasis (groundedNetworkIncidence src dst).row) :=
  wilson_incidence_basis_exists _ (wilson_incidence_spans G src dst hc hcover)

variable {A : E → Fin n → ℝ} (B : WilsonIncidenceBasis A)

abbrev WilsonIncidenceBasis.Chord := {e : E // e ∉ B.tree}

def WilsonIncidenceBasis.coefficient (j : B.tree) (c : B.Chord) : ℝ := - B.basis.repr (A c) j

def WilsonIncidenceBasis.offset (b : Fin n → OSFourSpace) (j : B.tree) : OSFourSpace :=
  WithLp.toLp 2 (fun k => B.basis.repr (fun v => b v k) j)

def WilsonIncidenceBasis.onTree (b : Fin n → OSFourSpace) (q : B.Chord → OSFourSpace) (j : B.tree) : OSFourSpace :=
  wilsonAffineTransfer (B.offset b j) (B.coefficient j) q

def WilsonIncidenceBasis.flow (b : Fin n → OSFourSpace) (q : B.Chord → OSFourSpace) (e : E) : OSFourSpace :=
  if h : e ∈ B.tree then B.onTree b q ⟨e,h⟩ else q ⟨e,h⟩

@[simp] theorem WilsonIncidenceBasis.chord_flow (b : Fin n → OSFourSpace) (q : B.Chord → OSFourSpace) (c : B.Chord) :
    B.flow b q c = q c := by simp [flow,c.property]

@[simp] theorem WilsonIncidenceBasis.tree_flow (b : Fin n → OSFourSpace) (q : B.Chord → OSFourSpace) (j : B.tree) :
    B.flow b q j = B.onTree b q j := by simp [flow,j.property]

theorem WilsonIncidenceBasis.onTree_component (b : Fin n → OSFourSpace) (q : B.Chord → OSFourSpace)
    (j : B.tree) (k : Fin 4) :
    B.onTree b q j k = B.basis.repr ((fun v => b v k) - ∑ c : B.Chord, (q c k) • A c) j := by
  have hcoord (f : B.Chord → OSFourSpace) : (∑ c, f c) k = ∑ c, (f c) k :=
    map_sum (EuclideanSpace.proj k : OSFourSpace →L[ℝ] ℝ) f _
  change _ = B.basis.coord j ((fun v => b v k) - ∑ c : B.Chord, (q c k) • A c)
  rw [map_sub,map_sum]
  simp only [onTree,wilsonAffineTransfer,wilson_route_linear_apply,offset,coefficient,
    PiLp.add_apply,PiLp.toLp_apply,hcoord,PiLp.smul_apply,map_smul,Module.Basis.coord_apply,
    smul_eq_mul,neg_mul,Finset.sum_neg_distrib,sub_eq_add_neg]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Momentum balance in every carrier coordinate at every ungrounded
vertex. The omitted equation is the global external conservation law. -/
theorem WilsonIncidenceBasis.balance (b : Fin n → OSFourSpace) (q : B.Chord → OSFourSpace) (k : Fin 4) :
    (∑ e, (B.flow b q e k) • A e) = fun v => b v k := by
  rw [←Fintype.sum_subtype_add_sum_subtype (fun e => e ∈ B.tree)]
  rw [show Subtype.fintype (fun e => e ∈ B.tree) = Finset.Subtype.fintype B.tree from Subsingleton.elim _ _]
  simp only [B.tree_flow,B.chord_flow,B.onTree_component,←B.edge_eq]
  let g := ∑ c : B.Chord, (q c k) • A c
  exact (congrArg (· + g) (B.basis.sum_repr ((fun v => b v k)-g))).trans (sub_add_cancel _ _)

theorem WilsonIncidenceBasis.unique_flow (b : Fin n → OSFourSpace) (q : B.Chord → OSFourSpace)
    (f : E → OSFourSpace) (hchord : ∀ c : B.Chord, f c = q c)
    (hconserve : ∀ k : Fin 4, (∑ e, (f e k) • A e) = fun v => b v k) : f = B.flow b q := by
  funext e
  by_cases hj : e ∈ B.tree
  · let j : B.tree := ⟨e,hj⟩
    ext k
    have h := hconserve k
    rw [←Fintype.sum_subtype_add_sum_subtype (fun e => e ∈ B.tree)] at h
    rw [show Subtype.fintype (fun e => e ∈ B.tree) = Finset.Subtype.fintype B.tree from Subsingleton.elim _ _] at h
    simp only [hchord,←B.edge_eq] at h
    have he := congrArg (fun x => B.basis.repr x j) (eq_sub_of_add_eq h)
    change f j k = B.flow b q j k
    rw [B.tree_flow,B.onTree_component]
    exact (congrFun (B.basis.repr_sum_self (fun i : B.tree => f i k)) j).symm.trans he
  · exact (hchord ⟨e,hj⟩).trans (B.chord_flow b q ⟨e,hj⟩).symm

/-- If deletion of the tree edge preserves the incidence span, that
edge carries a nonzero free-chord coefficient. -/
theorem WilsonIncidenceBasis.active_of_deletion (j : B.tree)
    (hdel : A j ∈ span ℝ (A '' {e | e ≠ j.val})) : ∃ c : B.Chord, B.coefficient j c ≠ 0 := by
  classical
  by_contra! hn
  have hker : span ℝ (A '' {e | e ≠ j.val}) ≤ LinearMap.ker (B.basis.coord j) := by
    apply Submodule.span_le.mpr
    rintro x ⟨e,he,rfl⟩
    change B.basis.repr (A e) j = 0
    by_cases h : e ∈ B.tree
    · let i : B.tree := ⟨e,h⟩
      have hij : i ≠ j := fun hi => he (congrArg Subtype.val hi)
      change B.basis.repr (A i) j = 0
      rw [←B.edge_eq i,B.basis.repr_self_apply,if_neg hij]
    · simpa only [coefficient,neg_eq_zero] using hn (⟨e,h⟩ : B.Chord)
  have hx := hker hdel
  change B.basis.repr (A j) j = 0 at hx
  simp [←B.edge_eq] at hx

/-- Graph-theoretic deletion test, allowing other parallel edges to
continue connecting the same pair of vertices. -/
theorem wilson_incidence_nonbridge (src dst : E → Option (Fin n)) (e : E)
    (G' : SimpleGraph (Option (Fin n))) (hc : G'.Connected)
    (hcover : NetworkOrientationCovers G' (fun j : {j : E // j ≠ e} => src j) (fun j => dst j)) :
    (groundedNetworkIncidence src dst).row e ∈ span ℝ ((groundedNetworkIncidence src dst).row '' {j | j ≠ e}) := by
  have h := wilson_incidence_spans G' _ _ hc hcover
  change span ℝ (range (fun j : {j : E // j ≠ e} => (groundedNetworkIncidence src dst).row j)) = ⊤ at h
  rw [Set.image_eq_range]
  apply (eq_top_iff.mp h)
  exact Submodule.mem_top

end UV
