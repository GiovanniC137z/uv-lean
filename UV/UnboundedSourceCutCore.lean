import UV.UnboundedSourceCommute

/-! A closed operator has the prescribed common core whenever actual
graph-commuting cuts land in that core and converge strongly to the identity.
The graph closure and the HasCore conclusion are derived. -/

noncomputable section
open Set Filter
open scoped Topology

namespace UV

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Graph-commuting strong cut approximations prove the genuine closed
operator core property on an arbitrary Hilbert realization. -/
theorem sourceGraphCore_of_cut_approximation (K : H →ₗ.[ℂ] H) (S : Submodule ℂ H)
    (hClosed : K.IsClosed) (hDom : S ≤ K.domain) (J : ℕ → H →L[ℂ] H)
    (hRange : ∀ n x, J n x ∈ S)
    (hComm : ∀ n, sourceGraphCommutes K (J n))
    (hApprox : ∀ x : H, Tendsto (fun n => J n x) atTop (𝓝 x)) :
    K.HasCore S := by
  let R := K.domRestrict S
  have hle : R ≤ K := LinearPMap.domRestrict_le
  have hClosable : R.IsClosable := hClosed.isClosable.leIsClosable hle
  have hGraph : R.graph.topologicalClosure = K.graph := by
    apply le_antisymm
    · exact Submodule.topologicalClosure_minimal R.graph
        (LinearPMap.le_graph_of_le hle) hClosed
    · intro p hp
      obtain ⟨f, rfl⟩ := (K.mem_graph_iff').mp hp
      have hMem (n : ℕ) : (J n f.val, J n (K f)) ∈ R.graph := by
        obtain ⟨g, hg, hKg⟩ := (K.mem_graph_iff).mp (hComm n f)
        have hgS : g.val ∈ S := by rw [hg]; exact hRange n f.val
        let gR : R.domain := ⟨g.val, ⟨hgS, g.property⟩⟩
        apply (R.mem_graph_iff).mpr
        refine ⟨gR, hg, ?_⟩
        calc
          R gR = K g := LinearPMap.domRestrict_apply rfl
          _ = _ := hKg
      have hPair : Tendsto (fun n => (J n f.val, J n (K f))) atTop (𝓝 (f.val, K f)) :=
        (hApprox f.val).prodMk_nhds (hApprox (K f))
      change (f.val, K f) ∈ closure (R.graph : Set (H × H))
      exact mem_closure_of_tendsto hPair (Eventually.of_forall hMem)
  refine ⟨hDom, ?_⟩
  apply LinearPMap.eq_of_eq_graph
  exact hClosable.graph_closure_eq_closure_graph.symm.trans hGraph

end UV
