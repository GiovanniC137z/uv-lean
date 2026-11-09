import UV.UnboundedSourceCore
import UV.UnboundedSourceProjection

/-! The union of bounded joint spectral cuts is an actual operator core.
Both the vectors and their maximal-multiplier images converge in L2, so
the graph of the restricted operator is dense in the full closed graph. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace UV

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- The genuine graph-core statement for every real measurable spectral
symbol bounded on each compact joint cut. The core property is proved from
the cut approximation and self-adjoint closedness of maximal multiplication. -/
theorem sourceJointCore_hasCore {F K w : X → ℝ}
    (hF : Measurable F) (hK : Measurable K)
    (hposF : ∀ᵐ x ∂μ, 0 < F x) (hposK : ∀ᵐ x ∂μ, 0 < K x)
    (hw : Measurable w) (hAdm : sourceCoreAdmissible F K (fun x => (w x : ℂ))) :
    LinearPMap.HasCore (sourceL2Multiplier μ (fun x => (w x : ℂ)))
      (sourceJointCore μ F K) := by
  let T := sourceL2Multiplier μ (fun x => (w x : ℂ))
  let C := sourceJointCore μ F K
  let R := T.domRestrict C
  have hle : R ≤ T := LinearPMap.domRestrict_le
  have hclosed : T.IsClosed := (sourceL2Multiplier_real_selfAdjoint μ w hw).isClosed
  have hclosable : R.IsClosable := hclosed.isClosable.leIsClosable hle
  have hcover : ∀ᵐ x ∂μ, ∃ N : ℕ, ∀ n ≥ N, x ∈ sourceJointSpectralCut F K n := by
    filter_upwards [hposF, hposK] with x hxF hxK
    exact sourceJointSpectralCut_eventually_mem hxF hxK
  let s := sourceJointSpectralCut F K
  have hs : ∀ n, MeasurableSet (s n) := sourceJointSpectralCut_measurable hF hK
  have hgraph : R.graph.topologicalClosure = T.graph := by
    apply le_antisymm
    · exact Submodule.topologicalClosure_minimal R.graph
        (LinearPMap.le_graph_of_le hle) hclosed
    · intro p hp
      obtain ⟨f, rfl⟩ := (T.mem_graph_iff').mp hp
      let fn : ℕ → Lp ℂ 2 μ := fun n => sourceL2Cut μ (s n) (hs n) f.val
      have hcore (n : ℕ) : fn n ∈ C := sourceJointCore_cut_mem μ hF hK n f.val
      have hdom (n : ℕ) : fn n ∈ T.domain := sourceJointCore_mem_multiplier μ hAdm (hcore n)
      let fnR : ℕ → R.domain := fun n => ⟨fn n, ⟨hcore n, hdom n⟩⟩
      have hout (n : ℕ) : R (fnR n) = sourceL2Cut μ (s n) (hs n) (T f) := by
        calc
          _ = T ⟨fn n, hdom n⟩ := LinearPMap.domRestrict_apply rfl
          _ = _ := sourceL2Projection_reduce μ (s n) (hs n)
            (fun x => (w x : ℂ)) f.val f.property
      have hvec : Tendsto fn atTop (𝓝 f.val) := sourceL2Cut_tendsto μ s hs hcover f.val
      have himage : Tendsto (fun n => R (fnR n)) atTop (𝓝 (T f)) := by
        simpa only [hout] using sourceL2Cut_tendsto μ s hs hcover (T f)
      have hpair : Tendsto (fun n => (fn n, R (fnR n))) atTop (𝓝 (f.val, T f)) :=
        hvec.prodMk_nhds himage
      change (f.val, T f) ∈ closure (R.graph : Set (Lp ℂ 2 μ × Lp ℂ 2 μ))
      exact mem_closure_of_tendsto hpair (Eventually.of_forall fun n => R.mem_graph (fnR n))
  refine ⟨fun _ hf => sourceJointCore_mem_multiplier μ hAdm hf, ?_⟩
  apply LinearPMap.eq_of_eq_graph
  exact hclosable.graph_closure_eq_closure_graph.symm.trans hgraph

end UV
