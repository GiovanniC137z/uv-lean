import UV.ExtendOpeningSelfAdjoint

/-! A self-adjoint realization of the number-state Jacobi rule must be
the closure of the finite-number operator. -/

noncomputable section
namespace UV

theorem opening_position_core_number_expansion (ω : ℝ) (v : (openingPositionOnCore ω).domain) :
    ∃ c : ℕ, v = ∑ n ∈ Finset.range (c+1), ((v:OpeningFock) n) • openingPositionNumberState ω n := by
  obtain ⟨c,hc⟩ := v.property
  refine ⟨c,?_⟩
  apply Subtype.ext
  ext k
  simp only [Submodule.coe_sum,Submodule.coe_smul_of_tower,openingPositionNumberState]
  by_cases h : k ≤ c
  · simp [mul_ite,Finset.mem_range,Nat.lt_succ_iff,h]
  · simp [mul_ite,Finset.mem_range,Nat.lt_succ_iff,h,hc k (by omega)]

theorem opening_position_core_graph_le (ω : ℝ) (R : OpeningFock →ₗ.[ℂ] OpeningFock)
    (hn : ∀ n, (openingNumberState n,openingPositionOnCore ω (openingPositionNumberState ω n)) ∈ R.graph) :
    (openingPositionOnCore ω).graph ≤ R.graph := by
  intro p hp
  obtain ⟨v,rfl⟩ := ((openingPositionOnCore ω).mem_graph_iff').mp hp
  obtain ⟨c,hv⟩ := opening_position_core_number_expansion ω v
  have hsum := R.graph.sum_mem (t:=Finset.range (c+1)) (fun n _ => R.graph.smul_mem ((v:OpeningFock) n) (hn n))
  convert hsum using 1
  apply Prod.ext
  · simpa [Prod.fst_sum] using congrArg (fun w : (openingPositionOnCore ω).domain => (w:OpeningFock)) hv
  · simpa [Prod.snd_sum] using congrArg (openingPositionOnCore ω).toFun hv

/-- Equality of the unbounded operators, including their domains. -/
theorem opening_position_eq_closure_of_number_graph (ω : ℝ) (R : OpeningFock →ₗ.[ℂ] OpeningFock)
    (hR : IsSelfAdjoint R)
    (hn : ∀ n, (openingNumberState n,openingPositionOnCore ω (openingPositionNumberState ω n)) ∈ R.graph) :
    R = (openingPositionOnCore ω).closure := by
  have hc := opening_position_core_graph_le ω R hn
  apply LinearPMap.eq_of_eq_graph
  apply le_antisymm
  · rw [openingPositionClosure_eq_adjoint,LinearPMap.adjoint_graph_eq_graph_adjoint (openingPositionOnCore_dense ω)]
    intro p hp
    have he : R.adjoint = R := LinearPMap.isSelfAdjoint_def.mp hR
    have hgra : R.graph.adjoint = R.graph :=
      (LinearPMap.adjoint_graph_eq_graph_adjoint hR.dense_domain).symm.trans (congrArg LinearPMap.graph he)
    have h := (R.graph.mem_adjoint_iff p).mp (hgra.symm ▸ hp)
    exact ((openingPositionOnCore ω).graph.mem_adjoint_iff p).mpr fun x y hxy => h x y (hc hxy)
  · rw [←(openingPositionOnCore_closable ω).graph_closure_eq_closure_graph]
    exact (Submodule.topologicalClosure_mono hc).trans_eq hR.isClosed.submodule_topologicalClosure_eq

end UV
