import UV.UnboundedSource
import UV.UnboundedSourceGraphCore

/-! Unitary transport of actual maximal spectral operators to arbitrary
complex Hilbert spaces. The domain is pulled back by the unitary map, and
the action, symmetry and imaginary resolvents are constructed explicitly. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace UV

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def sourceUnitaryDomainMap (U : H ≃ₗᵢ[ℂ] E) (T : E →ₗ.[ℂ] E) :
    (T.domain.comap U.toLinearEquiv.toLinearMap) →ₗ[ℂ] T.domain where
  toFun f := ⟨U f.val, f.property⟩
  map_add' f g := Subtype.ext (U.map_add f.val g.val)
  map_smul' c f := Subtype.ext (U.map_smul c f.val)

def sourceUnitaryConjugate (U : H ≃ₗᵢ[ℂ] E) (T : E →ₗ.[ℂ] E) : H →ₗ.[ℂ] H where
  domain := T.domain.comap U.toLinearEquiv.toLinearMap
  toFun := U.symm.toLinearEquiv.toLinearMap.comp (T.toFun.comp (sourceUnitaryDomainMap U T))

theorem sourceUnitaryConjugate_mem_domain (U : H ≃ₗᵢ[ℂ] E) (T : E →ₗ.[ℂ] E) (f : H) :
    f ∈ (sourceUnitaryConjugate U T).domain ↔ U f ∈ T.domain := Iff.rfl

theorem sourceUnitaryConjugate_apply (U : H ≃ₗᵢ[ℂ] E) (T : E →ₗ.[ℂ] E)
    (f : (sourceUnitaryConjugate U T).domain) :
    sourceUnitaryConjugate U T f = U.symm (T (sourceUnitaryDomainMap U T f)) := rfl

theorem sourceUnitaryConjugate_symmetric (U : H ≃ₗᵢ[ℂ] E) (T : E →ₗ.[ℂ] E)
    (hT : T.IsFormalAdjoint T) :
    (sourceUnitaryConjugate U T).IsFormalAdjoint (sourceUnitaryConjugate U T) := by
  intro f g
  rw [← U.inner_map_map, ← U.inner_map_map]
  simp only [sourceUnitaryConjugate_apply, U.apply_symm_apply]
  exact hT (sourceUnitaryDomainMap U T f) (sourceUnitaryDomainMap U T g)

/-- A unitary change of Hilbert realization preserves genuine resolvent
surjectivity, including the concrete preimage for each target vector. -/
theorem sourceUnitaryConjugate_shift_surjective (U : H ≃ₗᵢ[ℂ] E)
    (T : E →ₗ.[ℂ] E) (c : ℂ)
    (hT : Function.Surjective (fun f : T.domain => T f+c • (f : E))) :
    Function.Surjective (fun f : (sourceUnitaryConjugate U T).domain =>
      sourceUnitaryConjugate U T f+c • (f : H)) := by
  intro g
  obtain ⟨f, hf⟩ := hT (U g)
  have hdom : U.symm (f : E) ∈ (sourceUnitaryConjugate U T).domain := by
    change U (U.symm (f : E)) ∈ T.domain
    simpa only [U.apply_symm_apply] using f.property
  refine ⟨⟨U.symm f, hdom⟩, ?_⟩
  apply U.injective
  change U (U.symm (T ⟨U (U.symm (f : E)), hdom⟩)+c • U.symm (f : E)) = U g
  simpa only [map_add, map_smul, U.apply_symm_apply] using hf

theorem sourceUnitaryConjugate_graph_mem_iff (U : H ≃ₗᵢ[ℂ] E) (T : E →ₗ.[ℂ] E)
    (p : H × H) :
    p ∈ (sourceUnitaryConjugate U T).graph ↔ (U p.1, U p.2) ∈ T.graph := by
  constructor
  · intro hp
    obtain ⟨f, hf, ht⟩ := (LinearPMap.mem_graph_iff _).mp hp
    apply (T.mem_graph_iff).mpr
    refine ⟨sourceUnitaryDomainMap U T f, congrArg U hf, ?_⟩
    calc
      _ = U (sourceUnitaryConjugate U T f) := by
        rw [sourceUnitaryConjugate_apply, U.apply_symm_apply]
      _ = _ := congrArg U ht
  · intro hp
    obtain ⟨f, hf, ht⟩ := (T.mem_graph_iff).mp hp
    change (f : E) = U p.1 at hf
    have hdom : U p.1 ∈ T.domain := hf ▸ f.property
    apply (LinearPMap.mem_graph_iff _).mpr
    refine ⟨⟨p.1, hdom⟩, rfl, ?_⟩
    apply U.injective
    rw [sourceUnitaryConjugate_apply, U.apply_symm_apply]
    have he : sourceUnitaryDomainMap U T ⟨p.1, hdom⟩ = f := Subtype.ext hf.symm
    rw [he, ht]

theorem sourceUnitaryConjugate_graph_preimage (U : H ≃ₗᵢ[ℂ] E) (T : E →ₗ.[ℂ] E) :
    ((sourceUnitaryConjugate U T).graph : Set (H × H)) =
      (fun p : H × H => (U p.1, U p.2)) ⁻¹' (T.graph : Set (E × E)) := by
  ext p
  exact sourceUnitaryConjugate_graph_mem_iff U T p

theorem sourceUnitaryConjugate_domRestrict (U : H ≃ₗᵢ[ℂ] E) (T : E →ₗ.[ℂ] E)
    (S : Submodule ℂ E) :
    sourceUnitaryConjugate U (T.domRestrict S) =
      (sourceUnitaryConjugate U T).domRestrict (S.comap U.toLinearEquiv.toLinearMap) := by
  apply LinearPMap.ext
  · ext f
    rfl
  · intro f hf hg
    rfl

theorem sourceUnitaryConjugate_isClosed (U : H ≃ₗᵢ[ℂ] E) (T : E →ₗ.[ℂ] E)
    (hT : T.IsClosed) : (sourceUnitaryConjugate U T).IsClosed := by
  change IsClosed ((sourceUnitaryConjugate U T).graph : Set (H × H))
  rw [sourceUnitaryConjugate_graph_preimage]
  exact hT.preimage ((U.continuous.comp continuous_fst).prodMk (U.continuous.comp continuous_snd))

/-- A genuine closed-operator core transports through an arbitrary unitary
realization. The graph closure is pulled back by the product homeomorphism. -/
theorem sourceUnitaryConjugate_hasCore (U : H ≃ₗᵢ[ℂ] E) (T : E →ₗ.[ℂ] E)
    (S : Submodule ℂ E) (hT : T.IsClosed) (hCore : T.HasCore S) :
    (sourceUnitaryConjugate U T).HasCore (S.comap U.toLinearEquiv.toLinearMap) := by
  let e : (H × H) ≃L[ℂ] (E × E) :=
    U.toContinuousLinearEquiv.prodCongr U.toContinuousLinearEquiv
  let Q := sourceUnitaryConjugate U T
  let C := S.comap U.toLinearEquiv.toLinearMap
  let R := Q.domRestrict C
  have hB : (T.domRestrict S).IsClosable :=
    hT.isClosable.leIsClosable LinearPMap.domRestrict_le
  have hBase : closure ((T.domRestrict S).graph : Set (E × E)) = (T.graph : Set (E × E)) := by
    change ((T.domRestrict S).graph.topologicalClosure : Set (E × E)) = _
    rw [hB.graph_closure_eq_closure_graph, hCore.closure_eq]
  have hQgraph : (Q.graph : Set (H × H)) = e ⁻¹' (T.graph : Set (E × E)) :=
    sourceUnitaryConjugate_graph_preimage U T
  have hRgraph : (R.graph : Set (H × H)) = e ⁻¹' ((T.domRestrict S).graph : Set (E × E)) := by
    change (((sourceUnitaryConjugate U T).domRestrict
      (S.comap U.toLinearEquiv.toLinearMap)).graph : Set (H × H)) = _
    rw [← sourceUnitaryConjugate_domRestrict U T S]
    exact sourceUnitaryConjugate_graph_preimage U (T.domRestrict S)
  have hRclose : closure (R.graph : Set (H × H)) = (Q.graph : Set (H × H)) := by
    have hecl : e ⁻¹' closure ((T.domRestrict S).graph : Set (E × E)) =
        closure (e ⁻¹' ((T.domRestrict S).graph : Set (E × E))) := by
      simpa only [ContinuousLinearEquiv.coe_toHomeomorph] using
        e.toHomeomorph.preimage_closure ((T.domRestrict S).graph : Set (E × E))
    rw [hRgraph, ← hecl, hBase, ← hQgraph]
  have hQclosed : Q.IsClosed := sourceUnitaryConjugate_isClosed U T hT
  have hRclosable : R.IsClosable := hQclosed.isClosable.leIsClosable LinearPMap.domRestrict_le
  refine ⟨fun _ hf => hCore.le_domain hf, ?_⟩
  apply LinearPMap.eq_of_eq_graph
  have hgraph : R.graph.topologicalClosure = Q.graph := SetLike.coe_injective hRclose
  exact hRclosable.graph_closure_eq_closure_graph.symm.trans hgraph

variable [CompleteSpace H]

/-- The unitary-conjugated partial operator is actually self-adjoint. Its
adjoint-domain identity follows from the transported imaginary resolvents. -/
theorem sourceUnitaryConjugate_selfAdjoint_of_resolvents (U : H ≃ₗᵢ[ℂ] E)
    (T : E →ₗ.[ℂ] E) (hT : T.IsFormalAdjoint T)
    (hPlus : Function.Surjective (fun f : T.domain => T f+Complex.I • (f : E)))
    (hMinus : Function.Surjective (fun f : T.domain => T f-Complex.I • (f : E))) :
    IsSelfAdjoint (sourceUnitaryConjugate U T) := by
  apply unbounded_selfAdjoint_of_imaginary_resolvents'
    (sourceUnitaryConjugate U T) (sourceUnitaryConjugate_symmetric U T hT)
  · exact sourceUnitaryConjugate_shift_surjective U T Complex.I hPlus
  · have hm : Function.Surjective (fun f : T.domain => T f+(-Complex.I) • (f : E)) := by
      simpa only [neg_smul, sub_eq_add_neg] using hMinus
    simpa only [neg_smul, sub_eq_add_neg] using
      sourceUnitaryConjugate_shift_surjective U T (-Complex.I) hm

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def sourceUnitaryRealMultiplier (U : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (w : X → ℝ) : H →ₗ.[ℂ] H :=
  sourceUnitaryConjugate U (sourceL2Multiplier μ (fun x => (w x : ℂ)))

/-- Every specified unitary joint spectral realization gives the actual
unbounded self-adjoint multiplier on the original arbitrary Hilbert space.
This does not assume that an unspecified commuting pair admits such a U. -/
theorem sourceUnitaryRealMultiplier_selfAdjoint (U : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (w : X → ℝ) (hw : Measurable w) : IsSelfAdjoint (sourceUnitaryRealMultiplier μ U w) := by
  apply sourceUnitaryConjugate_selfAdjoint_of_resolvents U
    (sourceL2Multiplier μ (fun x => (w x : ℂ))) (sourceL2Multiplier_real_symmetric μ w)
  · exact sourceL2Multiplier_shift_surjective μ w hw Complex.I (by simp) (by simp)
  · simpa only [neg_smul, sub_eq_add_neg] using
      sourceL2Multiplier_shift_surjective μ w hw (-Complex.I) (by simp) (by simp)

omit [CompleteSpace H] in
/-- The actual dense joint graph core survives unitary transport to the
original Hilbert realization, with all inverse/root domain obligations. -/
theorem sourceUnitaryRealMultiplier_hasCore (U : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    {F K w : X → ℝ} (hF : Measurable F) (hK : Measurable K)
    (hposF : ∀ᵐ x ∂μ, 0 < F x) (hposK : ∀ᵐ x ∂μ, 0 < K x)
    (hw : Measurable w) (hAdm : sourceCoreAdmissible F K (fun x => (w x : ℂ))) :
    (sourceUnitaryRealMultiplier μ U w).HasCore
      ((sourceJointCore μ F K).comap U.toLinearEquiv.toLinearMap) :=
  sourceUnitaryConjugate_hasCore U (sourceL2Multiplier μ (fun x => (w x : ℂ)))
    (sourceJointCore μ F K) (sourceL2Multiplier_real_selfAdjoint μ w hw).isClosed
    (sourceJointCore_hasCore μ hF hK hposF hposK hw hAdm)

end UV
