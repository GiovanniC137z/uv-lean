import UV.UnboundedSourceAbstract

/-! Domain-preserving commutants of actual inverse operators. The inverse
range obligations and the inverse graph identities are consequences of
injectivity and the original graph commutation, not input data. -/

noncomputable section

namespace UV

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem sourceRangeInverse_graphCommutes (S : H →L[ℂ] H)
    (hS : Function.Injective S) (A : H →L[ℂ] H) (hComm : Commute S A) :
    sourceGraphCommutes (sourceRangeInverse S hS) A := by
  intro f
  have hSA : S (A (sourceRangeInverse S hS f)) = A (f : H) := by
    calc
      _ = A (S (sourceRangeInverse S hS f)) :=
        congrArg (fun B : H →L[ℂ] H => B (sourceRangeInverse S hS f)) hComm.eq
      _ = _ := by rw [sourceRangeInverse_left]
  have hDom : A (f : H) ∈ (sourceRangeInverse S hS).domain :=
    ⟨A (sourceRangeInverse S hS f), hSA⟩
  apply (LinearPMap.mem_graph_iff _).mpr
  refine ⟨⟨A (f : H), hDom⟩, rfl, ?_⟩
  apply hS
  rw [sourceRangeInverse_left]
  exact hSA.symm

theorem sourcePartialInverse_graphCommutes (K : H →ₗ.[ℂ] H)
    (hK : Function.Injective K) (A : H →L[ℂ] H)
    (hComm : sourceGraphCommutes K A) : sourceGraphCommutes K.inverse A := by
  intro f
  obtain ⟨x, hx, hInv⟩ := source_partial_inverse_spec K hK f
  obtain ⟨y, hy, hKy⟩ := K.mem_graph_iff.mp (hComm x)
  have hKya : K y = A (f : H) := hKy.trans (congrArg A hx)
  have hDom : A (f : H) ∈ K.inverse.domain := by
    exact (le_of_eq (LinearPMap.inverse_domain (f := K)).symm) ⟨y, hKya⟩
  apply K.inverse.mem_graph_iff.mpr
  refine ⟨⟨A (f : H), hDom⟩, rfl, ?_⟩
  rw [LinearPMap.inverse_apply_eq (LinearMap.ker_eq_bot.mpr hK) hKya, hInv]
  exact hy

theorem sourcePartialInverse_isClosed (K : H →ₗ.[ℂ] H) (hClosed : K.IsClosed)
    (hK : Function.Injective K) : K.inverse.IsClosed :=
  (LinearPMap.inverse_closed_iff (LinearMap.ker_eq_bot.mpr hK)).mpr hClosed

end UV
