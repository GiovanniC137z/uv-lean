import UV.SourceOperators
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Algebra.Module.Submodule.Equiv

/-! Inverse operators on the actual range of a bounded injective operator.
The inverse is generally unbounded. Self-adjointness of a bounded inverse
is proved with full adjoint-domain equality, without a spectral model. -/

noncomputable section
open scoped InnerProductSpace

namespace UV

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def sourceRangeInverse (S : H →L[ℂ] H) (hS : Function.Injective S) : H →ₗ.[ℂ] H where
  domain := LinearMap.range S.toLinearMap
  toFun := (LinearEquiv.ofInjective S.toLinearMap hS).symm.toLinearMap

omit [CompleteSpace H] in
theorem sourceRangeInverse_left (S : H →L[ℂ] H) (hS : Function.Injective S)
    (y : (sourceRangeInverse S hS).domain) : S (sourceRangeInverse S hS y) = y := by
  exact congrArg Subtype.val ((LinearEquiv.ofInjective S.toLinearMap hS).apply_symm_apply y)

omit [CompleteSpace H] in
theorem sourceRangeInverse_right (S : H →L[ℂ] H) (hS : Function.Injective S) (x : H) :
    sourceRangeInverse S hS ⟨S x, ⟨x,rfl⟩⟩ = x :=
  hS (sourceRangeInverse_left S hS ⟨S x, ⟨x,rfl⟩⟩)

/-- An injective bounded self-adjoint operator has dense range. -/
theorem source_selfAdjoint_injective_dense_range {S : H →L[ℂ] H}
    (hSelf : IsSelfAdjoint S) (hInj : Function.Injective S) :
    Dense (LinearMap.range S.toLinearMap : Set H) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  have hAdj : S.adjoint = S := hSelf
  have hker : LinearMap.ker S.adjoint.toLinearMap = ⊥ := by
    rw [hAdj]
    exact LinearMap.ker_eq_bot.mpr hInj
  exact S.orthogonal_range.trans hker

/-- The generally unbounded inverse of an injective bounded self-adjoint
operator is self-adjoint on its precise range domain. -/
theorem sourceRangeInverse_selfAdjoint {S : H →L[ℂ] H}
    (hSelf : IsSelfAdjoint S) (hInj : Function.Injective S) :
    IsSelfAdjoint (sourceRangeInverse S hInj) := by
  let T := sourceRangeInverse S hInj
  have hAdj : S.adjoint = S := hSelf
  have hDense : Dense (T.domain : Set H) := source_selfAdjoint_injective_dense_range hSelf hInj
  have hSym : T.IsFormalAdjoint T := by
    intro x y
    calc
      inner ℂ (T x) (y : H) = inner ℂ (T x) (S (T y)) := by rw [sourceRangeInverse_left]
      _ = inner ℂ (S (T x)) (T y) := by simpa only [hAdj] using S.adjoint_inner_right (T x) (T y)
      _ = inner ℂ (x : H) (T y) := by rw [sourceRangeInverse_left]
  have hle : T ≤ T.adjoint := hSym.le_adjoint hDense
  have hrev : T.adjoint ≤ T := by
    refine ⟨?_, fun _ _ he => (hle.2 he.symm).symm⟩
    intro y hy
    let y' : T.adjoint.domain := ⟨y,hy⟩
    have hSy : S (T.adjoint y') = y := by
      apply ext_inner_right ℂ
      intro x
      let v : T.domain := ⟨S x, ⟨x,rfl⟩⟩
      have he := LinearPMap.adjoint_isFormalAdjoint hDense y' v
      rw [sourceRangeInverse_right S hInj x] at he
      calc
        inner ℂ (S (T.adjoint y')) x = inner ℂ (T.adjoint y') (S x) := by
          simpa only [hAdj] using S.adjoint_inner_left x (T.adjoint y')
        _ = inner ℂ y x := he
    exact ⟨T.adjoint y',hSy⟩
  exact LinearPMap.isSelfAdjoint_def.mpr (le_antisymm hrev hle)

theorem source_sqrt_injective {F : H →L[ℂ] H} (hF : 0 ≤ F)
    (hInj : Function.Injective F) : Function.Injective (CFC.sqrt F : H →L[ℂ] H) := by
  intro x y hxy
  apply hInj
  rw [← CFC.sqrt_mul_sqrt_self F hF]
  change (CFC.sqrt F : H →L[ℂ] H) ((CFC.sqrt F : H →L[ℂ] H) x) =
    (CFC.sqrt F : H →L[ℂ] H) ((CFC.sqrt F : H →L[ℂ] H) y)
  rw [hxy]

/-- The actual inverse square-root endpoint for a bounded positive injective
multiplier, on an arbitrary Hilbert space and without a spectral theorem. -/
def sourceHilbertNormalizer (F : H →L[ℂ] H) (hF : 0 ≤ F) (hInj : Function.Injective F) :
    H →ₗ.[ℂ] H := sourceRangeInverse (CFC.sqrt F) (source_sqrt_injective hF hInj)

theorem sourceHilbertNormalizer_selfAdjoint (F : H →L[ℂ] H) (hF : 0 ≤ F)
    (hInj : Function.Injective F) : IsSelfAdjoint (sourceHilbertNormalizer F hF hInj) :=
  sourceRangeInverse_selfAdjoint (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg F))
    (source_sqrt_injective hF hInj)

/-- F times any bounded covariance has range inside the generally unbounded
normalizer's domain; this domain obligation is derived from F=(sqrt F)^2. -/
theorem sourceHilbertNormalizer_mixed_domain (F D : H →L[ℂ] H) (hF : 0 ≤ F)
    (hInj : Function.Injective F) (x : H) :
    F (D x) ∈ (sourceHilbertNormalizer F hF hInj).domain := by
  refine ⟨(CFC.sqrt F : H →L[ℂ] H) (D x), ?_⟩
  change ((CFC.sqrt F : H →L[ℂ] H)*(CFC.sqrt F : H →L[ℂ] H)) (D x) = F (D x)
  rw [CFC.sqrt_mul_sqrt_self F hF]

/-- The mixed half-factor for the actual unbounded inverse square root on
an arbitrary Hilbert space, without any lower spectral gap for F. -/
theorem sourceHilbertNormalizer_mixed (F D : H →L[ℂ] H) (hF : 0 ≤ F)
    (hInj : Function.Injective F) (x : H) :
    sourceHilbertNormalizer F hF hInj
      ⟨F (D x),sourceHilbertNormalizer_mixed_domain F D hF hInj x⟩ =
        (CFC.sqrt F : H →L[ℂ] H) (D x) := by
  apply source_sqrt_injective hF hInj
  change (CFC.sqrt F : H →L[ℂ] H)
      (sourceRangeInverse (CFC.sqrt F) (source_sqrt_injective hF hInj)
        ⟨F (D x),sourceHilbertNormalizer_mixed_domain F D hF hInj x⟩) = _
  rw [sourceRangeInverse_left]
  change F (D x) = ((CFC.sqrt F : H →L[ℂ] H)*(CFC.sqrt F : H →L[ℂ] H)) (D x)
  rw [CFC.sqrt_mul_sqrt_self F hF]

/-- Exact covariance cancellation for a bounded commuting covariance and a
genuinely unbounded endpoint. Only the input belongs to ran(sqrt F); the
outer endpoint's domain membership is proved, rather than postulated. -/
theorem sourceHilbertNormalizer_covariance (F D : H →L[ℂ] H) (hF : 0 ≤ F)
    (hInj : Function.Injective F) (hcomm : Commute F D)
    (y : (sourceHilbertNormalizer F hF hInj).domain) :
    sourceHilbertNormalizer F hF hInj
      ⟨F (D (sourceHilbertNormalizer F hF hInj y)),
        sourceHilbertNormalizer_mixed_domain F D hF hInj (sourceHilbertNormalizer F hF hInj y)⟩ =
      D (y : H) := by
  rw [sourceHilbertNormalizer_mixed]
  have he := congrArg (fun A : H →L[ℂ] H => A (sourceHilbertNormalizer F hF hInj y))
    (sourceOperator_sqrt_commute hcomm).eq
  change (CFC.sqrt F : H →L[ℂ] H) (D (sourceHilbertNormalizer F hF hInj y)) =
    D ((CFC.sqrt F : H →L[ℂ] H) (sourceHilbertNormalizer F hF hInj y)) at he
  rw [he]
  exact congrArg D (sourceRangeInverse_left (CFC.sqrt F) (source_sqrt_injective hF hInj) y)

end UV
