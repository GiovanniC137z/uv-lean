import UV.UnboundedSourceCommute

/-! Free-source identities with an arbitrary closed injective unbounded
kinetic operator. Its covariance is the actual LinearPMap inverse. The
normalizer's domain and every covariance-domain inclusion are derived. -/

noncomputable section
open scoped InnerProductSpace

namespace UV

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Specification of the actual inverse of an injective partial operator. -/
theorem source_partial_inverse_spec (K : H →ₗ.[ℂ] H) (hInj : Function.Injective K)
    (f : K.inverse.domain) :
    ∃ x : K.domain, K x = (f : H) ∧ K.inverse f = (x : H) := by
  have hf := (le_of_eq (LinearPMap.inverse_domain (f := K))) f.property
  obtain ⟨x,hx⟩ := hf
  exact ⟨x,hx,LinearPMap.inverse_apply_eq (LinearMap.ker_eq_bot.mpr hInj) hx⟩

/-- sqrt(F) intertwines the actual unbounded K domain, so the covariance
domain of T f implies and constructs the covariance domain of f itself. -/
theorem source_abstract_inverse_domain (K : H →ₗ.[ℂ] H) (hClosed : K.IsClosed)
    (hKInj : Function.Injective K) (F : H →L[ℂ] H) (hF : 0 ≤ F)
    (hFInj : Function.Injective F) (hcomm : sourceGraphCommutes K F)
    (f : (sourceHilbertNormalizer F hF hFInj).domain)
    (hDf : sourceHilbertNormalizer F hF hFInj f ∈ K.inverse.domain) :
    ∃ hf : (f : H) ∈ K.inverse.domain,
      K.inverse ⟨(f : H),hf⟩ =
        (CFC.sqrt F : H →L[ℂ] H)
          (K.inverse ⟨sourceHilbertNormalizer F hF hFInj f,hDf⟩) := by
  obtain ⟨x,hx,hDx⟩ := source_partial_inverse_spec K hKInj
    ⟨sourceHilbertNormalizer F hF hFInj f,hDf⟩
  obtain ⟨y,hy,hKy⟩ := K.mem_graph_iff.mp (source_sqrt_graph_commutes hClosed hF hcomm x)
  have hKyf : K y = (f : H) := by
    rw [hKy,hx]
    exact sourceRangeInverse_left (CFC.sqrt F) (source_sqrt_injective hF hFInj) f
  have hf : (f : H) ∈ K.inverse.domain := by
    rw [LinearPMap.inverse_domain]
    exact ⟨y,hKyf⟩
  refine ⟨hf,?_⟩
  rw [LinearPMap.inverse_apply_eq (LinearMap.ker_eq_bot.mpr hKInj) hKyf, hDx]
  exact hy

/-- Exact normalization with a genuinely unbounded covariance. No bound on
K inverse and no joint spectral realization is an input to this identity. -/
theorem source_abstract_unbounded_covariance (K : H →ₗ.[ℂ] H) (hClosed : K.IsClosed)
    (hKInj : Function.Injective K) (F : H →L[ℂ] H) (hF : 0 ≤ F)
    (hFInj : Function.Injective F) (hcomm : sourceGraphCommutes K F)
    (f : (sourceHilbertNormalizer F hF hFInj).domain)
    (hDf : sourceHilbertNormalizer F hF hFInj f ∈ K.inverse.domain) :
    ∃ hf : (f : H) ∈ K.inverse.domain,
      sourceHilbertNormalizer F hF hFInj
        ⟨F (K.inverse ⟨sourceHilbertNormalizer F hF hFInj f,hDf⟩),
          sourceHilbertNormalizer_mixed_domain F 1 hF hFInj
            (K.inverse ⟨sourceHilbertNormalizer F hF hFInj f,hDf⟩)⟩ = K.inverse ⟨(f : H),hf⟩ := by
  obtain ⟨hf,he⟩ := source_abstract_inverse_domain K hClosed hKInj F hF hFInj hcomm f hDf
  refine ⟨hf,?_⟩
  simpa only [ContinuousLinearMap.one_apply] using
    (sourceHilbertNormalizer_mixed F 1 hF hFInj
      (K.inverse ⟨sourceHilbertNormalizer F hF hFInj f,hDf⟩)).trans he.symm

/-- The mixed half-factor needs only the actual covariance domain. -/
theorem source_abstract_unbounded_mixed (K : H →ₗ.[ℂ] H)
    (F : H →L[ℂ] H) (hF : 0 ≤ F) (hFInj : Function.Injective F)
    (f : K.inverse.domain) :
    sourceHilbertNormalizer F hF hFInj
      ⟨F (K.inverse f),sourceHilbertNormalizer_mixed_domain F 1 hF hFInj (K.inverse f)⟩ =
      (CFC.sqrt F : H →L[ℂ] H) (K.inverse f) := by
  exact sourceHilbertNormalizer_mixed F 1 hF hFInj (K.inverse f)

omit [CompleteSpace H] in
theorem source_partial_inverse_domain (K : H →ₗ.[ℂ] H) (x : K.domain) :
    K x ∈ K.inverse.domain := by
  rw [LinearPMap.inverse_domain]
  exact LinearMap.mem_range_self K.toFun x

/-- Ordinary kinetic amputation of the actual mixed unbounded contraction
leaves sqrt(F), with inverse domains proved from injectivity of K. -/
theorem source_abstract_unbounded_amputation (K : H →ₗ.[ℂ] H) (hKInj : Function.Injective K)
    (F : H →L[ℂ] H) (hF : 0 ≤ F) (hFInj : Function.Injective F) (x : K.domain) :
    sourceHilbertNormalizer F hF hFInj
      ⟨F (K.inverse ⟨K x,source_partial_inverse_domain K x⟩),
        sourceHilbertNormalizer_mixed_domain F 1 hF hFInj
          (K.inverse ⟨K x,source_partial_inverse_domain K x⟩)⟩ =
      (CFC.sqrt F : H →L[ℂ] H) (x : H) := by
  rw [source_abstract_unbounded_mixed,
    LinearPMap.inverse_apply_eq (LinearMap.ker_eq_bot.mpr hKInj) (rfl : K x = K x)]

/-- The Hermitian smeared source covariance follows from the actual
self-adjoint normalizer and the proved unbounded covariance identity. -/
theorem source_abstract_unbounded_smeared (K : H →ₗ.[ℂ] H) (hClosed : K.IsClosed)
    (hKInj : Function.Injective K) (F : H →L[ℂ] H) (hF : 0 ≤ F)
    (hFInj : Function.Injective F) (hcomm : sourceGraphCommutes K F)
    (f g : (sourceHilbertNormalizer F hF hFInj).domain)
    (hDg : sourceHilbertNormalizer F hF hFInj g ∈ K.inverse.domain) :
    ∃ hg : (g : H) ∈ K.inverse.domain,
      inner ℂ (sourceHilbertNormalizer F hF hFInj f)
        (F (K.inverse ⟨sourceHilbertNormalizer F hF hFInj g,hDg⟩)) =
        inner ℂ (f : H) (K.inverse ⟨(g : H),hg⟩) := by
  let T := sourceHilbertNormalizer F hF hFInj
  have hSelf := sourceHilbertNormalizer_selfAdjoint F hF hFInj
  have hAdj : (sourceHilbertNormalizer F hF hFInj).adjoint =
      sourceHilbertNormalizer F hF hFInj := hSelf
  have hSym : T.IsFormalAdjoint T := by
    simpa only [hAdj] using LinearPMap.adjoint_isFormalAdjoint hSelf.dense_domain
  obtain ⟨hg,hCov⟩ := source_abstract_unbounded_covariance K hClosed hKInj F hF hFInj hcomm g hDg
  refine ⟨hg,?_⟩
  have hd := sourceHilbertNormalizer_mixed_domain F 1 hF hFInj
    (K.inverse ⟨sourceHilbertNormalizer F hF hFInj g,hDg⟩)
  have he := hSym f ⟨F (K.inverse ⟨sourceHilbertNormalizer F hF hFInj g,hDg⟩),hd⟩
  exact he.trans (congrArg (inner ℂ (f : H)) hCov)

end UV
