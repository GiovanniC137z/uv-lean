import UV.UnboundedSourceCutDomains
import UV.UnboundedSourceDomain
import UV.UnboundedSourceCutCore

/-! The complete free-source calculation on the actual common reducing
spectral core of separate supplied resolutions. Every domain, invariance,
graph-core and covariance conclusion is derived from the spectral data. -/

noncomputable section
open Set Filter
open scoped Topology InnerProductSpace

namespace UV

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem sourcePVM_self_commute (P : SourcePVM H) (s t : Set ℝ)
    (hs : MeasurableSet s) (ht : MeasurableSet t) : Commute (P.projection s) (P.projection t) := by
  change P.projection s*P.projection t = P.projection t*P.projection s
  rw [← P.inter s t hs ht,← P.inter t s ht hs,inter_comm]

theorem sourceResolution_joint_graph_commutes {K : H →ₗ.[ℂ] H}
    (P : SourcePVM H) (RK : SourceSpectralResolution K)
    (hPQ : ∀ s t, MeasurableSet s → MeasurableSet t → Commute (P.projection s) (RK.measure.projection t))
    (n : ℕ) : sourceGraphCommutes K (sourcePVMJointProjection P RK.measure n) := by
  apply sourceGraphCommutes_mul
  · exact sourceResolution_graph_commutes_bounded RK _ (fun s hs =>
      (hPQ _ _ (sourcePositiveSpectralCut_measurable n) hs).symm)
  · exact sourceResolution_graph_commutes_bounded RK _ (fun s hs =>
      sourcePVM_self_commute RK.measure s _ hs (sourcePositiveSpectralCut_measurable n))

theorem sourceResolution_joint_commutes_F (F : H →L[ℂ] H)
    (RF : SourceSpectralResolution (F.toLinearMap.toPMap ⊤)) (Q : SourcePVM H)
    (hPQ : ∀ s t, MeasurableSet s → MeasurableSet t → Commute (RF.measure.projection s) (Q.projection t))
    (n : ℕ) : Commute F (sourcePVMJointProjection RF.measure Q n) :=
  (sourceResolution_bounded_commutes_projection F RF RF.measure
    (sourcePVM_self_commute RF.measure) _ (sourcePositiveSpectralCut_measurable n)).mul_right
      (sourceResolution_bounded_commutes_projection F RF Q hPQ _ (sourcePositiveSpectralCut_measurable n))

omit [CompleteSpace H] in
theorem sourceGraphCommutes_bounded {A B : H →L[ℂ] H} (h : Commute A B) :
    sourceGraphCommutes (A.toLinearMap.toPMap ⊤) B := by
  intro x
  apply (A.toLinearMap.toPMap ⊤).mem_graph_iff.mpr
  refine ⟨⟨B (x : H),Submodule.mem_top⟩,rfl,?_⟩
  exact congrArg (fun C : H →L[ℂ] H => C (x : H)) h.eq

/-- An actual graph-commuting cut preserves the literal common cut union.
This invariant-domain fact is a consequence, not spectral input data. -/
theorem sourcePVM_core_invariant (P Q : SourcePVM H)
    (hPQ : ∀ s t, MeasurableSet s → MeasurableSet t → Commute (P.projection s) (Q.projection t))
    (A : H →ₗ.[ℂ] H) (hDom : sourcePVMJointCore P Q ≤ A.domain)
    (hComm : ∀ n, sourceGraphCommutes A (sourcePVMJointProjection P Q n))
    (f : sourcePVMJointCore P Q) : A ⟨f.val,hDom f.property⟩ ∈ sourcePVMJointCore P Q := by
  obtain ⟨n,x,hx⟩ := (sourcePVM_jointCore_mem_iff P Q hPQ f.val).mp f.property
  have hfixed : sourcePVMJointProjection P Q n f.val = f.val := by
    rw [← hx]
    exact congrArg (fun B : H →L[ℂ] H => B x) (sourcePVM_jointProjection_idempotent P Q hPQ n)
  let fA : A.domain := ⟨f.val,hDom f.property⟩
  obtain ⟨g,hg,hAg⟩ := A.mem_graph_iff.mp (hComm n fA)
  dsimp only [Prod.fst, Prod.snd] at hg hAg
  have hgEq : g = fA := Subtype.ext (hg.trans hfixed)
  have hfixedImage : sourcePVMJointProjection P Q n (A fA) = A fA := by
    rw [← hAg,hgEq]
  exact Submodule.mem_iSup_of_mem n ⟨A fA,hfixedImage⟩

inductive SourceAbstractFactor
  | kinetic | covariance | normalizer | damping | half

def sourceSpectralPartial (K : H →ₗ.[ℂ] H) (F : H →L[ℂ] H)
    (hF : 0 ≤ F) (hFInj : Function.Injective F) : SourceAbstractFactor → H →ₗ.[ℂ] H
  | .kinetic => K
  | .covariance => K.inverse
  | .normalizer => sourceHilbertNormalizer F hF hFInj
  | .damping => F.toLinearMap.toPMap ⊤
  | .half => (CFC.sqrt F : H →L[ℂ] H).toLinearMap.toPMap ⊤

theorem sourceSpectralPartial_domain (K : H →ₗ.[ℂ] H) (F : H →L[ℂ] H)
    (hF : 0 ≤ F) (hFInj : Function.Injective F)
    (RF : SourceSpectralResolution (F.toLinearMap.toPMap ⊤)) (RK : SourceSpectralResolution K)
    (hPQ : ∀ s t, MeasurableSet s → MeasurableSet t →
      Commute (RF.measure.projection s) (RK.measure.projection t)) (j : SourceAbstractFactor) :
    sourcePVMJointCore RF.measure RK.measure ≤ (sourceSpectralPartial K F hF hFInj j).domain := by
  cases j
  · exact source_jointCore_kinetic_domain RF.measure RK hPQ
  · exact source_jointCore_covariance_domain RF.measure RK hPQ
  · exact source_jointCore_normalizer_domain F hF hFInj RF RK.measure
  · exact le_top
  · exact le_top

theorem sourceSpectralPartial_graph_commutes (K : H →ₗ.[ℂ] H) (hKInj : Function.Injective K)
    (F : H →L[ℂ] H) (hF : 0 ≤ F) (hFInj : Function.Injective F)
    (RF : SourceSpectralResolution (F.toLinearMap.toPMap ⊤)) (RK : SourceSpectralResolution K)
    (hPQ : ∀ s t, MeasurableSet s → MeasurableSet t →
      Commute (RF.measure.projection s) (RK.measure.projection t)) (j : SourceAbstractFactor) (n : ℕ) :
    sourceGraphCommutes (sourceSpectralPartial K F hF hFInj j)
      (sourcePVMJointProjection RF.measure RK.measure n) := by
  have hFJ := sourceResolution_joint_commutes_F F RF RK.measure hPQ n
  cases j
  · exact sourceResolution_joint_graph_commutes RF.measure RK hPQ n
  · exact sourcePartialInverse_graphCommutes K hKInj _
      (sourceResolution_joint_graph_commutes RF.measure RK hPQ n)
  · exact sourceRangeInverse_graphCommutes (CFC.sqrt F) (source_sqrt_injective hF hFInj) _
      (sourceOperator_sqrt_commute hFJ)
  · exact sourceGraphCommutes_bounded hFJ
  · exact sourceGraphCommutes_bounded (sourceOperator_sqrt_commute hFJ)

/-- Every actual source operator is restricted to the proved invariant
common core, so compositions below have no hidden domain obligation. -/
def sourceSpectralCoreMap (K : H →ₗ.[ℂ] H) (hKInj : Function.Injective K)
    (F : H →L[ℂ] H) (hF : 0 ≤ F) (hFInj : Function.Injective F)
    (RF : SourceSpectralResolution (F.toLinearMap.toPMap ⊤)) (RK : SourceSpectralResolution K)
    (hPQ : ∀ s t, MeasurableSet s → MeasurableSet t →
      Commute (RF.measure.projection s) (RK.measure.projection t)) (j : SourceAbstractFactor) :
    sourcePVMJointCore RF.measure RK.measure →ₗ[ℂ] sourcePVMJointCore RF.measure RK.measure where
  toFun f := ⟨sourceSpectralPartial K F hF hFInj j
      ⟨f.val,sourceSpectralPartial_domain K F hF hFInj RF RK hPQ j f.property⟩,
    sourcePVM_core_invariant RF.measure RK.measure hPQ _
      (sourceSpectralPartial_domain K F hF hFInj RF RK hPQ j)
      (sourceSpectralPartial_graph_commutes K hKInj F hF hFInj RF RK hPQ j) f⟩
  map_add' f g := by
    apply Subtype.ext
    exact (sourceSpectralPartial K F hF hFInj j).map_add
      ⟨f.val,sourceSpectralPartial_domain K F hF hFInj RF RK hPQ j f.property⟩
      ⟨g.val,sourceSpectralPartial_domain K F hF hFInj RF RK hPQ j g.property⟩
  map_smul' c f := by
    apply Subtype.ext
    exact (sourceSpectralPartial K F hF hFInj j).map_smul c
      ⟨f.val,sourceSpectralPartial_domain K F hF hFInj RF RK hPQ j f.property⟩

/-- The literal common reducing cut union is a genuine graph core for K,
Delta and the generally unbounded normalizer T. -/
theorem source_spectral_common_graphCore (K : H →ₗ.[ℂ] H) (hClosed : K.IsClosed)
    (hKInj : Function.Injective K) (F : H →L[ℂ] H) (hF : 0 ≤ F) (hFInj : Function.Injective F)
    (RF : SourceSpectralResolution (F.toLinearMap.toPMap ⊤)) (RK : SourceSpectralResolution K)
    (hPQ : ∀ s t, MeasurableSet s → MeasurableSet t →
      Commute (RF.measure.projection s) (RK.measure.projection t))
    (hposF : RF.measure.projection (Ioi 0) = 1) (hposK : RK.measure.projection (Ioi 0) = 1) :
    K.HasCore (sourcePVMJointCore RF.measure RK.measure) ∧
      K.inverse.HasCore (sourcePVMJointCore RF.measure RK.measure) ∧
      (sourceHilbertNormalizer F hF hFInj).HasCore (sourcePVMJointCore RF.measure RK.measure) := by
  have hRange : ∀ n x, sourcePVMJointProjection RF.measure RK.measure n x ∈
      sourcePVMJointCore RF.measure RK.measure := fun n x => Submodule.mem_iSup_of_mem n ⟨x,rfl⟩
  have hApprox := sourcePVM_jointCut_tendsto RF.measure RK.measure hposF hposK
  refine ⟨?_,?_,?_⟩
  · exact sourceGraphCore_of_cut_approximation K _ hClosed
      (sourceSpectralPartial_domain K F hF hFInj RF RK hPQ .kinetic) _ hRange
      (sourceSpectralPartial_graph_commutes K hKInj F hF hFInj RF RK hPQ .kinetic) hApprox
  · exact sourceGraphCore_of_cut_approximation K.inverse _
      (sourcePartialInverse_isClosed K hClosed hKInj)
      (sourceSpectralPartial_domain K F hF hFInj RF RK hPQ .covariance) _ hRange
      (sourceSpectralPartial_graph_commutes K hKInj F hF hFInj RF RK hPQ .covariance) hApprox
  · exact sourceGraphCore_of_cut_approximation (sourceHilbertNormalizer F hF hFInj) _
      (sourceHilbertNormalizer_selfAdjoint F hF hFInj).isClosed
      (sourceSpectralPartial_domain K F hF hFInj RF RK hPQ .normalizer) _ hRange
      (sourceSpectralPartial_graph_commutes K hKInj F hF hFInj RF RK hPQ .normalizer) hApprox

section Normalization

variable (K : H →ₗ.[ℂ] H) (hClosed : K.IsClosed) (hKInj : Function.Injective K)
  (F : H →L[ℂ] H) (hF : 0 ≤ F) (hFInj : Function.Injective F)
  (RF : SourceSpectralResolution (F.toLinearMap.toPMap ⊤)) (RK : SourceSpectralResolution K)
  (hPQ : ∀ s t, MeasurableSet s → MeasurableSet t →
    Commute (RF.measure.projection s) (RK.measure.projection t))

include hClosed in
/-- Exact normalized covariance on the actual common reducing spectral
core. Every intermediate vector lies in the actual operator domain. -/
theorem source_spectral_normalized_covariance :
    let M := sourceSpectralCoreMap K hKInj F hF hFInj RF RK hPQ
    ∀ f, M .normalizer (M .damping (M .covariance (M .normalizer f))) = M .covariance f := by
  dsimp only
  intro f
  let fT : (sourceHilbertNormalizer F hF hFInj).domain :=
    ⟨f.val,sourceSpectralPartial_domain K F hF hFInj RF RK hPQ .normalizer f.property⟩
  have hDf : sourceHilbertNormalizer F hF hFInj fT ∈ K.inverse.domain :=
    source_jointCore_covariance_domain RF.measure RK hPQ
      (sourceSpectralCoreMap K hKInj F hF hFInj RF RK hPQ .normalizer f).property
  obtain ⟨hf,he⟩ := source_abstract_unbounded_covariance K hClosed hKInj F hF hFInj
    (sourceResolution_strong_commutes_graph F RF RK hPQ) fT hDf
  apply Subtype.ext
  exact he

/-- A normalized external source and an original field retain exactly
the positive square-root damping factor. -/
theorem source_spectral_mixed_covariance :
    let M := sourceSpectralCoreMap K hKInj F hF hFInj RF RK hPQ
    ∀ f, M .normalizer (M .damping (M .covariance f)) = M .half (M .covariance f) := by
  dsimp only
  intro f
  apply Subtype.ext
  exact source_abstract_unbounded_mixed K F hF hFInj
    ⟨f.val,sourceSpectralPartial_domain K F hF hFInj RF RK hPQ .covariance f.property⟩

/-- Ordinary kinetic amputation leaves the square-root damping factor,
with the inverse-domain membership derived from the genuine kinetic map. -/
theorem source_spectral_mixed_amputation :
    let M := sourceSpectralCoreMap K hKInj F hF hFInj RF RK hPQ
    ∀ f, M .normalizer (M .damping (M .covariance (M .kinetic f))) = M .half f := by
  dsimp only
  intro f
  apply Subtype.ext
  exact source_abstract_unbounded_amputation K hKInj F hF hFInj
    ⟨f.val,sourceSpectralPartial_domain K F hF hFInj RF RK hPQ .kinetic f.property⟩

include hClosed in
/-- The Hermitian smeared source covariance on the actual spectral core. -/
theorem source_spectral_smeared_covariance :
    let M := sourceSpectralCoreMap K hKInj F hF hFInj RF RK hPQ
    ∀ f g, inner ℂ (M .normalizer f : H)
        (M .damping (M .covariance (M .normalizer g)) : H) =
      inner ℂ (f : H) (M .covariance g : H) := by
  dsimp only
  intro f g
  let fT : (sourceHilbertNormalizer F hF hFInj).domain :=
    ⟨f.val,sourceSpectralPartial_domain K F hF hFInj RF RK hPQ .normalizer f.property⟩
  let gT : (sourceHilbertNormalizer F hF hFInj).domain :=
    ⟨g.val,sourceSpectralPartial_domain K F hF hFInj RF RK hPQ .normalizer g.property⟩
  have hDg : sourceHilbertNormalizer F hF hFInj gT ∈ K.inverse.domain :=
    source_jointCore_covariance_domain RF.measure RK hPQ
      (sourceSpectralCoreMap K hKInj F hF hFInj RF RK hPQ .normalizer g).property
  obtain ⟨hg,he⟩ := source_abstract_unbounded_smeared K hClosed hKInj F hF hFInj
    (sourceResolution_strong_commutes_graph F RF RK hPQ) fT gT hDg
  exact he

include hClosed in
/-- Full operational free-source theorem for the separate positive,
injective spectral resolutions invoked by the source. The support
hypotheses express positivity and absence of a zero spectral subspace.
This theorem constructs the dense common reducing graph core and all
source identities; it does not assert spectral classification from a
bare self-adjoint partial operator. -/
theorem free_source_normalization_actual_spectral_resolutions
    (hposF : RF.measure.projection (Ioi 0) = 1)
    (hposK : RK.measure.projection (Ioi 0) = 1) :
    let C := sourcePVMJointCore RF.measure RK.measure
    let M := sourceSpectralCoreMap K hKInj F hF hFInj RF RK hPQ
    Dense (C : Set H) ∧
      IsSelfAdjoint (sourceHilbertNormalizer F hF hFInj) ∧
      K.HasCore C ∧ K.inverse.HasCore C ∧
      (sourceHilbertNormalizer F hF hFInj).HasCore C ∧
      (∀ f, M .normalizer (M .damping (M .covariance (M .normalizer f))) = M .covariance f) ∧
      (∀ f, M .normalizer (M .damping (M .covariance f)) = M .half (M .covariance f)) ∧
      (∀ f, M .normalizer (M .damping (M .covariance (M .kinetic f))) = M .half f) ∧
      (∀ f g, inner ℂ (M .normalizer f : H)
          (M .damping (M .covariance (M .normalizer g)) : H) =
        inner ℂ (f : H) (M .covariance g : H)) := by
  dsimp only
  obtain ⟨hK,hD,hT⟩ := source_spectral_common_graphCore K hClosed hKInj F hF hFInj
    RF RK hPQ hposF hposK
  exact ⟨sourcePVM_jointCore_dense RF.measure RK.measure hposF hposK,
    sourceHilbertNormalizer_selfAdjoint F hF hFInj,hK,hD,hT,
    source_spectral_normalized_covariance K hClosed hKInj F hF hFInj RF RK hPQ,
    source_spectral_mixed_covariance K hKInj F hF hFInj RF RK hPQ,
    source_spectral_mixed_amputation K hKInj F hF hFInj RF RK hPQ,
    source_spectral_smeared_covariance K hClosed hKInj F hF hFInj RF RK hPQ⟩

end Normalization

end UV
