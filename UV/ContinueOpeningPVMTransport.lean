import UV.ContinueOpeningCoordinateMoment
import UV.UnboundedSourceTransport

/-! Transport an actual normalized projection measure, its Borel calculus,
and the first-moment graph through a complex unitary equivalence. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace
namespace UV

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def openingPulledOperator (U : H ≃ₗᵢ[ℂ] E) (A : E →L[ℂ] E) : H →L[ℂ] H :=
  U.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (A.comp U.toContinuousLinearEquiv.toContinuousLinearMap)

omit [CompleteSpace H] [CompleteSpace E] in
theorem opening_pulled_apply (U : H ≃ₗᵢ[ℂ] E) (A : E →L[ℂ] E) (x : H) :
    openingPulledOperator U A x = U.symm (A (U x)) := rfl

private theorem opening_pulled_selfAdjoint (U : H ≃ₗᵢ[ℂ] E) (A : E →L[ℂ] E)
    (h : IsSelfAdjoint A) : IsSelfAdjoint (openingPulledOperator U A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at h ⊢
  intro x y
  change ⟪U.symm (A (U x)),y⟫_ℂ = ⟪x,U.symm (A (U y))⟫_ℂ
  rw [←U.inner_map_map,←U.inner_map_map x,U.apply_symm_apply,U.apply_symm_apply]
  exact h (U x) (U y)

def openingPulledPVM (U : H ≃ₗᵢ[ℂ] E) (P : SourcePVM E) : SourcePVM H where
  projection := fun s => openingPulledOperator U (P.projection s)
  empty := by ext x; simp [P.empty,opening_pulled_apply]
  univ := by ext x; simp [P.univ,opening_pulled_apply]
  selfAdjoint := fun s hs => opening_pulled_selfAdjoint U _ (P.selfAdjoint s hs)
  inter := fun s t hs ht => by ext x; simp [P.inter s t hs ht,opening_pulled_apply]
  countable := fun s hs hd x => (P.countable s hs hd (U x)).map U.symm.toLinearEquiv.toAddMonoidHom U.symm.continuous

def openingPulledBorel (U : H ≃ₗᵢ[ℂ] E) {P : SourcePVM E} (C : SourceBorelCalculus P) :
    SourceBorelCalculus (openingPulledPVM U P) where
  operator := fun f => openingPulledOperator U (C.operator f)
  indicator := fun s hs => congrArg (openingPulledOperator U) (C.indicator s hs)
  add := fun f g hf hg => by ext x; simp [C.add _ _ hf hg,opening_pulled_apply]
  smul := fun a f hf => by
    ext x
    rw [C.smul _ _ hf]
    exact U.symm.map_smul (a:ℂ) ((C.operator f) (U x))
  mul := fun f g hf hg => by ext x; simp [C.mul _ _ hf hg,opening_pulled_apply]
  selfAdjoint := fun f hf => opening_pulled_selfAdjoint U _ (C.selfAdjoint f hf)
  norm_le := fun f B hf hB hbound => by
    apply ContinuousLinearMap.opNorm_le_bound _ hB
    intro x
    rw [opening_pulled_apply,U.symm.norm_map]
    have hh := (C.operator f).le_opNorm (U x)
    rw [U.norm_map] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (C.norm_le f B hf hB hbound) (norm_nonneg x))
  strong_limit := fun f g B hf hg hB hbound hlim x =>
    U.symm.continuous.continuousAt.tendsto.comp (C.strong_limit f g B hf hg hB hbound hlim (U x))

theorem opening_pulled_simple (U : H ≃ₗᵢ[ℂ] E) {P : SourcePVM E} (C : SourceBorelCalculus P)
    (f : SimpleFunc ℝ ℝ) (x : H) :
    sourceSimpleSpectralIntegral (openingPulledPVM U P) f x =
      U.symm (sourceSimpleSpectralIntegral P f (U x)) := by
  rw [←sourceBorel_simple (openingPulledBorel U C),←sourceBorel_simple C]
  rfl

def openingPulledResolution (U : H ≃ₗᵢ[ℂ] E) {K : E →ₗ.[ℂ] E} (S : SourceSpectralResolution K) :
    SourceSpectralResolution (sourceUnitaryConjugate U K) where
  measure := openingPulledPVM U S.measure
  calculus := openingPulledBorel U S.calculus
  moment x y := by
    rw [sourceUnitaryConjugate_graph_mem_iff U K,(S.moment (U x) (U y))]
    simp_rw [opening_pulled_simple U S.calculus]
    constructor
    · intro h
      simpa only [U.symm_apply_apply] using U.symm.continuous.continuousAt.tendsto.comp h
    · intro h
      have ht := U.continuous.continuousAt.tendsto.comp h
      apply ht.congr
      intro n
      exact U.apply_symm_apply _

end UV
