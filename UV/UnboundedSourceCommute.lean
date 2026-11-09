import UV.UnboundedSourceInverse
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

/-! Continuous functional calculus preserves domain commutation with a
closed unbounded operator. The commutant is constructed from its actual
closed graph, not from assumed square-root intertwining identities. -/

noncomputable section
open Set Filter
open scoped Topology

namespace UV

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def sourceGraphCommutes (K : H →ₗ.[ℂ] H) (A : H →L[ℂ] H) : Prop :=
  ∀ x : K.domain, (A (x : H), A (K x)) ∈ K.graph

omit [CompleteSpace H] in
theorem sourceGraphCommutes_one (K : H →ₗ.[ℂ] H) : sourceGraphCommutes K 1 := by
  intro x
  simp

omit [CompleteSpace H] in
theorem sourceGraphCommutes_add {K : H →ₗ.[ℂ] H} {A B : H →L[ℂ] H}
    (hA : sourceGraphCommutes K A) (hB : sourceGraphCommutes K B) :
    sourceGraphCommutes K (A+B) := by
  intro x
  simpa only [ContinuousLinearMap.add_apply, Prod.mk_add_mk] using K.graph.add_mem (hA x) (hB x)

omit [CompleteSpace H] in
theorem sourceGraphCommutes_mul {K : H →ₗ.[ℂ] H} {A B : H →L[ℂ] H}
    (hA : sourceGraphCommutes K A) (hB : sourceGraphCommutes K B) :
    sourceGraphCommutes K (A*B) := by
  intro x
  obtain ⟨y,hy,hKy⟩ := K.mem_graph_iff.mp (hB x)
  have ha := hA y
  simpa only [ContinuousLinearMap.mul_apply, hy, hKy] using ha

theorem sourceGraphCommutes_real_scalar (K : H →ₗ.[ℂ] H) (r : ℝ) :
    sourceGraphCommutes K (algebraMap ℝ (H →L[ℂ] H) r) := by
  intro x
  convert K.graph.smul_mem (r : ℂ) (K.mem_graph x) using 1

def sourceClosedGraphCommutant (K : H →ₗ.[ℂ] H) : StarSubalgebra ℝ (H →L[ℂ] H) where
  carrier := {A | sourceGraphCommutes K A ∧ sourceGraphCommutes K (star A)}
  zero_mem' := by
    constructor <;> intro x <;> simp
  one_mem' := by simpa using And.intro (sourceGraphCommutes_one K) (sourceGraphCommutes_one K)
  add_mem' hA hB := ⟨sourceGraphCommutes_add hA.1 hB.1,
    by simpa only [star_add] using sourceGraphCommutes_add hA.2 hB.2⟩
  mul_mem' hA hB := ⟨sourceGraphCommutes_mul hA.1 hB.1,
    by simpa only [star_mul] using sourceGraphCommutes_mul hB.2 hA.2⟩
  algebraMap_mem' r := by
    change sourceGraphCommutes K (algebraMap ℝ (H →L[ℂ] H) r) ∧
      sourceGraphCommutes K (star (algebraMap ℝ (H →L[ℂ] H) r))
    simpa only [← algebraMap_star_comm, star_trivial] using
      And.intro (sourceGraphCommutes_real_scalar K r) (sourceGraphCommutes_real_scalar K r)
  star_mem' {A} hA := by
    change sourceGraphCommutes K (star A) ∧ sourceGraphCommutes K (star (star A))
    simpa only [star_star] using And.intro hA.2 hA.1

omit [CompleteSpace H] in
/-- The operator-norm limit of actual graph-preserving intertwiners still
preserves and intertwines the closed graph. -/
theorem sourceGraphCommutes_isClosed (K : H →ₗ.[ℂ] H) (hK : K.IsClosed) :
    IsClosed {A : H →L[ℂ] H | sourceGraphCommutes K A} := by
  rw [show {A : H →L[ℂ] H | sourceGraphCommutes K A} =
    ⋂ x : K.domain, {A : H →L[ℂ] H | (A (x : H),A (K x)) ∈ K.graph} from by
      ext A; simp only [sourceGraphCommutes, mem_setOf_eq, mem_iInter]]
  apply isClosed_iInter
  intro x
  apply hK.preimage
  exact (ContinuousLinearMap.apply ℂ H (x : H)).continuous.prodMk
    (ContinuousLinearMap.apply ℂ H (K x)).continuous

theorem sourceClosedGraphCommutant_isClosed (K : H →ₗ.[ℂ] H) (hK : K.IsClosed) :
    IsClosed (sourceClosedGraphCommutant K : Set (H →L[ℂ] H)) :=
  (sourceGraphCommutes_isClosed K hK).inter
    ((sourceGraphCommutes_isClosed K hK).preimage continuous_star)

/-- Bounded positive F commuting on the actual domain of closed K forces
sqrt(F) to preserve that same domain and to commute there. -/
theorem source_sqrt_graph_commutes {K : H →ₗ.[ℂ] H} (hK : K.IsClosed)
    {F : H →L[ℂ] H} (hF : 0 ≤ F) (hcomm : sourceGraphCommutes K F) :
    sourceGraphCommutes K (CFC.sqrt F) := by
  have hSelf : IsSelfAdjoint F := IsSelfAdjoint.of_nonneg hF
  have hmem : F ∈ sourceClosedGraphCommutant K :=
    ⟨hcomm, by simpa only [hSelf.star_eq] using hcomm⟩
  have hle := StarAlgebra.elemental.le_of_mem (sourceClosedGraphCommutant_isClosed K hK) hmem
  have hsqrt : CFC.sqrt F ∈ StarAlgebra.elemental ℝ F := by
    rw [CFC.sqrt_eq_real_sqrt F hF, cfcₙ_eq_cfc (hf0 := by simp)]
    exact cfc_apply_mem_elemental Real.sqrt F
  exact (hle hsqrt).1

end UV
