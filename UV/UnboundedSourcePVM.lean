import UV.UnboundedSourceCore
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.MeasureTheory.VectorMeasure.Basic
import Mathlib.Algebra.Order.Disjointed

/-! Projection-valued spectral measures and their actual joint cut core.
Only the standard projection-measure laws are input data; cut convergence
and density of the joint core are consequences. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace

namespace UV

/-- A normalized orthogonal projection-valued measure on the real line.
Countable additivity is strong vector-valued additivity, not a spectral
core or a covariance identity. -/
structure SourcePVM (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  projection : Set ℝ → H →L[ℂ] H
  empty : projection ∅ = 0
  univ : projection univ = 1
  selfAdjoint : ∀ s, MeasurableSet s → IsSelfAdjoint (projection s)
  inter : ∀ s t, MeasurableSet s → MeasurableSet t →
    projection (s ∩ t) = projection s * projection t
  countable : ∀ s : ℕ → Set ℝ, (∀ n, MeasurableSet (s n)) →
    Pairwise (fun i j => Disjoint (s i) (s j)) → ∀ x : H,
    HasSum (fun n => projection (s n) x) (projection (⋃ n, s n) x)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem sourcePVM_idempotent (P : SourcePVM H) {s : Set ℝ} (hs : MeasurableSet s) :
    P.projection s * P.projection s = P.projection s := by
  simpa only [inter_self] using (P.inter s s hs hs).symm

theorem sourcePVM_norm_le_one (P : SourcePVM H) {s : Set ℝ} (hs : MeasurableSet s) :
    ‖P.projection s‖ ≤ 1 := by
  have h : ‖P.projection s * P.projection s‖ = ‖P.projection s‖ ^ 2 :=
    IsSelfAdjoint.norm_mul_self (x := P.projection s) (P.selfAdjoint s hs)
  rw [sourcePVM_idempotent P hs] at h
  have hn := norm_nonneg (P.projection s)
  nlinarith

def sourcePVMVectorMeasure (P : SourcePVM H) (x : H) : VectorMeasure ℝ H := by
  classical
  exact
    { measureOf' := fun s => if MeasurableSet s then P.projection s x else 0
      empty' := by simp [P.empty]
      not_measurable' := by intro s hs; simp only [if_neg hs]
      m_iUnion' := by
        intro s hs hd
        simpa only [if_pos (MeasurableSet.iUnion hs), if_pos (hs _)] using P.countable s hs hd x }

theorem sourcePVMVectorMeasure_apply (P : SourcePVM H) (x : H) {s : Set ℝ}
    (hs : MeasurableSet s) : sourcePVMVectorMeasure P x s = P.projection s x := by
  classical
  exact if_pos hs

theorem sourcePVM_disjoint_union (P : SourcePVM H) {s t : Set ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hd : Disjoint s t) :
    P.projection (s ∪ t) = P.projection s + P.projection t := by
  apply ContinuousLinearMap.ext
  intro x
  have h := (sourcePVMVectorMeasure P x).of_union hd hs ht
  simpa only [sourcePVMVectorMeasure_apply P x (hs.union ht),
    sourcePVMVectorMeasure_apply P x hs, sourcePVMVectorMeasure_apply P x ht,
    ContinuousLinearMap.add_apply] using h

/-- Strong continuity on increasing measurable sets is derived solely
from countable vector-valued additivity. -/
theorem sourcePVM_tendsto_iUnion (P : SourcePVM H) (s : ℕ → Set ℝ)
    (hs : ∀ n, MeasurableSet (s n)) (hm : Monotone s) (x : H) :
    Tendsto (fun n => P.projection (s n) x) atTop (𝓝 (P.projection (⋃ n, s n) x)) := by
  let v := sourcePVMVectorMeasure P x
  have hpart (n : ℕ) : (∑ i ∈ Finset.range (n+1), v (disjointed s i)) = v (s n) := by
    induction n with
    | zero => simp only [Nat.zero_add, Finset.sum_range_one, disjointed_zero]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, hm.disjointed_add_one n]
      exact v.of_add_of_diff (hs n) (hs (n+1)) (hm (Nat.le_succ n))
  have hlim := (v.m_iUnion (MeasurableSet.disjointed hs) (disjoint_disjointed s)).tendsto_sum_nat
  have hlim' := hlim.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun n => ∑ i ∈ Finset.range (n+1), v (disjointed s i)) atTop
    (𝓝 (v (⋃ i, disjointed s i))) at hlim'
  have hv : Tendsto (fun n => v (s n)) atTop (𝓝 (v (⋃ n, s n))) := by
    simpa only [hpart, iUnion_disjointed] using hlim'
  have hefun : (fun n => v (s n)) = fun n => P.projection (s n) x :=
    funext fun n => sourcePVMVectorMeasure_apply P x (hs n)
  have hend : v (⋃ n, s n) = P.projection (⋃ n, s n) x :=
    sourcePVMVectorMeasure_apply P x (MeasurableSet.iUnion hs)
  rwa [hefun, hend] at hv

def sourcePositiveSpectralCut (n : ℕ) : Set ℝ :=
  Icc ((n : ℝ)+1)⁻¹ ((n : ℝ)+1)

theorem sourcePositiveSpectralCut_measurable (n : ℕ) :
    MeasurableSet (sourcePositiveSpectralCut n) := measurableSet_Icc

theorem sourcePositiveSpectralCut_mono : Monotone sourcePositiveSpectralCut := by
  intro n m hnm x hx
  have h : x ∈ sourceJointSpectralCut (id : ℝ → ℝ) id m :=
    sourceJointSpectralCut_mono (id : ℝ → ℝ) id hnm ⟨hx.1, hx.2, hx.1, hx.2⟩
  exact ⟨h.1, h.2.1⟩

theorem sourcePositiveSpectralCut_iUnion : (⋃ n, sourcePositiveSpectralCut n) = Ioi (0 : ℝ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact (inv_pos.mpr (by positivity : (0 : ℝ) < (n : ℝ)+1)).trans_le hn.1
  · intro hx
    obtain ⟨N, hN⟩ := sourceJointSpectralCut_eventually_mem
      (F := (id : ℝ → ℝ)) (K := id) (x := x) hx hx
    have h := hN N le_rfl
    exact mem_iUnion.mpr ⟨N, h.1, h.2.1⟩

theorem sourcePVM_positiveCut_tendsto (P : SourcePVM H)
    (hpos : P.projection (Ioi 0) = 1) (x : H) :
    Tendsto (fun n => P.projection (sourcePositiveSpectralCut n) x) atTop (𝓝 x) := by
  simpa only [sourcePositiveSpectralCut_iUnion, hpos, ContinuousLinearMap.one_apply] using
    sourcePVM_tendsto_iUnion P sourcePositiveSpectralCut
      sourcePositiveSpectralCut_measurable sourcePositiveSpectralCut_mono x

def sourcePVMJointProjection (P Q : SourcePVM H) (n : ℕ) : H →L[ℂ] H :=
  P.projection (sourcePositiveSpectralCut n) * Q.projection (sourcePositiveSpectralCut n)

def sourcePVMJointCore (P Q : SourcePVM H) : Submodule ℂ H :=
  ⨆ n, LinearMap.range (sourcePVMJointProjection P Q n).toLinearMap

/-- Products of the two independently exhausting spectral cuts converge
strongly to the identity. The contractive bound is proved from PVM laws. -/
theorem sourcePVM_jointCut_tendsto (P Q : SourcePVM H)
    (hP : P.projection (Ioi 0) = 1) (hQ : Q.projection (Ioi 0) = 1) (x : H) :
    Tendsto (fun n => sourcePVMJointProjection P Q n x) atTop (𝓝 x) := by
  have hp := sourcePVM_positiveCut_tendsto P hP x
  have hq := sourcePVM_positiveCut_tendsto Q hQ x
  have hpNorm : Tendsto (fun n => ‖P.projection (sourcePositiveSpectralCut n) x-x‖)
      atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hp
  have hqNorm : Tendsto (fun n => ‖Q.projection (sourcePositiveSpectralCut n) x-x‖)
      atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hq
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
  · intro n
    let A := P.projection (sourcePositiveSpectralCut n)
    let B := Q.projection (sourcePositiveSpectralCut n)
    change ‖A (B x)-x‖ ≤ ‖B x-x‖+‖A x-x‖
    have hcontr : ‖A (B x-x)‖ ≤ ‖B x-x‖ := by
      simpa only [one_mul] using A.le_of_opNorm_le
        (sourcePVM_norm_le_one P (sourcePositiveSpectralCut_measurable n)) (B x-x)
    calc
      _ = ‖A (B x-x)+(A x-x)‖ := by rw [map_sub]; congr 1; abel
      _ ≤ ‖A (B x-x)‖+‖A x-x‖ := norm_add_le _ _
      _ ≤ _ := add_le_add_right hcontr _
  · simpa only [zero_add] using hqNorm.add hpNorm

/-- Density of the actual joint spectral cut core is a consequence of the
standard projection-measure laws and positive injective support. -/
theorem sourcePVM_jointCore_dense (P Q : SourcePVM H)
    (hP : P.projection (Ioi 0) = 1) (hQ : Q.projection (Ioi 0) = 1) :
    Dense (sourcePVMJointCore P Q : Set H) := by
  intro x
  apply mem_closure_of_tendsto (sourcePVM_jointCut_tendsto P Q hP hQ x)
  apply Eventually.of_forall
  intro n
  exact Submodule.mem_iSup_of_mem n ⟨x, rfl⟩

theorem sourcePVM_projection_absorb (P : SourcePVM H) {s t : Set ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s ⊆ t) :
    P.projection t * P.projection s = P.projection s := by
  rw [← P.inter t s ht hs, inter_eq_right.mpr hst]

theorem sourcePVM_jointProjection_absorb (P Q : SourcePVM H)
    (hcomm : ∀ s t : Set ℝ, MeasurableSet s → MeasurableSet t →
      Commute (P.projection s) (Q.projection t)) {m n : ℕ} (hmn : m ≤ n) :
    sourcePVMJointProjection P Q n * sourcePVMJointProjection P Q m =
      sourcePVMJointProjection P Q m := by
  let A := P.projection (sourcePositiveSpectralCut n)
  let B := Q.projection (sourcePositiveSpectralCut n)
  let C := P.projection (sourcePositiveSpectralCut m)
  let D := Q.projection (sourcePositiveSpectralCut m)
  have hAC : A*C = C := sourcePVM_projection_absorb P
    (sourcePositiveSpectralCut_measurable m) (sourcePositiveSpectralCut_measurable n)
    (sourcePositiveSpectralCut_mono hmn)
  have hBD : B*D = D := sourcePVM_projection_absorb Q
    (sourcePositiveSpectralCut_measurable m) (sourcePositiveSpectralCut_measurable n)
    (sourcePositiveSpectralCut_mono hmn)
  have hCB : C*B = B*C := (hcomm (sourcePositiveSpectralCut m) (sourcePositiveSpectralCut n)
    (sourcePositiveSpectralCut_measurable m) (sourcePositiveSpectralCut_measurable n)).eq
  change (A*B)*(C*D) = C*D
  calc
    _ = A*(B*C)*D := by noncomm_ring
    _ = A*(C*B)*D := by rw [hCB]
    _ = (A*C)*(B*D) := by noncomm_ring
    _ = _ := by rw [hAC, hBD]

theorem sourcePVM_jointRange_mono (P Q : SourcePVM H)
    (hcomm : ∀ s t : Set ℝ, MeasurableSet s → MeasurableSet t →
      Commute (P.projection s) (Q.projection t)) :
    Monotone (fun n => LinearMap.range (sourcePVMJointProjection P Q n).toLinearMap) := by
  intro m n hmn x hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨sourcePVMJointProjection P Q m y, ?_⟩
  change (sourcePVMJointProjection P Q n * sourcePVMJointProjection P Q m) y = x
  rw [sourcePVM_jointProjection_absorb P Q hcomm hmn]
  exact hy

/-- For strongly commuting PVMs the defined core is literally the union of
the joint cut ranges; no algebraic span enlarges the prescribed core. -/
theorem sourcePVM_jointCore_mem_iff (P Q : SourcePVM H)
    (hcomm : ∀ s t : Set ℝ, MeasurableSet s → MeasurableSet t →
      Commute (P.projection s) (Q.projection t)) (x : H) :
    x ∈ sourcePVMJointCore P Q ↔
      ∃ n, x ∈ LinearMap.range (sourcePVMJointProjection P Q n).toLinearMap := by
  have hmono := sourcePVM_jointRange_mono P Q hcomm
  apply Submodule.mem_iSup_of_directed
  intro m n
  exact ⟨max m n, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩

theorem sourcePVM_jointProjection_idempotent (P Q : SourcePVM H)
    (hcomm : ∀ s t : Set ℝ, MeasurableSet s → MeasurableSet t →
      Commute (P.projection s) (Q.projection t)) (n : ℕ) :
    sourcePVMJointProjection P Q n * sourcePVMJointProjection P Q n =
      sourcePVMJointProjection P Q n := sourcePVM_jointProjection_absorb P Q hcomm le_rfl

theorem sourcePVM_jointProjection_selfAdjoint (P Q : SourcePVM H)
    (hcomm : ∀ s t : Set ℝ, MeasurableSet s → MeasurableSet t →
      Commute (P.projection s) (Q.projection t)) (n : ℕ) :
    IsSelfAdjoint (sourcePVMJointProjection P Q n) := by
  change star (P.projection (sourcePositiveSpectralCut n)*Q.projection (sourcePositiveSpectralCut n)) = _
  rw [star_mul, (Q.selfAdjoint _ (sourcePositiveSpectralCut_measurable n)).star_eq,
    (P.selfAdjoint _ (sourcePositiveSpectralCut_measurable n)).star_eq]
  exact (hcomm _ _ (sourcePositiveSpectralCut_measurable n)
    (sourcePositiveSpectralCut_measurable n)).eq.symm

end UV
