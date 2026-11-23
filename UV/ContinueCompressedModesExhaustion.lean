import UV.ContinueCompressedGraph
import Mathlib.Analysis.Normed.Group.Tannery

/-! Remove finite carrier/mode restrictions from each mixed graph after
the exact finite source coefficient has been expanded. All intermediate
charged momenta are tested at once, including open endpoints. -/

noncomputable section

open MeasureTheory Set Filter UV.SectorPlane
open scoped Topology

namespace UV

variable {ι V Z : Type*} [Fintype ι] [Fintype V] [MeasurableSpace Z]

/-- The finite sums of lengths control every momentum on the finitely
many charged arcs and every independent integer mode. -/
def compressedSectionSize (P : V → CompressedPiece)
    (s : (V → ℤ) → (v : V) → Z → Fin (P v).length → OSFourSpace)
    (j : V → ℤ) (x : Z × (V → OSFourSpace)) : ℝ :=
  ∑ v, (|(j v : ℝ)| + ∑ a, ‖x.2 v+s j v x.1 a‖)

omit [MeasurableSpace Z] in
theorem compressed_section_contains (P : V → CompressedPiece)
    (s : (V → ℤ) → (v : V) → Z → Fin (P v).length → OSFourSpace)
    (j : V → ℤ) (x : Z × (V → OSFourSpace)) (v : V) (a : Fin (P v).length) :
    |(j v : ℝ)| ≤ compressedSectionSize P s j x ∧
      ‖x.2 v+s j v x.1 a‖ ≤ compressedSectionSize P s j x := by
  let f (v : V) := |(j v : ℝ)| + ∑ a, ‖x.2 v+s j v x.1 a‖
  have h : f v ≤ ∑ w, f w := Finset.single_le_sum (fun w _ => by dsimp [f]; positivity) (Finset.mem_univ v)
  constructor
  · exact (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)).trans h
  · exact ((Finset.single_le_sum (fun a _ => norm_nonneg (x.2 v+s j v x.1 a)) (Finset.mem_univ a)).trans
      (le_add_of_nonneg_left (abs_nonneg _))).trans h

private theorem compressed_exhaustion {J X Y : Type*} [MeasurableSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (ν : Measure X) (F : J → X → Y) (hf : ∀ j, Integrable (F j) ν) (hb : Summable (fun j => ∫ x, ‖F j x‖ ∂ν))
    (B : J → ℕ → Set X) (hM : ∀ j N, MeasurableSet (B j N)) (hmono : ∀ j, Monotone (B j))
    (hcover : ∀ j, ⋃ N, B j N = univ) :
    Tendsto (fun N : ℕ => ∑' j, ∫ x in B j N, F j x ∂ν) atTop (𝓝 (∑' j, ∫ x, F j x ∂ν)) := by
  apply tendsto_tsum_of_dominated_convergence hb
  · intro j
    simpa only [hcover,Measure.restrict_univ] using tendsto_setIntegral_of_monotone (f := F j)
      (hM j) (hmono j) (hf j).integrableOn
  · exact Eventually.of_forall fun n j => (norm_integral_le_integral_norm _).trans
      (integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun _ => norm_nonneg _) (hf j).norm)

/-- The signed integral and the integral of the absolute value both
converge to their unrestricted graph values, including the mode sums. -/
theorem compressed_graph_remove_sections (σ : Measure OSFourSpace) (μ : Measure Z) (m L θ : ℝ)
    (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (P : V → CompressedPiece)
    (s : (V → ℤ) → (v : V) → Z → Fin (P v).length → OSFourSpace) (hs : ∀ j v a, Measurable (s j v · a))
    (Δ : V → Z → OSFourSpace) (W : Z → ℂ) (h : CompressedGraphAbsolute σ μ m L θ T P s Δ W) :
    let F := fun (j : V → ℤ) => wilsonJointFactors W (fun v z => (P v).value m L T (normalLegFrequency L θ (j v)) (s j v z) (Δ v z))
    let ν := μ.prod (Measure.pi fun _ : V => σ)
    let B := fun (j : V → ℤ) (N : ℕ) => {x : Z × (V → OSFourSpace) | ∀ v, |(j v:ℝ)| ≤ N ∧
      ∀ a, ‖x.2 v+s j v x.1 a‖ ≤ N}
    Tendsto (fun N => ∑' j, ∫ x in B j N, F j x ∂ν) atTop (𝓝 (∑' j, ∫ x, F j x ∂ν)) ∧
    Tendsto (fun N => ∑' j, ∫ x in B j N, ‖F j x‖ ∂ν) atTop (𝓝 (∑' j, ∫ x, ‖F j x‖ ∂ν)) := by
  let F := fun (j : V → ℤ) => wilsonJointFactors W (fun v z => (P v).value m L T (normalLegFrequency L θ (j v)) (s j v z) (Δ v z))
  let ν := μ.prod (Measure.pi fun _ : V => σ)
  let B (j : V → ℤ) (N : ℕ) := {x : Z × (V → OSFourSpace) | ∀ v, |(j v:ℝ)| ≤ N ∧
      ∀ a, ‖x.2 v+s j v x.1 a‖ ≤ N}
  have hM (j N) : MeasurableSet (B j N) := by
    simp only [B,setOf_forall,setOf_and]
    apply MeasurableSet.iInter
    intro v
    apply MeasurableSet.inter (measurableSet_le measurable_const measurable_const)
    apply MeasurableSet.iInter
    intro a
    exact measurableSet_le ((((measurable_pi_apply v).comp measurable_snd).add ((hs j v a).comp measurable_fst)).norm) measurable_const
  have hmono (j) : Monotone (B j) := fun _ _ hab x hx v =>
    ⟨(hx v).1.trans (Nat.cast_le.mpr hab),fun a => ((hx v).2 a).trans (Nat.cast_le.mpr hab)⟩
  have hcover (j) : ⋃ N, B j N = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    obtain ⟨N,hN⟩ := exists_nat_ge (compressedSectionSize P s j x)
    refine ⟨N,fun v => ⟨?_,fun a => (compressed_section_contains P s j x v a).2.trans hN⟩⟩
    have hn : 0 < (P v).length := by cases P v <;> simp [CompressedPiece.length]
    exact (compressed_section_contains P s j x v ⟨0,hn⟩).1.trans hN
  exact ⟨compressed_exhaustion ν F h.1 h.2 B hM hmono hcover,
    compressed_exhaustion ν (fun j x => ‖F j x‖) (fun j => (h.1 j).norm)
      (by simpa only [norm_norm] using h.2) B hM hmono hcover⟩

/-- At finite carrier volume each bounded momentum section intersects
the complete reciprocal lattice in a genuinely finite state set. -/
theorem compressed_lattice_section_finite (b : NormalReciprocalBasis) (R : ℝ) :
    (Metric.closedBall (0:OSFourSpace) R ∩ (NormalReciprocalLattice b : Set OSFourSpace)).Finite :=
  ZSpan.setFinite_inter b (Metric.isBounded_closedBall)

end UV
