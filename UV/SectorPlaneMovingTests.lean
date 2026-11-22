import UV.SectorPlaneTestSpace
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Same-height multipliers on the fixed compact C² momentum test space. -/

noncomputable section

namespace UV.SectorPlane

open Filter Set
open scoped UV.SectorPlane Topology BoundedContinuousFunction

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

private theorem supported_family_uniform {V : Type*} [NormedAddCommGroup V]
    (K : TopologicalSpace.Compacts MassiveMomentum) (F : ℝ → MassiveMomentum → V)
    (hc : Continuous (Function.uncurry F)) (hs : ∀ t q, q ∉ K → F t q = 0) (t : ℝ) :
    TendstoUniformly F (F t) (𝓝 t) := by
  let G (v : ℝ) (q : K) := F v q
  have hG : Continuous (Function.uncurry G) := hc.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hU := Continuous.tendstoUniformly G hG t
  rw [Metric.tendstoUniformly_iff] at hU ⊢
  intro δ hδ
  filter_upwards [hU δ hδ] with v hv q
  by_cases hq : q ∈ K
  · exact hv ⟨q, hq⟩
  · simpa only [hs t q hq, hs v q hq, dist_self] using hδ

private theorem slice_fderiv_contDiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : WithTop ENat} {F : ℝ → MassiveMomentum → V} (hc : ContDiff ℝ (n+1) (Function.uncurry F)) :
    ContDiff ℝ n (fun z : ℝ × MassiveMomentum => fderiv ℝ (F z.1) z.2) := by
  have H : ContDiff ℝ (n+1) (Function.uncurry (fun (z : ℝ × MassiveMomentum) (q : MassiveMomentum) => F z.1 q)) :=
    hc.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  exact H.fderiv contDiff_snd le_rfl

/-- Joint C² regularity with a common compact support implies continuity of the
entire slice jet, including the two spatial derivatives in the test norm. -/
theorem compact_momentum_slices_tendsto (K : TopologicalSpace.Compacts MassiveMomentum)
    (F : ℝ → MassiveMomentum → ℂ) (hc : ContDiff ℝ 2 (Function.uncurry F))
    (hs : ∀ t q, q ∉ K → F t q = 0) (t : ℝ) :
    let j (v : ℝ) := CompactMomentumTest.ofFunction K (F v) (hc.comp (contDiff_const.prodMk contDiff_id)) (hs v)
    Tendsto j (𝓝 t) (𝓝 (j t)) := by
  intro j
  let D (v : ℝ) := fderiv ℝ (F v)
  let DD (v : ℝ) := fderiv ℝ (D v)
  have hd : ContDiff ℝ 1 (Function.uncurry D) := slice_fderiv_contDiff (n := 1) hc
  have hdd : ContDiff ℝ 0 (Function.uncurry DD) := slice_fderiv_contDiff (n := 0) hd
  have supp (v : ℝ) : tsupport (F v) ⊆ (K : Set MassiveMomentum) :=
    closure_minimal (fun q hq => by by_contra h; exact hq (hs v q h)) K.isCompact.isClosed
  have hD v q (hq : q ∉ K) : D v q = 0 := fderiv_of_notMem_tsupport ℝ (fun h => hq (supp v h))
  have hDD v q (hq : q ∉ K) : DD v q = 0 :=
    fderiv_of_notMem_tsupport ℝ (fun h => hq (supp v (tsupport_fderiv_subset ℝ h)))
  have h₀ : Tendsto (fun v => (j v).val.1) (𝓝 t) (𝓝 (j t).val.1) :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr (supported_family_uniform K F hc.continuous hs t)
  have h₁ : Tendsto (fun v => (j v).val.2.1) (𝓝 t) (𝓝 (j t).val.2.1) :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr (supported_family_uniform K D hd.continuous hD t)
  have h₂ : Tendsto (fun v => (j v).val.2.2) (𝓝 t) (𝓝 (j t).val.2.2) :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr (supported_family_uniform K DD hdd.continuous hDD t)
  exact tendsto_subtype_rng.mpr (h₀.prodMk_nhds (h₁.prodMk_nhds h₂))

/-- Along the common positive height a pointwise-convergent family can also be
tested on any family converging in the compact C² norm. -/
theorem compact_momentum_moving_test_limit (K : TopologicalSpace.Compacts MassiveMomentum)
    (L : Height → CompactMomentumTest K →L[ℂ] ℂ) (T : CompactMomentumTest K →L[ℂ] ℂ)
    (hL : ∀ f, Tendsto (fun h => L h f) poleBoundaryHeights (𝓝 (T f)))
    {g : Height → CompactMomentumTest K} {f : CompactMomentumTest K} (hg : Tendsto g poleBoundaryHeights (𝓝 f)) :
    Tendsto (fun h => L h (g h)) poleBoundaryHeights (𝓝 (T f)) := by
  apply tendsto_iff_seq_tendsto.mpr
  intro u hu
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun n => L (u n)) (fun x => by
    obtain ⟨B, hB⟩ := ((hL x).comp hu).norm.bddAbove_range
    exact ⟨B, fun n => hB (mem_range_self n)⟩)
  have hdiff : Tendsto (fun n => g (u n) - f) atTop (𝓝 0) := tendsto_sub_nhds_zero_iff.mpr (hg.comp hu)
  have hsmall : Tendsto (fun n => L (u n) (g (u n) - f)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ((L (u n)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _)))
    simpa using hdiff.norm.const_mul C
  simpa using hsmall.add ((hL f).comp hu)

end UV.SectorPlane
