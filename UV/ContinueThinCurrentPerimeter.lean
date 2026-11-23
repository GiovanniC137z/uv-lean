import UV.ContinueThinCurrentExpansion

/-! The perimeter limit after signed collinear subsegments have
been prepared. Distinct geometric pieces intersect in at most a point. -/

noncomputable section

open MeasureTheory Set Filter Bornology
open scoped BigOperators InnerProductSpace Topology ENNReal NNReal

namespace UV

/-- Remaining signed segments intersect in at most one point. The
hypothesis describes the result of splitting collinear overlaps. -/
def thinCurrentPrepared {ι : Type*} [Fintype ι] (edges : ι → ThinCurrentSegment) : Prop :=
  ∀ i j, i ≠ j →
    ((edges i).point '' Icc 0 (edges i).length ∩ (edges j).point '' Icc 0 (edges j).length).Subsingleton

def thinCurrentPerimeter {ι : Type*} [Fintype ι] (edges : ι → ThinCurrentSegment) : ℝ :=
  ∑ j, ((edges j).multiplicity : ℝ) ^ 2 * (edges j).length

theorem thinCurrentPerimeter_pos {ι : Type*} [Fintype ι]
    (edges : ι → ThinCurrentSegment)
    (nonzero : ∃ e, (edges e).multiplicity ≠ 0 ∧ 0 < (edges e).length) :
    0 < thinCurrentPerimeter edges := by
  obtain ⟨e, he, he'⟩ := nonzero
  apply lt_of_lt_of_le _ (Finset.single_le_sum
    (fun j _ => mul_nonneg (sq_nonneg ((edges j).multiplicity : ℝ)) (edges j).length_nonneg)
    (Finset.mem_univ e))
  exact mul_pos (sq_pos_iff.mpr (by exact_mod_cast he)) he'

private theorem thinCurrentSegment_point_injective (e : ThinCurrentSegment) :
    Function.Injective e.point := by
  intro s t h
  unfold ThinCurrentSegment.point at h
  have hh : (s - t) • e.tangent = 0 := by
    rw [sub_smul, add_left_cancel h, sub_self]
  have hn := congrArg norm hh
  rw [norm_smul, e.unit_tangent, mul_one, norm_zero, norm_eq_zero, sub_eq_zero] at hn
  exact hn

/-- A nonparallel crossing, or adjacent collinear pieces with disjoint
interiors, changes no perimeter term. This uses the actual path images
and ignores only sets of arclength measure zero. -/
theorem thinCurrentEdge_no_hit_ae (e e' : ThinCurrentSegment)
    (hprep : (e.point '' Icc 0 e.length ∩ e'.point '' Icc 0 e'.length).Subsingleton) :
    ∀ᵐ u ∂((volume : Measure ℝ).restrict (Ioo 0 e'.length)),
      thinEdgeResidual e e' u ≠ 0 ∨ -thinEdgeProjection e e' u < 0 ∨
        e.length < -thinEdgeProjection e e' u := by
  let bad := {u | e'.point u ∈ e.point '' Icc 0 e.length ∩ e'.point '' Icc 0 e'.length}
  have hbad : bad.Subsingleton := fun a ha b hb =>
    thinCurrentSegment_point_injective e' (hprep ha hb)
  have hnull : (volume : Measure ℝ).restrict (Ioo 0 e'.length) bad = 0 := hbad.measure_zero _
  have hbad_ae : ∀ᵐ u ∂((volume : Measure ℝ).restrict (Ioo 0 e'.length)), u ∉ bad := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using hnull
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioo :
    MeasurableSet (Ioo 0 e'.length)), hbad_ae] with u hu hgood
  by_contra! hhit
  apply hgood
  refine ⟨⟨-thinEdgeProjection e e' u, ⟨hhit.2.1, hhit.2.2⟩, ?_⟩,
    ⟨u, Ioo_subset_Icc_self hu, rfl⟩⟩
  have hoff := sub_eq_zero.mp hhit.1
  unfold ThinCurrentSegment.point
  rw [neg_smul, ← sub_eq_add_neg, ← hoff]
  unfold thinEdgeOffset
  abel
  rfl

/-- Exact shell asymptotic from the inverse transform's norm majorant
and line trace. The norm-one directions used in the trace are the
original arclength tangents. -/
theorem thinCurrentShell_perimeter_of_line_trace {ι : Type*} [Fintype ι]
    (edges : ι → ThinCurrentSegment) (hprep : thinCurrentPrepared edges)
    {φ : ThinCurrentPlane → ℝ} (hφ : Continuous φ) (hφI : Integrable φ)
    (hnn : ∀ p, 0 ≤ φ p)
    (hK : Continuous (thinWindowInverse φ))
    (hvanish : Tendsto (thinWindowInverse φ) (cobounded ThinCurrentPlane) (𝓝 0))
    {dom : ℝ → ℝ} (hdom : ∀ x z, |z| ≤ ‖x‖ → ‖thinWindowInverse φ x‖ ≤ dom z)
    (hi : Integrable dom) {c : ℝ}
    (htrace : ∀ v : ThinCurrentPlane, ‖v‖ = 1 → (∫ z : ℝ, thinWindowInverse φ (z • v)) = (c : ℂ)) :
    Tendsto (fun R : ℝ => (thinCurrentShell edges φ R).toReal / R^3) atTop
      (𝓝 (c * thinCurrentPerimeter edges)) := by
  classical
  let K := thinWindowInverse φ
  let g (j k : ι) := if j = k then ((edges j).length : ℂ) * c else 0
  have hpair (j k : ι) :
      Tendsto (thinEdgeNormalizedPair K (edges j) (edges k)) atTop (𝓝 (g j k)) := by
    by_cases he : j = k
    · subst k
      simp only [g, if_pos rfl]
      have h := thinEdgeNormalizedPair_tendsto_diagonal hK hdom hi (edges j)
      rw [htrace _ (edges j).unit_tangent, Complex.real_smul] at h
      exact h
    · simp only [g, if_neg he]
      exact thinEdgeNormalizedPair_tendsto_zero hK hvanish hdom hi _ _
        (thinCurrentEdge_no_hit_ae _ _ (hprep j k he))
  have hsum : Tendsto (fun R : ℝ =>
      ∑ j, ∑ k, (thinEdgePairWeight (edges j) (edges k) : ℂ) *
        thinEdgeNormalizedPair K (edges j) (edges k) R) atTop
      (𝓝 (∑ j, ∑ k, (thinEdgePairWeight (edges j) (edges k) : ℂ) * g j k)) := by
    apply tendsto_finset_sum
    intro j _
    apply tendsto_finset_sum
    intro k _
    exact (hpair j k).const_mul _
  have hlimit :
      (∑ j, ∑ k, (thinEdgePairWeight (edges j) (edges k) : ℂ) * g j k) =
        ((c * thinCurrentPerimeter edges : ℝ) : ℂ) := by
    simp only [thinCurrentPerimeter]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_eq_single j]
    · simp only [g, if_pos rfl, thinEdgePairWeight_self]
      push_cast
      ring
    · intro k _ hkj
      simp [g, Ne.symm hkj]
    · simp
  rw [hlimit] at hsum
  have h := Complex.continuous_re.continuousAt.tendsto.comp hsum
  simp only [Complex.ofReal_re] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact (thinCurrentShell_eq_pair_sum hφ hφI hnn edges hR).symm

/-- The perimeter asymptotic immediately rules out a finite quadratic
response for the same current and nonzero positive spectrum. -/
theorem thinCurrentResponse_eq_top_of_perimeter {ι : Type*} [Fintype ι]
    (edges : ι → ThinCurrentSegment) (φ : ThinCurrentPlane → ℝ) (ρ : Measure ℝ≥0)
    (hρ : ρ ≠ 0) {B c : ℝ} (hB : 0 ≤ B) (hupper : ∀ p, φ p ≤ B)
    (hsupport : ∀ p, φ p ≠ 0 → 1 < ‖p‖ ∧ ‖p‖ < 2) (hc : 0 < c)
    (nonzero : ∃ e, (edges e).multiplicity ≠ 0 ∧ 0 < (edges e).length)
    (hlim : Tendsto (fun R : ℝ => (thinCurrentShell edges φ R).toReal / R^3) atTop
      (𝓝 (c * thinCurrentPerimeter edges))) :
    thinCurrentResponse edges (thinCurrentSpectrum ρ) = ⊤ :=
  thinCurrentResponse_eq_top_of_shell_limit edges φ ρ hρ hB hupper hsupport
    (mul_pos hc (thinCurrentPerimeter_pos edges nonzero)) hlim

end UV
