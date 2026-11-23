import Mathlib.MeasureTheory.Integral.Prod
import UV.ContinueThinCurrent
import Mathlib.Analysis.SpecificLimits.Normed

/-! The arclength change of coordinates for the ultraviolet perimeter.
Projection on the first unit tangent supplies a single integrable
majorant for diagonal, crossing, and disjoint edge pairs. -/

noncomputable section

open MeasureTheory Filter Set Bornology
open scoped Topology InnerProductSpace ENNReal BigOperators

namespace UV

def thinEdgeOffset (e e' : ThinCurrentSegment) (u : ℝ) : ThinCurrentPlane :=
  e.start - e'.point u

def thinEdgeProjection (e e' : ThinCurrentSegment) (u : ℝ) : ℝ :=
  inner ℝ e.tangent (thinEdgeOffset e e' u)

def thinEdgeResidual (e e' : ThinCurrentSegment) (u : ℝ) : ThinCurrentPlane :=
  thinEdgeOffset e e' u - thinEdgeProjection e e' u • e.tangent

theorem thinEdgeResidual_orthogonal (e e' : ThinCurrentSegment) (u : ℝ) :
    inner ℝ e.tangent (thinEdgeResidual e e' u) = 0 := by
  simp [thinEdgeResidual, thinEdgeProjection, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, e.unit_tangent]

private theorem thinEdgeChart_norm_lower (e e' : ThinCurrentSegment) (u R z : ℝ) :
    |z| ≤ ‖z • e.tangent + R • thinEdgeResidual e e' u‖ := by
  have h := abs_real_inner_le_norm e.tangent (z • e.tangent + R • thinEdgeResidual e e' u)
  simpa [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, e.unit_tangent,
    thinEdgeResidual_orthogonal] using h

/-- The change to the projected first arclength retains the actual edge
cutoff rather than integrating over its full supporting line. -/
def thinEdgeChart (K : ThinCurrentPlane → ℂ) (e e' : ThinCurrentSegment)
    (R u z : ℝ) : ℂ :=
  if z / R - thinEdgeProjection e e' u ∈ Ioo 0 e.length then
    K (z • e.tangent + R • thinEdgeResidual e e' u) else 0

/-- Per-unit-width expression after the first arclength substitution. -/
def thinEdgeNormalizedPair (K : ThinCurrentPlane → ℂ) (e e' : ThinCurrentSegment)
    (R : ℝ) : ℂ :=
  ∫ u in Ioo 0 e'.length, ∫ z : ℝ, thinEdgeChart K e e' R u z

private theorem thinEdgeChart_joint_measurable (K : ThinCurrentPlane → ℂ) (hK : Continuous K)
    (e e' : ThinCurrentSegment) (R : ℝ) :
    Measurable (fun p : ℝ × ℝ => thinEdgeChart K e e' R p.1 p.2) := by
  have hp : Continuous (thinEdgeProjection e e') := by
    unfold thinEdgeProjection thinEdgeOffset ThinCurrentSegment.point
    fun_prop
  have hr : Continuous (thinEdgeResidual e e') := by
    unfold thinEdgeResidual thinEdgeOffset ThinCurrentSegment.point
    fun_prop
  let A := (fun p : ℝ × ℝ => p.2 / R - thinEdgeProjection e e' p.1) ⁻¹' Ioo 0 e.length
  have hA : MeasurableSet A := measurableSet_Ioo.preimage
    ((continuous_snd.div_const R).sub (hp.comp continuous_fst)).measurable
  have hC : Continuous (fun p : ℝ × ℝ => K
      (p.2 • e.tangent + R • thinEdgeResidual e e' p.1)) := by fun_prop
  have hfun : (fun p : ℝ × ℝ => thinEdgeChart K e e' R p.1 p.2) =
      A.indicator (fun p => K (p.2 • e.tangent + R • thinEdgeResidual e e' p.1)) := by
    funext p
    by_cases hp : p ∈ A
    · have hs : p.2 / R - thinEdgeProjection e e' p.1 ∈ Ioo 0 e.length := hp
      rw [Set.indicator_of_mem hp, thinEdgeChart, if_pos hs]
    · have hs : p.2 / R - thinEdgeProjection e e' p.1 ∉ Ioo 0 e.length := hp
      rw [Set.indicator_of_notMem hp, thinEdgeChart, if_neg hs]
  rw [hfun]
  exact hC.measurable.indicator hA

/-- Exact Lebesgue arclength change in the actual edge-pair term. -/
theorem thinEdgeNormalizedPair_eq (K : ThinCurrentPlane → ℂ)
    (e e' : ThinCurrentSegment) {R : ℝ} (hR : 0 < R) :
    thinEdgeNormalizedPair K e e' R =
      R • ∫ u in Ioo 0 e'.length, ∫ s in Ioo 0 e.length,
        K (R • (e.point s - e'.point u)) := by
  unfold thinEdgeNormalizedPair
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with u
  let a := thinEdgeProjection e e' u
  let r := thinEdgeResidual e e' u
  let F : ℝ → ℂ := fun z => K (z • e.tangent + R • r)
  have hset (z : ℝ) : z / R - a ∈ Ioo 0 e.length ↔
      z ∈ Ioo (R * a) (R * e.length + R * a) := by
    simp only [mem_Ioo, lt_sub_iff_add_lt, zero_add, sub_lt_iff_lt_add, lt_div_iff₀ hR, div_lt_iff₀ hR]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hfun (s : ℝ) : K (R • (e.point s - e'.point u)) = F (R * s + R * a) := by
    have he : e.point s - e'.point u = s • e.tangent + thinEdgeOffset e e' u := by
      unfold thinEdgeOffset ThinCurrentSegment.point
      abel
    change K (R • (e.point s - e'.point u)) =
      K ((R * s + R * a) • e.tangent + R • r)
    rw [he, smul_add, smul_smul, add_smul]
    dsimp only [r, thinEdgeResidual, a]
    rw [smul_sub, smul_smul]
    congr 1
    abel
  calc
    _ = ∫ z in Ioo (R * a) (R * e.length + R * a), F z := by
      rw [← integral_indicator measurableSet_Ioo]
      exact integral_congr_ae (Eventually.of_forall fun z => by
        change (if z / R - a ∈ Ioo 0 e.length then F z else 0) = _
        by_cases hz : z / R - a ∈ Ioo 0 e.length
        · rw [if_pos hz, Set.indicator_of_mem ((hset z).mp hz)]
        · rw [if_neg hz, Set.indicator_of_notMem (fun hm => hz ((hset z).mpr hm))])
    _ = ∫ z in (R * 0 + R * a)..(R * e.length + R * a), F z := by
      rw [intervalIntegral.integral_of_le (by
        have := mul_nonneg hR.le e.length_nonneg
        linarith), integral_Ioc_eq_integral_Ioo]
      simp
    _ = R • ∫ s in (0 : ℝ)..e.length, F (R * s + R * a) :=
      (intervalIntegral.smul_integral_comp_mul_add F R (R * a)).symm
    _ = _ := by
      rw [intervalIntegral.integral_of_le e.length_nonneg, integral_Ioc_eq_integral_Ioo]
      simp_rw [← hfun]

private theorem thinEdgeChart_norm_bound {K : ThinCurrentPlane → ℂ} {dom : ℝ → ℝ}
    (hdom : ∀ x z, |z| ≤ ‖x‖ → ‖K x‖ ≤ dom z) (e e' : ThinCurrentSegment)
    (R u z : ℝ) :
    ‖thinEdgeChart K e e' R u z‖ ≤ dom z := by
  have hb := hdom _ _ (thinEdgeChart_norm_lower e e' u R z)
  unfold thinEdgeChart
  split
  · exact hb
  · rw [norm_zero]
    exact (norm_nonneg _).trans hb

private theorem thinEdgeChart_inner_integrable {K : ThinCurrentPlane → ℂ}
    (hK : Continuous K) {dom : ℝ → ℝ} (hdom : ∀ x z, |z| ≤ ‖x‖ → ‖K x‖ ≤ dom z)
    (hi : Integrable dom) (e e' : ThinCurrentSegment) (R u : ℝ) :
    Integrable (thinEdgeChart K e e' R u) := by
  have hm : Measurable (fun z : ℝ => (u,z)) := measurable_const.prodMk measurable_id
  exact hi.mono' ((thinEdgeChart_joint_measurable K hK e e' R).comp hm).aestronglyMeasurable
    (Eventually.of_forall (thinEdgeChart_norm_bound hdom e e' R u))

private theorem thinEdgeChart_integral_bound {K : ThinCurrentPlane → ℂ}
    {dom : ℝ → ℝ} (hdom : ∀ x z, |z| ≤ ‖x‖ → ‖K x‖ ≤ dom z)
    (hi : Integrable dom) (e e' : ThinCurrentSegment) (R u : ℝ) :
    ‖∫ z : ℝ, thinEdgeChart K e e' R u z‖ ≤ ∫ z : ℝ, dom z :=
  norm_integral_le_of_norm_le hi (Eventually.of_forall (thinEdgeChart_norm_bound hdom e e' R u))

private theorem thinEdgeChart_integral_measurable {K : ThinCurrentPlane → ℂ}
    (hK : Continuous K) (e e' : ThinCurrentSegment) (R : ℝ) :
    Measurable (fun u : ℝ => ∫ z : ℝ, thinEdgeChart K e e' R u z) :=
  (thinEdgeChart_joint_measurable K hK e e' R).stronglyMeasurable.integral_prod_right'.measurable

private theorem thinDiv_tendsto (z : ℝ) :
    Tendsto (fun R : ℝ => z / R) atTop (𝓝 0) := by
  simpa only [div_eq_mul_inv, mul_zero] using
    (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0)).const_mul z

private theorem thinEdgeChart_tendsto_no_hit {K : ThinCurrentPlane → ℂ}
    (hvanish : Tendsto K (cobounded ThinCurrentPlane) (𝓝 0))
    (e e' : ThinCurrentSegment) (u z : ℝ)
    (hout : thinEdgeResidual e e' u ≠ 0 ∨ -thinEdgeProjection e e' u < 0 ∨
      e.length < -thinEdgeProjection e e' u) :
    Tendsto (fun R : ℝ => thinEdgeChart K e e' R u z) atTop (𝓝 0) := by
  rcases hout with hperp | hlow | hhigh
  · let r := thinEdgeResidual e e' u
    let v := z • e.tangent
    have hr : 0 < ‖r‖ := norm_pos_iff.mpr hperp
    have ht : Tendsto (fun R : ℝ => v + R • r) atTop (cobounded ThinCurrentPlane) := by
      rw [← tendsto_norm_atTop_iff_cobounded]
      apply tendsto_atTop.mpr
      intro b
      filter_upwards [eventually_ge_atTop (max 0 ((b + ‖v‖) / ‖r‖))] with R hR
      have hp := (le_max_left _ _).trans hR
      have hbound := (div_le_iff₀ hr).mp ((le_max_right _ _).trans hR)
      have htri : ‖R • r‖ ≤ ‖v + R • r‖ + ‖v‖ := by
        calc
          _ = ‖(v + R • r) - v‖ := by rw [add_sub_cancel_left]
          _ ≤ _ := norm_sub_le _ _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp] at htri
      linarith
    have hk := hvanish.comp ht
    have hkn : Tendsto (fun R : ℝ => ‖K (v + R • r)‖) atTop (𝓝 0) := by
      simpa only [norm_zero] using hk.norm
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero (fun R : ℝ => norm_nonneg (thinEdgeChart K e e' R u z)) ?_ hkn
    intro R
    unfold thinEdgeChart
    split
    · exact le_rfl
    · simp
  · have hdiv : Tendsto (fun R : ℝ => z / R - thinEdgeProjection e e' u) atTop
        (𝓝 (-thinEdgeProjection e e' u)) := by
      simpa only [zero_sub] using (thinDiv_tendsto z).sub_const
        (thinEdgeProjection e e' u)
    apply tendsto_const_nhds.congr'
    filter_upwards [hdiv (Iio_mem_nhds hlow)] with R hR
    have hn : z / R - thinEdgeProjection e e' u ∉ Ioo 0 e.length := fun hm =>
      not_lt_of_ge hm.1.le hR
    simp [thinEdgeChart, hn]
  · have hdiv : Tendsto (fun R : ℝ => z / R - thinEdgeProjection e e' u) atTop
        (𝓝 (-thinEdgeProjection e e' u)) := by
      simpa only [zero_sub] using (thinDiv_tendsto z).sub_const
        (thinEdgeProjection e e' u)
    apply tendsto_const_nhds.congr'
    filter_upwards [hdiv (Ioi_mem_nhds hhigh)] with R hR
    have hn : z / R - thinEdgeProjection e e' u ∉ Ioo 0 e.length := fun hm =>
      not_lt_of_ge hm.2.le hR
    simp [thinEdgeChart, hn]

/-- A distinct pair gives no perimeter term when its second arclength
almost never lies on the first closed segment. This is enough for the
two asymptotic contributions adjacent to an intersection or endpoint. -/
theorem thinEdgeNormalizedPair_tendsto_zero {K : ThinCurrentPlane → ℂ} (hK : Continuous K)
    (hvanish : Tendsto K (cobounded ThinCurrentPlane) (𝓝 0))
    {dom : ℝ → ℝ} (hdom : ∀ x z, |z| ≤ ‖x‖ → ‖K x‖ ≤ dom z)
    (hi : Integrable dom) (e e' : ThinCurrentSegment)
    (hout : ∀ᵐ u ∂(volume.restrict (Ioo 0 e'.length)),
      thinEdgeResidual e e' u ≠ 0 ∨ -thinEdgeProjection e e' u < 0 ∨
        e.length < -thinEdgeProjection e e' u) :
    Tendsto (thinEdgeNormalizedPair K e e') atTop (𝓝 0) := by
  haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo 0 e'.length)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure ℝ).restrict (Ioo 0 e'.length)) (l := atTop)
    (F := fun R u => ∫ z : ℝ, thinEdgeChart K e e' R u z) (f := fun _ => (0 : ℂ))
    (fun _ => ∫ z : ℝ, dom z)
    (Eventually.of_forall fun R => (thinEdgeChart_integral_measurable hK e e' R).aestronglyMeasurable)
    (Eventually.of_forall fun R => Eventually.of_forall (thinEdgeChart_integral_bound hdom hi e e' R))
    (integrable_const _) ?_
  · simpa only [integral_zero, thinEdgeNormalizedPair] using hlim
  · filter_upwards [hout] with u hu
    have hz := tendsto_integral_filter_of_dominated_convergence
      (F := fun R => thinEdgeChart K e e' R u) (f := fun _ => (0 : ℂ)) dom
      (Eventually.of_forall fun R => (thinEdgeChart_inner_integrable hK hdom hi e e' R u).aestronglyMeasurable)
      (Eventually.of_forall fun R => Eventually.of_forall (thinEdgeChart_norm_bound hdom e e' R u))
      hi (Eventually.of_forall fun z => thinEdgeChart_tendsto_no_hit hvanish e e' u z hu)
    simpa only [integral_zero] using hz

private theorem thinDiagonal_projection (e : ThinCurrentSegment) (u : ℝ) :
    thinEdgeProjection e e u = -u ∧ thinEdgeResidual e e u = 0 := by
  have hoff : thinEdgeOffset e e u = (-u) • e.tangent := by
    unfold thinEdgeOffset ThinCurrentSegment.point
    rw [neg_smul]
    abel
  have hp : thinEdgeProjection e e u = -u := by
    simp [thinEdgeProjection, hoff, real_inner_smul_right, real_inner_self_eq_norm_sq, e.unit_tangent]
  exact ⟨hp, by simp [thinEdgeResidual, hoff, hp]⟩

/-- The actual diagonal arclength term tends to the segment length
times the integral of the kernel along its original unit tangent. -/
theorem thinEdgeNormalizedPair_tendsto_diagonal {K : ThinCurrentPlane → ℂ} (hK : Continuous K)
    {dom : ℝ → ℝ} (hdom : ∀ x z, |z| ≤ ‖x‖ → ‖K x‖ ≤ dom z)
    (hi : Integrable dom) (e : ThinCurrentSegment) :
    Tendsto (thinEdgeNormalizedPair K e e) atTop
      (𝓝 (e.length • ∫ z : ℝ, K (z • e.tangent))) := by
  haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo 0 e.length)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure ℝ).restrict (Ioo 0 e.length)) (l := atTop)
    (F := fun R u => ∫ z : ℝ, thinEdgeChart K e e R u z)
    (f := fun _ => (∫ z : ℝ, K (z • e.tangent))) (fun _ => ∫ z : ℝ, dom z)
    (Eventually.of_forall fun R => (thinEdgeChart_integral_measurable hK e e R).aestronglyMeasurable)
    (Eventually.of_forall fun R => Eventually.of_forall (thinEdgeChart_integral_bound hdom hi e e R))
    (integrable_const _) ?_
  · rw [integral_const, measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
      ENNReal.toReal_ofReal e.length_nonneg] at hlim
    exact hlim
  · filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo] with u hu
    apply tendsto_integral_filter_of_dominated_convergence
      (F := fun R => thinEdgeChart K e e R u) (f := fun z => K (z • e.tangent)) dom
      (Eventually.of_forall fun R => (thinEdgeChart_inner_integrable hK hdom hi e e R u).aestronglyMeasurable)
      (Eventually.of_forall fun R => Eventually.of_forall (thinEdgeChart_norm_bound hdom e e R u))
      hi
    refine Eventually.of_forall fun z => ?_
    have hdiv : Tendsto (fun R : ℝ => z / R - thinEdgeProjection e e u) atTop (𝓝 u) := by
      simpa only [(thinDiagonal_projection e u).1, zero_sub, neg_neg] using
        (thinDiv_tendsto z).sub_const (thinEdgeProjection e e u)
    apply tendsto_const_nhds.congr'
    filter_upwards [hdiv (Ioo_mem_nhds hu.1 hu.2)] with R hR
    have hR' : z / R - thinEdgeProjection e e u ∈ Ioo 0 e.length := hR
    rw [thinEdgeChart, if_pos hR', (thinDiagonal_projection e u).2, smul_zero, add_zero]

end UV
