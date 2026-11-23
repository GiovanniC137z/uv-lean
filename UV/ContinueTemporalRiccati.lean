import UV.ContinueTemporalTailAverage
import Mathlib.Topology.MetricSpace.Contracting

/-! Bounded positive solutions of the normal impedance equation. The
quadratic right hand side admits invariant constant barriers. Averaging
backwards gives a strict contraction between those barriers. -/

noncomputable section

namespace UV.TemporalRay

open Set
open scoped BoundedContinuousFunction NNReal

structure ImpedanceBounds where
  invA : ℝ → ℝ
  p : ℝ → ℝ
  continuous_invA : Continuous invA
  continuous_p : Continuous p
  invMin : ℝ
  invMax : ℝ
  lo : ℝ
  hi : ℝ
  invMin_pos : 0 < invMin
  inv_bounds : ∀ r, invMin ≤ invA r ∧ invA r ≤ invMax
  lo_pos : 0 < lo
  lo_le_hi : lo ≤ hi
  barriers : ∀ r, invA r * lo^2 ≤ p r ∧ p r ≤ invA r * hi^2

private def impedanceRate (B : ImpedanceBounds) : ℝ := 2*B.invMax*B.hi

private theorem impedance_rate_pos (B : ImpedanceBounds) : 0 < impedanceRate B := by
  have hi := B.lo_pos.trans_le B.lo_le_hi
  have ha := B.invMin_pos.trans_le ((B.inv_bounds 0).1.trans (B.inv_bounds 0).2)
  exact mul_pos (mul_pos zero_lt_two ha) hi

private def impedanceStep (B : ImpedanceBounds) (r x : ℝ) : ℝ :=
  x + (B.p r - B.invA r*x^2)/impedanceRate B

private theorem impedance_step_sub (B : ImpedanceBounds) (r x z : ℝ) :
    impedanceStep B r x - impedanceStep B r z =
      (x-z) * (1 - B.invA r*(x+z)/impedanceRate B) := by
  unfold impedanceStep
  ring

private def impedanceRatio (B : ImpedanceBounds) : ℝ :=
  1 - (2*B.invMin*B.lo)/impedanceRate B

private theorem impedance_slope_bounds (B : ImpedanceBounds) (r : ℝ)
    {x z : ℝ} (hx : x ∈ Icc B.lo B.hi) (hz : z ∈ Icc B.lo B.hi) :
    0 ≤ 1 - B.invA r*(x+z)/impedanceRate B ∧
      1 - B.invA r*(x+z)/impedanceRate B ≤ impedanceRatio B := by
  have ha := (B.inv_bounds r).1
  have ha' := (B.inv_bounds r).2
  have hsum := add_nonneg (B.lo_pos.le.trans hx.1) (B.lo_pos.le.trans hz.1)
  constructor
  · apply sub_nonneg.mpr
    apply (div_le_one (impedance_rate_pos B)).2
    calc
      _ ≤ B.invMax*(B.hi+B.hi) := mul_le_mul ha' (add_le_add hx.2 hz.2) hsum
        (B.invMin_pos.le.trans (ha.trans ha'))
      _ = impedanceRate B := by unfold impedanceRate; ring
  · apply sub_le_sub_left
    apply div_le_div_of_nonneg_right _ (impedance_rate_pos B).le
    calc
      _ = B.invMin*(B.lo+B.lo) := by ring
      _ ≤ _ := mul_le_mul ha (add_le_add hx.1 hz.1) (add_nonneg B.lo_pos.le B.lo_pos.le)
        (B.invMin_pos.le.trans ha)

private theorem impedance_step_mono (B : ImpedanceBounds) (r : ℝ) :
    MonotoneOn (impedanceStep B r) (Icc B.lo B.hi) := by
  intro x hx z hz hxz
  apply sub_nonneg.mp
  rw [impedance_step_sub]
  exact mul_nonneg (sub_nonneg.mpr hxz) (impedance_slope_bounds B r hz hx).1

private theorem impedance_step_mem (B : ImpedanceBounds) (r : ℝ)
    {x : ℝ} (hx : x ∈ Icc B.lo B.hi) : impedanceStep B r x ∈ Icc B.lo B.hi := by
  have hlo : B.lo ≤ impedanceStep B r B.lo := by
    exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (B.barriers r).1) (impedance_rate_pos B).le)
  have hhi : impedanceStep B r B.hi ≤ B.hi := by
    exact add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (B.barriers r).2)
      (impedance_rate_pos B).le)
  exact ⟨hlo.trans (impedance_step_mono B r (left_mem_Icc.mpr B.lo_le_hi) hx hx.1),
    (impedance_step_mono B r hx (right_mem_Icc.mpr B.lo_le_hi) hx.2).trans hhi⟩

private abbrev ImpedanceSection (B : ImpedanceBounds) := ℝ →ᵇ Icc B.lo B.hi

private def impedanceSource (B : ImpedanceBounds) (f : ImpedanceSection B) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun r => impedanceStep B r (f r)) (by
    unfold impedanceStep
    have hf : Continuous (fun r => (f r : ℝ)) := continuous_subtype_val.comp f.continuous
    exact hf.add ((B.continuous_p.sub (B.continuous_invA.mul (hf.pow 2))).div_const _))
    B.hi (fun r => by
      have h := impedance_step_mem B r (f r).property
      exact (Real.norm_of_nonneg (B.lo_pos.le.trans h.1)).trans_le h.2)

private theorem impedance_average_mem (B : ImpedanceBounds) (f : ImpedanceSection B) (r : ℝ) :
    normalTailAverage (impedanceRate B) (impedanceSource B f) r ∈ Icc B.lo B.hi := by
  constructor
  · rw [← normal_tail_average_const (impedance_rate_pos B) B.lo r]
    exact normal_tail_average_mono (impedance_rate_pos B)
      (fun s => (impedance_step_mem B s (f s).property).1) r
  · rw [← normal_tail_average_const (impedance_rate_pos B) B.hi r]
    exact normal_tail_average_mono (impedance_rate_pos B)
      (fun s => (impedance_step_mem B s (f s).property).2) r

private def impedanceAverage (B : ImpedanceBounds) (f : ImpedanceSection B) : ImpedanceSection B where
  toFun r := ⟨_, impedance_average_mem B f r⟩
  continuous_toFun := Continuous.subtype_mk (continuous_iff_continuousAt.mpr
    (fun r => (normal_tail_average_derivative (impedance_rate_pos B) (impedanceSource B f) r).continuousAt)) _
  map_bounded' := by
    refine ⟨B.hi-B.lo, fun r s => ?_⟩
    change |normalTailAverage _ _ r - normalTailAverage _ _ s| ≤ _
    have hr := impedance_average_mem B f r
    have hs := impedance_average_mem B f s
    exact abs_le.mpr ⟨by linarith only [hr.1,hs.2], by linarith only [hr.2,hs.1]⟩

private theorem impedance_ratio_nonneg (B : ImpedanceBounds) : 0 ≤ impedanceRatio B := by
  have h := impedance_slope_bounds B 0 (left_mem_Icc.mpr B.lo_le_hi) (left_mem_Icc.mpr B.lo_le_hi)
  exact h.1.trans h.2

private theorem impedance_contracting (B : ImpedanceBounds) :
    ContractingWith ⟨impedanceRatio B, impedance_ratio_nonneg B⟩ (impedanceAverage B) := by
  constructor
  · change 1 - 2*B.invMin*B.lo/impedanceRate B < 1
    have h := div_pos (mul_pos (mul_pos zero_lt_two B.invMin_pos) B.lo_pos) (impedance_rate_pos B)
    linarith
  · apply LipschitzWith.of_dist_le_mul
    intro f g
    apply BoundedContinuousFunction.dist_le_iff_of_nonempty.mpr
    intro r
    change |normalTailAverage _ (impedanceSource B f) r - normalTailAverage _ (impedanceSource B g) r|
      ≤ impedanceRatio B * dist f g
    apply normal_tail_average_dist (impedance_rate_pos B)
    intro s
    change |impedanceStep B s (f s) - impedanceStep B s (g s)| ≤ _
    rw [impedance_step_sub,abs_mul]
    have h := impedance_slope_bounds B s (f s).property (g s).property
    rw [abs_of_nonneg h.1, mul_comm]
    exact mul_le_mul h.2 (BoundedContinuousFunction.dist_coe_le_dist (f := f) (g := g) s) (abs_nonneg _)
      (impedance_ratio_nonneg B)

/-- Positive bounded impedance for the actual variable-coefficient equation.
The interval of barriers may collapse, as it does for constant coefficients. -/
theorem exists_normal_impedance (B : ImpedanceBounds) :
    ∃ q : ℝ → ℝ, Continuous q ∧ (∀ r, q r ∈ Icc B.lo B.hi) ∧
      ∀ r, HasDerivAt q (B.invA r*(q r)^2-B.p r) r := by
  letI : Nonempty (ImpedanceSection B) := ⟨BoundedContinuousFunction.const ℝ ⟨B.lo, left_mem_Icc.mpr B.lo_le_hi⟩⟩
  let f := (impedance_contracting B).fixedPoint (impedanceAverage B)
  have hf : impedanceAverage B f = f := (impedance_contracting B).fixedPoint_isFixedPt
  have he : normalTailAverage (impedanceRate B) (impedanceSource B f) = fun r => (f r : ℝ) := by
    funext r
    exact congrArg (fun g : ImpedanceSection B => (g r : ℝ)) hf
  refine ⟨fun r => (f r : ℝ), continuous_subtype_val.comp f.continuous, fun r => (f r).property, ?_⟩
  intro r
  have hd := normal_tail_average_derivative (impedance_rate_pos B) (impedanceSource B f) r
  rw [he] at hd
  convert hd using 1
  change B.invA r*(f r : ℝ)^2 - B.p r = impedanceRate B * ((f r : ℝ) - impedanceStep B r (f r))
  unfold impedanceStep
  field_simp [(impedance_rate_pos B).ne']
  ring

end UV.TemporalRay
