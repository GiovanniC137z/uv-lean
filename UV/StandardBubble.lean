import UV.Holomorphy
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Tactic

noncomputable section
open MeasureTheory Set Complex
open scoped Topology

namespace UV

def bubbleCutDomain (m : ℝ) : Set ℂ := {z | z.re < 4 * m ^ 2 ∨ z.im ≠ 0}

def bubbleFeynmanWeight (x : ℝ) : ℝ := x * (1 - x)

def standardBubbleLog (m : ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  Complex.log ((m ^ 2 : ℝ) : ℂ) -
    Complex.log (((m ^ 2 : ℝ) : ℂ) - (bubbleFeynmanWeight x : ℂ) * z)

def standardBubble (m : ℝ) (z : ℂ) : ℂ :=
  ((16 * Real.pi ^ 2 : ℝ) : ℂ)⁻¹ * ∫ x in Icc (0 : ℝ) 1, standardBubbleLog m z x

theorem bubbleFeynmanWeight_bounds {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ bubbleFeynmanWeight x ∧ bubbleFeynmanWeight x ≤ 1 / 4 := by
  unfold bubbleFeynmanWeight
  constructor
  · exact mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  · nlinarith [sq_nonneg (x - 1 / 2)]

theorem bubbleCutDomain_open (m : ℝ) : IsOpen (bubbleCutDomain m) :=
  (isOpen_lt Complex.continuous_re continuous_const).union
    (isOpen_ne_fun Complex.continuous_im continuous_const)

theorem bubbleCutDomain_zero {m : ℝ} (hm : 0 < m) : (0 : ℂ) ∈ bubbleCutDomain m := by
  left
  simp only [Complex.zero_re]
  positivity

theorem bubbleCutDomain_preconnected {m : ℝ} (hm : 0 < m) :
    IsPreconnected (bubbleCutDomain m) := by
  have hstar : StarConvex ℝ (0 : ℂ) (bubbleCutDomain m) := by
    intro z hz a b ha hb hab
    simp only [smul_zero, zero_add]
    change (b • z).re < 4 * m ^ 2 ∨ (b • z).im ≠ 0
    simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul]
    rcases hz with hz | hz
    · left
      by_cases hre : 0 ≤ z.re
      · have hb1 : b ≤ 1 := by linarith
        nlinarith [mul_le_mul_of_nonneg_right hb1 hre]
      · have hh := mul_nonpos_of_nonneg_of_nonpos hb (le_of_not_ge hre)
        nlinarith [sq_pos_of_pos hm]
    · by_cases hb0 : b = 0
      · left
        rw [hb0, zero_mul]
        positivity
      · right
        exact mul_ne_zero hb0 hz
  exact (hstar.isPathConnected (bubbleCutDomain_zero hm)).isConnected.isPreconnected

theorem bubble_denominator_slit {m x : ℝ} (hm : 0 < m) (hx : x ∈ Icc (0 : ℝ) 1)
    {z : ℂ} (hz : z ∈ bubbleCutDomain m) :
    ((m ^ 2 : ℝ) : ℂ) - (bubbleFeynmanWeight x : ℂ) * z ∈ Complex.slitPlane := by
  obtain ⟨hc0, hc1⟩ := bubbleFeynmanWeight_bounds hx
  apply Complex.mem_slitPlane_iff.mpr
  rcases hz with hz | hz
  · left
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    by_cases hre : 0 ≤ z.re
    · nlinarith [mul_le_mul_of_nonneg_right hc1 hre, sq_pos_of_pos hm]
    · have hh := mul_nonpos_of_nonneg_of_nonpos hc0 (le_of_not_ge hre)
      nlinarith [sq_pos_of_pos hm]
  · by_cases hc : bubbleFeynmanWeight x = 0
    · left
      simp only [hc, Complex.ofReal_zero, zero_mul, sub_zero, Complex.ofReal_re]
      positivity
    · right
      simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_mul, add_zero, zero_sub]
      exact neg_ne_zero.mpr (mul_ne_zero hc hz)

theorem standardBubbleLog_ratio {m x : ℝ} (hm : 0 < m) (hx : x ∈ Icc (0 : ℝ) 1)
    {z : ℂ} (hz : z ∈ bubbleCutDomain m) :
    standardBubbleLog m z x = Complex.log (((m ^ 2 : ℝ) : ℂ) /
      (((m ^ 2 : ℝ) : ℂ) - (bubbleFeynmanWeight x : ℂ) * z)) := by
  have hd := bubble_denominator_slit hm hx hz
  unfold standardBubbleLog
  rw [div_eq_mul_inv, Complex.log_ofReal_mul (sq_pos_of_pos hm)
    (inv_ne_zero (Complex.slitPlane_ne_zero hd)),
    Complex.log_inv _ (Complex.slitPlane_arg_ne_pi hd),
    ← Complex.ofReal_log (sq_nonneg m)]
  ring

theorem standardBubble_ratio_integral {m : ℝ} (hm : 0 < m) {z : ℂ}
    (hz : z ∈ bubbleCutDomain m) :
    standardBubble m z = ((16 * Real.pi ^ 2 : ℝ) : ℂ)⁻¹ *
      ∫ x in Icc (0 : ℝ) 1, Complex.log (((m ^ 2 : ℝ) : ℂ) /
        (((m ^ 2 : ℝ) : ℂ) - (bubbleFeynmanWeight x : ℂ) * z)) := by
  unfold standardBubble
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  exact standardBubbleLog_ratio hm hx hz

theorem standardBubbleLog_differentiableOn {m x : ℝ}
    (hm : 0 < m) (hx : x ∈ Icc (0 : ℝ) 1) :
    DifferentiableOn ℂ (fun z => standardBubbleLog m z x) (bubbleCutDomain m) := by
  intro z hz
  have hden : DifferentiableAt ℂ (fun w : ℂ =>
      ((m ^ 2 : ℝ) : ℂ) - (bubbleFeynmanWeight x : ℂ) * w) z :=
    (differentiableAt_id.const_mul _).const_sub _
  exact (((Complex.differentiableAt_log (bubble_denominator_slit hm hx hz)).comp z hden).const_sub
    (Complex.log ((m ^ 2 : ℝ) : ℂ))).differentiableWithinAt

theorem standardBubbleLog_continuousOn {m : ℝ} (hm : 0 < m) {K : Set ℂ}
    (hK : K ⊆ bubbleCutDomain m) :
    ContinuousOn (fun p : ℂ × ℝ => standardBubbleLog m p.1 p.2) (K ×ˢ Icc 0 1) := by
  intro p hp
  have harg : ContinuousAt (fun q : ℂ × ℝ =>
      ((m ^ 2 : ℝ) : ℂ) - (bubbleFeynmanWeight q.2 : ℂ) * q.1) p := by
    unfold bubbleFeynmanWeight
    fun_prop
  have hlog : ContinuousAt (fun q : ℂ × ℝ => Complex.log
      (((m ^ 2 : ℝ) : ℂ) - (bubbleFeynmanWeight q.2 : ℂ) * q.1)) p :=
    (Complex.differentiableAt_log (bubble_denominator_slit hm hp.2 (hK hp.1))).continuousAt.comp
      (f := fun q : ℂ × ℝ => ((m ^ 2 : ℝ) : ℂ) - (bubbleFeynmanWeight q.2 : ℂ) * q.1) harg
  exact continuousWithinAt_const.sub hlog.continuousWithinAt

theorem standardBubble_holomorphic {m : ℝ} (hm : 0 < m) :
    AnalyticOnNhd ℂ (standardBubble m) (bubbleCutDomain m) := by
  have hi : DifferentiableOn ℂ (fun z => ∫ x in Icc (0 : ℝ) 1, standardBubbleLog m z x)
      (bubbleCutDomain m) := by
    apply holomorphy_from_compact_graph_majorants (bubbleCutDomain_open m)
    · intro z _
      apply Measurable.aestronglyMeasurable
      unfold standardBubbleLog bubbleFeynmanWeight
      exact measurable_const.sub (Complex.measurable_log.comp (by fun_prop))
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact standardBubbleLog_differentiableOn hm hx
    · intro K hK hsub
      obtain ⟨B, hB⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn
        (standardBubbleLog_continuousOn hm hsub)
      refine ⟨fun _ => max 0 B, integrable_const _, ?_⟩
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      intro z hz
      exact (hB (z, x) ⟨hz, hx⟩).trans (le_max_right _ _)
  apply DifferentiableOn.analyticOnNhd _ (bubbleCutDomain_open m)
  intro z hz
  exact (hi z hz).const_mul _

theorem standardBubbleLog_real_euclidean {m w x : ℝ} (hm : 0 < m)
    (hw : 0 ≤ w) (hx : x ∈ Icc (0 : ℝ) 1) :
    standardBubbleLog m (-(w : ℂ)) x =
      -(Real.log (1 + bubbleFeynmanWeight x * w / m ^ 2) : ℝ) := by
  have hc := (bubbleFeynmanWeight_bounds hx).1
  have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
  have hd : 0 < m ^ 2 + bubbleFeynmanWeight x * w := by positivity
  have hden : ((m ^ 2 : ℝ) : ℂ) - (bubbleFeynmanWeight x : ℂ) * (-(w : ℂ)) =
      ((m ^ 2 + bubbleFeynmanWeight x * w : ℝ) : ℂ) := by push_cast; ring
  have hfrac : (m ^ 2 + bubbleFeynmanWeight x * w) / m ^ 2 =
      1 + bubbleFeynmanWeight x * w / m ^ 2 := by field_simp
  have he : Real.log (m ^ 2) - Real.log (m ^ 2 + bubbleFeynmanWeight x * w) =
      -Real.log (1 + bubbleFeynmanWeight x * w / m ^ 2) := by
    rw [← hfrac, Real.log_div hd.ne' hm2.ne']
    ring
  unfold standardBubbleLog
  rw [hden, ← Complex.ofReal_log hm2.le, ← Complex.ofReal_log hd.le]
  exact_mod_cast he

theorem standardBubble_real_euclidean {m w : ℝ} (hm : 0 < m) (hw : 0 ≤ w) :
    standardBubble m (-(w : ℂ)) =
      -(((16 * Real.pi ^ 2)⁻¹ * ∫ x in Icc (0 : ℝ) 1,
        Real.log (1 + bubbleFeynmanWeight x * w / m ^ 2) : ℝ) : ℂ) := by
  have hi : (∫ x in Icc (0 : ℝ) 1, standardBubbleLog m (-(w : ℂ)) x) =
      -((∫ x in Icc (0 : ℝ) 1, Real.log (1 + bubbleFeynmanWeight x * w / m ^ 2) : ℝ) : ℂ) := by
    have hc : (∫ x in Icc (0 : ℝ) 1,
        ((Real.log (1 + bubbleFeynmanWeight x * w / m ^ 2) : ℝ) : ℂ)) =
        ((∫ x in Icc (0 : ℝ) 1, Real.log (1 + bubbleFeynmanWeight x * w / m ^ 2) : ℝ) : ℂ) :=
      integral_complex_ofReal
    rw [← hc, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    exact standardBubbleLog_real_euclidean hm hw hx
  unfold standardBubble
  rw [hi]
  push_cast
  ring

theorem standardBubble_zero (m : ℝ) : standardBubble m 0 = 0 := by
  simp [standardBubble, standardBubbleLog]

/-- Analytic continuation from the actual nonpositive Euclidean invariant
axis is unique throughout the admitted cut plane. -/
theorem bubble_cut_continuation_unique {m : ℝ} (hm : 0 < m) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (bubbleCutDomain m))
    (hg : AnalyticOnNhd ℂ g (bubbleCutDomain m))
    (he : ∀ w : ℝ, 0 ≤ w → f (-(w : ℂ)) = g (-(w : ℂ))) :
    EqOn f g (bubbleCutDomain m) := by
  let u (n : ℕ) : ℂ := -((1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have ht : Filter.Tendsto u Filter.atTop (𝓝 (0 : ℂ)) := by
    simpa only [Complex.ofReal_zero, neg_zero] using
      (Complex.continuous_ofReal.continuousAt.tendsto.comp
        tendsto_one_div_add_atTop_nhds_zero_nat).neg
  have hmem (n : ℕ) : u n ∈ {z : ℂ | f z = g z} \ {(0 : ℂ)} := by
    refine ⟨he _ (by positivity), ?_⟩
    simp only [mem_singleton_iff]
    exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity)))
  exact hf.eqOn_of_preconnected_of_mem_closure hg (bubbleCutDomain_preconnected hm)
    (bubbleCutDomain_zero hm) (mem_closure_of_tendsto ht (Filter.Eventually.of_forall hmem))

end UV
