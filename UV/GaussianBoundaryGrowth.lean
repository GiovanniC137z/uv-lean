import UV.GaussianDecomposition
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.Polynomial.Basic

/-! The genuine upper-rim logarithmic boundary, and its growth compared with
the entire Gaussian remainder. The logarithmic singularities are integrated
before taking the boundary limit. -/

noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology ENNReal

namespace UV

def standardBubbleRealDenominator (m s x : ℝ) : ℝ := m ^ 2 - bubbleFeynmanWeight x * s

def standardBubbleUpperLog (m s x : ℝ) : ℂ :=
  ((Real.log (m ^ 2) - Real.log (standardBubbleRealDenominator m s x) : ℝ) : ℂ) +
    if standardBubbleRealDenominator m s x < 0 then (Real.pi : ℂ) * Complex.I else 0

def standardBubbleUpperBoundary (m s : ℝ) : ℂ :=
  ((16 * Real.pi ^ 2 : ℝ) : ℂ)⁻¹ * ∫ x in Icc (0 : ℝ) 1, standardBubbleUpperLog m s x

theorem standard_bubble_real_denominator_nonzero_ae {m : ℝ} (hm : 0 < m) (s : ℝ) :
    ∀ᵐ x : ℝ, standardBubbleRealDenominator m s x ≠ 0 := by
  let p : Polynomial ℝ := Polynomial.C (m ^ 2) - Polynomial.C s *
    (Polynomial.X * (1 - Polynomial.X))
  have hp : p ≠ 0 := by
    intro h
    have h0 := congrArg (Polynomial.eval (0 : ℝ)) h
    simp only [p, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_one, mul_zero, zero_mul, sub_zero, Polynomial.eval_zero] at h0
    exact (sq_pos_of_pos hm).ne' h0
  have heval (x : ℝ) : p.eval x = standardBubbleRealDenominator m s x := by
    simp only [p, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_one, standardBubbleRealDenominator, bubbleFeynmanWeight]
    ring
  have hfinite : Set.Finite {x : ℝ | standardBubbleRealDenominator m s x = 0} :=
    (Polynomial.finite_setOf_isRoot hp).subset (fun x hx => by
      change p.eval x = 0
      rw [heval]
      exact hx)
  rw [ae_iff]
  simpa only [not_ne_iff] using hfinite.measure_zero (μ := volume)

theorem standard_bubble_denominator_log_integrable (m s : ℝ) :
    IntegrableOn (fun x => |Real.log (standardBubbleRealDenominator m s x)|) (Icc (0 : ℝ) 1) := by
  have ha : AnalyticOnNhd ℝ (standardBubbleRealDenominator m s) (uIcc (0 : ℝ) 1) := by
    unfold standardBubbleRealDenominator bubbleFeynmanWeight
    exact analyticOnNhd_const.sub ((analyticOnNhd_id.mul (analyticOnNhd_const.sub analyticOnNhd_id)).mul analyticOnNhd_const)
  have hi := intervalIntegrable_log_norm_meromorphicOn ha.meromorphicOn
  have hlog : IntervalIntegrable (fun x => Real.log (standardBubbleRealDenominator m s x)) volume 0 1 := by
    simpa only [Function.comp_apply, Real.norm_eq_abs, Real.log_abs] using hi
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hlog.abs

theorem complex_log_norm_bound_between {z : ℂ} {L U : ℝ} (hL : 0 < L)
    (hlower : L ≤ ‖z‖) (hupper : ‖z‖ ≤ U) :
    ‖Complex.log z‖ ≤ |Real.log L| + |Real.log U| + Real.pi := by
  have hz : 0 < ‖z‖ := hL.trans_le hlower
  have hlo := Real.log_le_log hL hlower
  have hhi := Real.log_le_log hz hupper
  have habs : |Real.log ‖z‖| ≤ |Real.log L| + |Real.log U| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_le_abs (Real.log L), abs_nonneg (Real.log U)]
    · linarith [le_abs_self (Real.log U), abs_nonneg (Real.log L)]
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by
    rw [Complex.log_re, Complex.log_im]
    exact add_le_add habs (Complex.abs_arg_le_pi _))

theorem standard_bubble_boundary_denominator_bounds {m s η x : ℝ}
    (hs : 0 ≤ s) (hη : η ∈ Ioc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    |standardBubbleRealDenominator m s x| ≤
      ‖((m ^ 2 : ℝ) : ℂ) - (bubbleFeynmanWeight x : ℂ) * ((s : ℂ) + (η : ℂ) * Complex.I)‖ ∧
    ‖((m ^ 2 : ℝ) : ℂ) - (bubbleFeynmanWeight x : ℂ) * ((s : ℂ) + (η : ℂ) * Complex.I)‖ ≤ m ^ 2 + s + 1 := by
  obtain ⟨hc0, hc4⟩ := bubbleFeynmanWeight_bounds hx
  have hc1 : bubbleFeynmanWeight x ≤ 1 := by linarith
  constructor
  · convert Complex.abs_re_le_norm
      (((m ^ 2 : ℝ) : ℂ) - (bubbleFeynmanWeight x : ℂ) * ((s : ℂ) + (η : ℂ) * Complex.I)) using 1
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.add_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      standardBubbleRealDenominator]
  · calc
      _ ≤ ‖((m ^ 2 : ℝ) : ℂ)‖ + ‖(bubbleFeynmanWeight x : ℂ) * ((s : ℂ) + (η : ℂ) * Complex.I)‖ := norm_sub_le _ _
      _ = m ^ 2 + bubbleFeynmanWeight x * ‖(s : ℂ) + (η : ℂ) * Complex.I‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0,
          Real.norm_of_nonneg (sq_nonneg m)]
      _ ≤ m ^ 2 + bubbleFeynmanWeight x * (s + η) := by
        apply add_le_add_left
        apply mul_le_mul_of_nonneg_left _ hc0
        calc
          _ ≤ ‖(s : ℂ)‖ + ‖(η : ℂ) * Complex.I‖ := norm_add_le _ _
          _ = _ := by rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Complex.norm_real, Real.norm_of_nonneg hs, Real.norm_of_nonneg hη.1.le]
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hc1 (add_nonneg hs hη.1.le)
        linarith [hη.2]

theorem standard_bubble_log_upper_common_bound {m s η x : ℝ} (hs : 0 ≤ s)
    (hη : η ∈ Ioc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1)
    (hn : standardBubbleRealDenominator m s x ≠ 0) :
    ‖standardBubbleLog m ((s : ℂ) + (η : ℂ) * Complex.I) x‖ ≤
      |Real.log (m ^ 2)| + |Real.log (standardBubbleRealDenominator m s x)| +
        |Real.log (m ^ 2 + s + 1)| + Real.pi := by
  obtain ⟨hlower, hupper⟩ := standard_bubble_boundary_denominator_bounds hs hη hx
  have hb := complex_log_norm_bound_between (abs_pos.mpr hn) hlower hupper
  rw [Real.log_abs] at hb
  have hc : ‖Complex.log ((m ^ 2 : ℝ) : ℂ)‖ = |Real.log (m ^ 2)| := by
    rw [← Complex.ofReal_log (sq_nonneg m), Complex.norm_real, Real.norm_eq_abs]
  unfold standardBubbleLog
  exact (norm_sub_le _ _).trans (by rw [hc]; linarith)

theorem standard_bubble_upper_log_tendsto {m s x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hn : standardBubbleRealDenominator m s x ≠ 0) :
    Tendsto (fun η : ℝ => standardBubbleLog m ((s : ℂ) + (η : ℂ) * Complex.I) x)
      (𝓝[>] (0 : ℝ)) (𝓝 (standardBubbleUpperLog m s x)) := by
  let D : ℝ → ℂ := fun η => ((m ^ 2 : ℝ) : ℂ) -
    (bubbleFeynmanWeight x : ℂ) * ((s : ℂ) + (η : ℂ) * Complex.I)
  have hD : Tendsto D (𝓝[>] (0 : ℝ)) (𝓝 ((standardBubbleRealDenominator m s x : ℝ) : ℂ)) := by
    have hc : Continuous D := by unfold D; fun_prop
    convert (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds using 1
    simp only [D, Complex.ofReal_zero, zero_mul, add_zero, standardBubbleRealDenominator,
      Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_mul]
  have hconst : Complex.log ((m ^ 2 : ℝ) : ℂ) = (Real.log (m ^ 2) : ℂ) :=
    (Complex.ofReal_log (sq_nonneg m)).symm
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · have hc0 := (bubbleFeynmanWeight_bounds hx).1
    have hcpos : 0 < bubbleFeynmanWeight x := by
      by_contra h
      have hc : bubbleFeynmanWeight x = 0 := le_antisymm (le_of_not_gt h) hc0
      unfold standardBubbleRealDenominator at hneg
      rw [hc, zero_mul, sub_zero] at hneg
      exact (not_lt_of_ge (sq_nonneg m)) hneg
    have hDw : Tendsto D (𝓝[>] (0 : ℝ))
        (𝓝[{z : ℂ | z.im < 0}] ((standardBubbleRealDenominator m s x : ℝ) : ℂ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hD, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with η hη
      have hη0 : 0 < η := hη
      change (D η).im < 0
      simp only [D, Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.add_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_mul, zero_add, add_zero]
      simpa only [zero_sub] using neg_neg_of_pos (mul_pos hcpos hη0)
    have hlog := (Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
      (show (((standardBubbleRealDenominator m s x : ℝ) : ℂ)).re < 0 from hneg)
      (Complex.ofReal_im _)).comp hDw
    have hmain := (tendsto_const_nhds (x := Complex.log ((m ^ 2 : ℝ) : ℂ))).sub hlog
    change Tendsto (fun η : ℝ => Complex.log ((m ^ 2 : ℝ) : ℂ) - Complex.log (D η)) _ _
    convert hmain using 1
    unfold standardBubbleUpperLog
    rw [if_pos hneg, Complex.norm_real, Real.norm_eq_abs, Real.log_abs]
    rw [Complex.ofReal_sub]
    rw [hconst]
    ring
  · have hslit : ((standardBubbleRealDenominator m s x : ℝ) : ℂ) ∈ Complex.slitPlane :=
      Or.inl hpos
    have hlog := (Complex.differentiableAt_log hslit).continuousAt.tendsto.comp hD
    have hmain := (tendsto_const_nhds (x := Complex.log ((m ^ 2 : ℝ) : ℂ))).sub hlog
    change Tendsto (fun η : ℝ => Complex.log ((m ^ 2 : ℝ) : ℂ) - Complex.log (D η)) _ _
    convert hmain using 1
    unfold standardBubbleUpperLog
    rw [if_neg (not_lt_of_ge hpos.le), add_zero, Complex.ofReal_sub, hconst,
      ← Complex.ofReal_log hpos.le]

theorem standard_bubble_upper_log_measurable (m s : ℝ) : Measurable (standardBubbleUpperLog m s) := by
  have hd : Measurable (standardBubbleRealDenominator m s) := by
    unfold standardBubbleRealDenominator bubbleFeynmanWeight
    fun_prop
  exact (Complex.measurable_ofReal.comp (measurable_const.sub hd.log)).add
    (Measurable.ite (measurableSet_lt hd measurable_const) measurable_const measurable_const)

theorem standard_bubble_upper_log_integrable (m s : ℝ) :
    IntegrableOn (standardBubbleUpperLog m s) (Icc (0 : ℝ) 1) := by
  apply (((integrable_const |Real.log (m ^ 2)|).add
    (standard_bubble_denominator_log_integrable m s)).add (integrable_const Real.pi)).mono'
    (standard_bubble_upper_log_measurable m s).aestronglyMeasurable
  filter_upwards with x
  unfold standardBubbleUpperLog
  have harg : ‖(if standardBubbleRealDenominator m s x < 0 then
      (Real.pi : ℂ) * Complex.I else 0)‖ ≤ Real.pi := by
    split_ifs
    · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    · simpa only [norm_zero] using Real.pi_pos.le
  calc
    _ ≤ ‖((Real.log (m ^ 2) - Real.log (standardBubbleRealDenominator m s x) : ℝ) : ℂ)‖ +
        ‖(if standardBubbleRealDenominator m s x < 0 then (Real.pi : ℂ) * Complex.I else 0)‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add (abs_sub _ _) harg

/-- The logarithmic upper-rim boundary is obtained by dominated convergence
in the actual Feynman x-integral. The common majorant includes the real
quadratic logarithmic singularities; it is not an assumed boundary formula. -/
theorem standard_bubble_upper_boundary_tendsto {m s : ℝ} (hm : 0 < m) (hs : 0 ≤ s) :
    Tendsto (fun η : ℝ => standardBubble m ((s : ℂ) + (η : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 (standardBubbleUpperBoundary m s)) := by
  let M : ℝ → ℝ := fun x => |Real.log (m ^ 2)| +
    |Real.log (standardBubbleRealDenominator m s x)| + |Real.log (m ^ 2 + s + 1)| + Real.pi
  have hMi : IntegrableOn M (Icc (0 : ℝ) 1) :=
    (((integrable_const |Real.log (m ^ 2)|).add (standard_bubble_denominator_log_integrable m s)).add
      (integrable_const |Real.log (m ^ 2 + s + 1)|)).add (integrable_const Real.pi)
  have hI : Tendsto (fun η : ℝ => ∫ x in Icc (0 : ℝ) 1,
      standardBubbleLog m ((s : ℂ) + (η : ℂ) * Complex.I) x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x in Icc (0 : ℝ) 1, standardBubbleUpperLog m s x)) := by
    apply tendsto_integral_filter_of_dominated_convergence M
    · exact Eventually.of_forall (fun η => by
        apply Measurable.aestronglyMeasurable
        unfold standardBubbleLog bubbleFeynmanWeight
        fun_prop)
    · filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with η hη
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae (standard_bubble_real_denominator_nonzero_ae hm s)] with x hx hn
      exact standard_bubble_log_upper_common_bound hs hη hx hn
    · exact hMi
    · filter_upwards [ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae (standard_bubble_real_denominator_nonzero_ae hm s)] with x hx hn
      exact standard_bubble_upper_log_tendsto hx hn
  exact tendsto_const_nhds.mul hI

def gaussianNormalizedBubbleUpperBoundary (t m s : ℝ) : ℂ :=
  standardBubbleUpperBoundary m s + gaussianRemainder t m (s : ℂ)

theorem gaussian_normalized_bubble_upper_boundary_tendsto {t m s : ℝ}
    (ht : 0 < t) (hm : 0 < m) (hs : 0 ≤ s) :
    Tendsto (fun η : ℝ => gaussianNormalizedBubble t m ((s : ℂ) + (η : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 (gaussianNormalizedBubbleUpperBoundary t m s)) := by
  have hcurve : Tendsto (fun η : ℝ => (s : ℂ) + (η : ℂ) * Complex.I)
      (𝓝[>] (0 : ℝ)) (𝓝 (s : ℂ)) := by
    have hc : Continuous (fun η : ℝ => (s : ℂ) + (η : ℂ) * Complex.I) := by fun_prop
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
      (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  exact (standard_bubble_upper_boundary_tendsto hm hs).add
    (((gaussian_remainder_entire ht.le).continuous.continuousAt).tendsto.comp hcurve)

end UV
