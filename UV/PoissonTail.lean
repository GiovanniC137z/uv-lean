import UV.ScalarGaussian
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The exact four dimensional Poisson kernel and its convolution tail.
The tail argument uses a global polynomial envelope, so a finite fifth moment
of the convolution measure suffices. -/

noncomputable section
open MeasureTheory Real Filter
open scoped Topology

namespace UV

def stablePoissonRadius (a : ℝ) (x : ScalarMomentum) : ℝ :=
  Real.sqrt (a ^ 2 + ‖x‖ ^ 2)

def stablePoissonKernel (a : ℝ) (x : ScalarMomentum) : ℝ :=
  (3 * a / (4 * Real.pi ^ 2)) / stablePoissonRadius a x ^ 5

def stableCoordinateConvolution (a : ℝ) (μ : Measure ScalarMomentum)
    (x : ScalarMomentum) : ℝ := ∫ y, stablePoissonKernel a (x - y) ∂μ

theorem stablePoissonRadius_nonneg (a : ℝ) (x : ScalarMomentum) :
    0 ≤ stablePoissonRadius a x := Real.sqrt_nonneg _

theorem stablePoissonRadius_sq (a : ℝ) (x : ScalarMomentum) :
    stablePoissonRadius a x ^ 2 = a ^ 2 + ‖x‖ ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem stablePoissonRadius_ge_norm (a : ℝ) (x : ScalarMomentum) :
    ‖x‖ ≤ stablePoissonRadius a x := by
  nlinarith [stablePoissonRadius_nonneg a x, stablePoissonRadius_sq a x,
    norm_nonneg x, sq_nonneg a]

theorem stablePoissonRadius_ge (a : ℝ) (x : ScalarMomentum) :
    a ≤ stablePoissonRadius a x := by
  nlinarith [stablePoissonRadius_nonneg a x, stablePoissonRadius_sq a x,
    sq_nonneg ‖x‖]

theorem stablePoissonRadius_pos {a : ℝ} (ha : 0 < a) (x : ScalarMomentum) :
    0 < stablePoissonRadius a x := ha.trans_le (stablePoissonRadius_ge a x)

theorem stablePoissonRadius_triangle (a : ℝ) (x y : ScalarMomentum) :
    stablePoissonRadius a (x + y) ≤ stablePoissonRadius a x + ‖y‖ := by
  have hxy := norm_add_le x y
  have hx := stablePoissonRadius_ge_norm a x
  have hy := norm_nonneg y
  have hz := norm_nonneg (x + y)
  have hr := stablePoissonRadius_nonneg a x
  have hp := mul_nonneg hy (sub_nonneg.mpr hx)
  have hs := stablePoissonRadius_sq a (x + y)
  have ht := stablePoissonRadius_sq a x
  nlinarith [sq_nonneg (‖x‖ + ‖y‖ - ‖x + y‖)]

theorem stablePoissonRadius_sub_abs (a : ℝ) (x y : ScalarMomentum) :
    |stablePoissonRadius a (x - y) - stablePoissonRadius a x| ≤ ‖y‖ := by
  apply abs_le.mpr
  constructor
  · have h := stablePoissonRadius_triangle a (x - y) y
    simp only [sub_add_cancel] at h
    linarith
  · have h := stablePoissonRadius_triangle a x (-y)
    simp only [← sub_eq_add_neg, norm_neg] at h
    linarith

theorem stablePoissonKernel_eq_rpow (a : ℝ) (x : ScalarMomentum) :
    stablePoissonKernel a x = (3 * a / (4 * Real.pi ^ 2)) *
      (a ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) := by
  rw [show -(5 : ℝ) / 2 = -(5 / 2 : ℝ) by ring, Real.rpow_neg (add_nonneg (sq_nonneg _) (sq_nonneg _)),
    Real.rpow_div_two_eq_sqrt _ (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  norm_num [stablePoissonKernel, stablePoissonRadius, div_eq_mul_inv]

theorem stablePoissonKernel_pos {a : ℝ} (ha : 0 < a) (x : ScalarMomentum) :
    0 < stablePoissonKernel a x := by
  exact div_pos (div_pos (by positivity) (by positivity))
    (pow_pos (stablePoissonRadius_pos ha x) _)

theorem stablePoissonKernel_continuous {a : ℝ} (ha : 0 < a) :
    Continuous (stablePoissonKernel a) := by
  apply continuous_const.div
  · exact (Real.continuous_sqrt.comp (continuous_const.add (continuous_norm.pow 2))).pow 5
  · intro x
    exact pow_ne_zero _ (stablePoissonRadius_pos ha x).ne'

theorem stablePoissonKernel_le_zero {a : ℝ} (ha : 0 < a) (x : ScalarMomentum) :
    stablePoissonKernel a x ≤ stablePoissonKernel a 0 := by
  have hz : stablePoissonRadius a 0 = a := by
    simp [stablePoissonRadius, Real.sqrt_sq ha.le]
  unfold stablePoissonKernel
  rw [hz]
  exact div_le_div_of_nonneg_left (by positivity) (pow_pos ha 5)
    (pow_le_pow_left₀ ha.le (stablePoissonRadius_ge a x) 5)

theorem stablePoissonKernel_ratio (a : ℝ) (ha : 0 < a) (x y : ScalarMomentum) :
    stablePoissonKernel a (x - y) / stablePoissonKernel a x =
      (stablePoissonRadius a x / stablePoissonRadius a (x - y)) ^ 5 := by
  have hx := (stablePoissonRadius_pos ha x).ne'
  have hy := (stablePoissonRadius_pos ha (x - y)).ne'
  have hc : 3 * a / (4 * Real.pi ^ 2) ≠ 0 := by positivity
  unfold stablePoissonKernel
  field_simp

 theorem stablePoissonKernel_ratio_bound {a : ℝ} (ha : 0 < a)
    (x y : ScalarMomentum) :
    stablePoissonKernel a (x - y) / stablePoissonKernel a x ≤ (1 + ‖y‖ / a) ^ 5 := by
  rw [stablePoissonKernel_ratio a ha]
  apply pow_le_pow_left₀ (div_nonneg (stablePoissonRadius_nonneg _ _)
    (stablePoissonRadius_nonneg _ _))
  apply (div_le_iff₀ (stablePoissonRadius_pos ha (x - y))).mpr
  have ht := stablePoissonRadius_triangle a (x - y) y
  simp only [sub_add_cancel] at ht
  have hn := norm_nonneg y
  have hb := stablePoissonRadius_ge a (x - y)
  have hh := mul_nonneg (div_nonneg hn ha.le) (sub_nonneg.mpr hb)
  have hid : (‖y‖ / a) * a = ‖y‖ := div_mul_cancel₀ _ ha.ne'
  nlinarith

 theorem stableCoordinateConvolution_integrable {a : ℝ} (ha : 0 < a)
    (μ : Measure ScalarMomentum) [IsFiniteMeasure μ] (x : ScalarMomentum) :
    Integrable (fun y => stablePoissonKernel a (x - y)) μ := by
  apply (integrable_const (stablePoissonKernel a 0)).mono'
  · exact ((stablePoissonKernel_continuous ha).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (stablePoissonKernel_pos ha _)]
      exact stablePoissonKernel_le_zero ha _

 theorem stableCoordinateConvolution_nonneg {a : ℝ} (ha : 0 < a)
    (μ : Measure ScalarMomentum) (x : ScalarMomentum) :
    0 ≤ stableCoordinateConvolution a μ x :=
  integral_nonneg fun _ => (stablePoissonKernel_pos ha _).le

 theorem stableCoordinateConvolution_le {a : ℝ} (ha : 0 < a)
    (μ : Measure ScalarMomentum) [IsFiniteMeasure μ] (x : ScalarMomentum) :
    stableCoordinateConvolution a μ x ≤ (μ Set.univ).toReal * stablePoissonKernel a 0 := by
  calc
    stableCoordinateConvolution a μ x ≤ ∫ _ : ScalarMomentum, stablePoissonKernel a 0 ∂μ :=
      integral_mono (stableCoordinateConvolution_integrable ha μ x) (integrable_const _)
        (fun y => stablePoissonKernel_le_zero ha (x-y))
    _ = _ := by simp [Measure.real, mul_comm]

 theorem stablePoissonKernel_ratio_tendsto {ι : Type*} {l : Filter ι}
    {a : ℝ} (ha : 0 < a) (x : ι → ScalarMomentum)
    (hx : Tendsto (fun i => ‖x i‖) l atTop) (y : ScalarMomentum) :
    Tendsto (fun i => stablePoissonKernel a (x i - y) / stablePoissonKernel a (x i))
      l (𝓝 1) := by
  have hrad : Tendsto (fun i => stablePoissonRadius a (x i - y)) l atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hx.eventually (eventually_ge_atTop (b + ‖y‖))] with i hi
    have htri : ‖x i‖ ≤ ‖x i - y‖ + ‖y‖ := by
      simpa only [sub_add_cancel] using norm_add_le (x i - y) y
    linarith [stablePoissonRadius_ge_norm a (x i - y)]
  have hinv := tendsto_inv_atTop_zero.comp hrad
  have hb : ∀ i, |stablePoissonRadius a (x i) /
      stablePoissonRadius a (x i - y) - 1| ≤
        ‖y‖ * (stablePoissonRadius a (x i - y))⁻¹ := by
    intro i
    have hr := stablePoissonRadius_pos ha (x i - y)
    rw [div_sub_one hr.ne', abs_div, abs_of_pos hr, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hr.le)
    rw [abs_sub_comm]
    exact stablePoissonRadius_sub_abs a (x i) y
  have hz : Tendsto (fun i => |stablePoissonRadius a (x i) /
      stablePoissonRadius a (x i - y) - 1|) l (𝓝 0) := by
    apply squeeze_zero (fun i => abs_nonneg _) hb
    simpa using tendsto_const_nhds.mul hinv
  have hr : Tendsto (fun i => stablePoissonRadius a (x i) /
      stablePoissonRadius a (x i - y)) l (𝓝 1) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using hz
  simpa only [stablePoissonKernel_ratio a ha, one_pow] using hr.pow 5

 theorem stableCoordinateConvolution_ratio_tendsto {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {a : ℝ} (ha : 0 < a)
    (μ : Measure ScalarMomentum) [IsFiniteMeasure μ]
    (hMoment : Integrable (fun y : ScalarMomentum => (1 + ‖y‖ / a) ^ 5) μ)
    (x : ι → ScalarMomentum) (hx : Tendsto (fun i => ‖x i‖) l atTop) :
    Tendsto (fun i => stableCoordinateConvolution a μ (x i) / stablePoissonKernel a (x i))
      l (𝓝 (μ Set.univ).toReal) := by
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (F := fun i y => stablePoissonKernel a (x i-y) /
      stablePoissonKernel a (x i)) (f := fun _ => (1:ℝ))
    (fun y => (1 + ‖y‖ / a) ^ 5)
    (Eventually.of_forall fun i =>
      ((((stablePoissonKernel_continuous ha).comp
        (continuous_const.sub continuous_id)).div_const _).aestronglyMeasurable))
    (Eventually.of_forall fun i => Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (div_pos (stablePoissonKernel_pos ha _)
        (stablePoissonKernel_pos ha _))]
      exact stablePoissonKernel_ratio_bound ha (x i) y)
    hMoment (Eventually.of_forall (stablePoissonKernel_ratio_tendsto ha x hx))
  simpa only [integral_div, stableCoordinateConvolution,
    integral_const, smul_eq_mul, mul_one, Measure.real] using ht

 theorem stablePoissonEnvelope_integrable {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (μ : Measure ScalarMomentum)
    (hexp : Integrable (fun y : ScalarMomentum => Real.exp (c * ‖y‖)) μ) :
    Integrable (fun y : ScalarMomentum => (1 + ‖y‖ / a) ^ 5) μ := by
  apply (hexp.const_mul (((5 : ℕ).factorial : ℝ) / (c*a)^5 * Real.exp (c*a))).mono'
  · exact ((continuous_const.add (continuous_norm.div_const a)).pow 5).aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1 + ‖y‖ / a)^5)]
    have ht : 0 ≤ 1 + ‖y‖ / a := by positivity
    have hpow := pow_mul_exp_neg_le (mul_pos hc ha) ht 5
    have he : (1 + ‖y‖ / a)^5 =
        ((1 + ‖y‖ / a)^5 * Real.exp (-(c*a*(1 + ‖y‖ / a)))) *
          Real.exp (c*a*(1 + ‖y‖ / a)) := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    rw [he]
    calc
      _ ≤ (((5 : ℕ).factorial : ℝ) / (c*a)^5) * Real.exp (c*a*(1 + ‖y‖ / a)) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
      _ = _ := by
        rw [show c*a*(1 + ‖y‖/a) = c*a + c*‖y‖ by field_simp,
          Real.exp_add]
        ring

 theorem stablePoissonRadius_le {a : ℝ} (ha : 0 ≤ a) (x : ScalarMomentum) :
    stablePoissonRadius a x ≤ a + ‖x‖ := by
  nlinarith [stablePoissonRadius_nonneg a x, stablePoissonRadius_sq a x,
    mul_nonneg ha (norm_nonneg x), norm_nonneg x]

 theorem stablePoissonKernel_exact_tail {ι : Type*} {l : Filter ι}
    {a : ℝ} (ha : 0 < a) (x : ι → ScalarMomentum)
    (hx : Tendsto (fun i => ‖x i‖) l atTop) :
    Tendsto (fun i => ‖x i‖ ^ 5 * stablePoissonKernel a (x i)) l
      (𝓝 (3*a/(4*Real.pi^2))) := by
  have hi := tendsto_inv_atTop_zero.comp hx
  have hev : ∀ᶠ i in l, 0 < ‖x i‖ := hx.eventually (eventually_gt_atTop 0)
  have hz : Tendsto (fun i => |stablePoissonRadius a (x i) / ‖x i‖ - 1|)
      l (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun i => abs_nonneg _) _
      (by simpa using (tendsto_const_nhds.mul hi :
        Tendsto (fun i => a * ‖x i‖⁻¹) l (𝓝 (a*0))))
    filter_upwards [hev] with i hr
    rw [abs_of_nonneg ((le_div_iff₀ hr).mpr (by
      simpa using stablePoissonRadius_ge_norm a (x i)) |> sub_nonneg.mpr)]
    apply (le_div_iff₀ hr).mpr
    have hle := stablePoissonRadius_le ha.le (x i)
    field_simp
    nlinarith
  have hr : Tendsto (fun i => stablePoissonRadius a (x i) / ‖x i‖) l (𝓝 1) := by
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using hz)
  have hri := hr.inv₀ (by norm_num : (1:ℝ) ≠ 0)
  have hrp := hri.pow 5
  have ht := hrp.const_mul (3*a/(4*Real.pi^2))
  simp only [inv_one, one_pow, mul_one] at ht
  apply ht.congr'
  filter_upwards with i
  simp only [inv_div, stablePoissonKernel]
  ring

 theorem stableCoordinateConvolution_exact_tail {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {a : ℝ} (ha : 0 < a)
    (μ : Measure ScalarMomentum) [IsFiniteMeasure μ]
    (hMoment : Integrable (fun y : ScalarMomentum => (1 + ‖y‖ / a) ^ 5) μ)
    (x : ι → ScalarMomentum) (hx : Tendsto (fun i => ‖x i‖) l atTop) :
    Tendsto (fun i => ‖x i‖ ^ 5 * stableCoordinateConvolution a μ (x i)) l
      (𝓝 ((3*a/(4*Real.pi^2)) * (μ Set.univ).toReal)) := by
  have ht := (stablePoissonKernel_exact_tail ha x hx).mul
    (stableCoordinateConvolution_ratio_tendsto ha μ hMoment x hx)
  apply ht.congr'
  filter_upwards with i
  have hp := (stablePoissonKernel_pos ha (x i)).ne'
  field_simp

end UV
