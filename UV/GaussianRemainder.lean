import UV.Holomorphy
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-! The Gaussian entire remainder, represented on a fixed finite parameter
square by the exact proper-time rescaling W = v Wmin(x). -/

noncomputable section
open MeasureTheory Set Real Complex Filter Metric
open scoped Topology

namespace UV

def gaussianWmin (t x : ℝ) : ℝ := t / min x (1 - x)
def gaussianRemainderScale (t x : ℝ) : ℝ := t * max x (1 - x)

def gaussianUnitMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))

instance gaussianUnitMeasure_isFinite : IsFiniteMeasure gaussianUnitMeasure := by
  unfold gaussianUnitMeasure
  infer_instance

theorem gaussian_remainder_scale_bounds {t x : ℝ} (ht : 0 ≤ t) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 ≤ gaussianWmin t x ∧ 0 ≤ gaussianRemainderScale t x ∧ gaussianRemainderScale t x ≤ t := by
  have hx0 := hx.1
  have hx1 := hx.2
  have hm : 0 < min x (1 - x) := lt_min hx0 (by linarith)
  refine ⟨div_nonneg ht hm.le, mul_nonneg ht (le_max_of_le_left hx0.le), ?_⟩
  exact mul_le_of_le_one_right ht (max_le hx1.le (by linarith))

theorem gaussian_Wmin_coefficient {t x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    gaussianWmin t x * (x * (1 - x)) = gaussianRemainderScale t x := by
  unfold gaussianWmin gaussianRemainderScale
  by_cases h : x ≤ 1 - x
  · rw [min_eq_left h, max_eq_right h]
    field_simp [ne_of_gt hx.1]
  · have h' : 1 - x ≤ x := le_of_lt (lt_of_not_ge h)
    rw [min_eq_right h', max_eq_left h']
    have hn : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx.2)
    field_simp

theorem gaussian_unit_parameters :
    ∀ᵐ p : ℝ × ℝ ∂gaussianUnitMeasure, p.1 ∈ Ioo (0 : ℝ) 1 ∧ p.2 ∈ Ioo (0 : ℝ) 1 := by
  have hx := (Measure.quasiMeasurePreserving_fst
    (μ := volume.restrict (Ioo (0 : ℝ) 1)) (ν := volume.restrict (Ioo (0 : ℝ) 1))).ae
    (ae_restrict_mem measurableSet_Ioo)
  have hv := (Measure.quasiMeasurePreserving_snd
    (μ := volume.restrict (Ioo (0 : ℝ) 1)) (ν := volume.restrict (Ioo (0 : ℝ) 1))).ae
    (ae_restrict_mem measurableSet_Ioo)
  exact hx.and hv

/-- Literal rescaled omitted-proper-time integrand. It is entire in z at
every parameter point, including the harmless total-division value at v=0. -/
def gaussianRemainderUnitIntegrand (t m : ℝ) (z : ℂ) (p : ℝ × ℝ) : ℂ :=
  ((Real.exp (-m ^ 2 * (p.2 * gaussianWmin t p.1)) / p.2 : ℝ) : ℂ) *
    (1 - Complex.exp (((p.2 * gaussianRemainderScale t p.1 : ℝ) : ℂ) * z))

def gaussianRemainder (t m : ℝ) (z : ℂ) : ℂ :=
  (16 * Real.pi ^ 2 : ℂ)⁻¹ * ∫ p, gaussianRemainderUnitIntegrand t m z p ∂gaussianUnitMeasure

theorem gaussian_remainder_unit_bound {t m : ℝ} (ht : 0 ≤ t) (z : ℂ) {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (0 : ℝ) 1) (hv : p.2 ∈ Ioo (0 : ℝ) 1) :
    ‖gaussianRemainderUnitIntegrand t m z p‖ ≤
      gaussianRemainderScale t p.1 * ‖z‖ * Real.exp (t * ‖z‖) := by
  obtain ⟨hW, hA, hAt⟩ := gaussian_remainder_scale_bounds ht hx
  have hvA : 0 ≤ p.2 * gaussianRemainderScale t p.1 := mul_nonneg hv.1.le hA
  have hvAt : p.2 * gaussianRemainderScale t p.1 ≤ t :=
    (mul_le_of_le_one_left hA hv.2.le).trans hAt
  have hmass : Real.exp (-m ^ 2 * (p.2 * gaussianWmin t p.1)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg m))
      (mul_nonneg hv.1.le hW))
  have hdiff := Complex.norm_exp_sub_sum_le_norm_mul_exp
    (((p.2 * gaussianRemainderScale t p.1 : ℝ) : ℂ) * z) 1
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one] at hdiff
  rw [norm_sub_rev] at hdiff
  have harg : ‖((p.2 * gaussianRemainderScale t p.1 : ℝ) : ℂ) * z‖ =
      (p.2 * gaussianRemainderScale t p.1) * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hvA]
  rw [harg] at hdiff
  have he : Real.exp ((p.2 * gaussianRemainderScale t p.1) * ‖z‖) ≤ Real.exp (t * ‖z‖) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hvAt (norm_nonneg _))
  unfold gaussianRemainderUnitIntegrand
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (Real.exp_nonneg _) hv.1.le)]
  calc
    _ ≤ (1 / p.2) * ((p.2 * gaussianRemainderScale t p.1) * ‖z‖ * Real.exp (t * ‖z‖)) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_right hmass hv.1.le
      · exact hdiff.trans (mul_le_mul_of_nonneg_left he (mul_nonneg hvA (norm_nonneg _)))
      · exact norm_nonneg _
      · exact div_nonneg zero_le_one hv.1.le
    _ = _ := by field_simp [ne_of_gt hv.1]

theorem gaussian_remainder_scale_continuous (t : ℝ) : Continuous (gaussianRemainderScale t) := by
  unfold gaussianRemainderScale
  fun_prop

theorem gaussian_remainder_scale_integrable (t : ℝ) :
    Integrable (fun p : ℝ × ℝ => gaussianRemainderScale t p.1) gaussianUnitMeasure := by
  exact ((gaussian_remainder_scale_continuous t).integrableOn_Icc.mono_set Ioo_subset_Icc_self).comp_fst _

theorem gaussian_remainder_scale_integral (t : ℝ) :
    (∫ p : ℝ × ℝ, gaussianRemainderScale t p.1 ∂gaussianUnitMeasure) = 3 * t / 4 := by
  have hcont := gaussian_remainder_scale_continuous t
  have hleft : (∫ x in (0 : ℝ)..(1 / 2 : ℝ), gaussianRemainderScale t x) = 3 * t / 8 := by
    calc
      _ = ∫ x in (0 : ℝ)..(1 / 2 : ℝ), t * (1 - x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Icc (0 : ℝ) (1 / 2) := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hx
        exact congrArg (t * ·) (max_eq_right (by linarith [hx'.2] : x ≤ 1 - x))
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
          (f := fun _ : ℝ => (1 : ℝ)) (g := fun x : ℝ => x)
          (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _)]
        simp
        ring
  have hright : (∫ x in (1 / 2 : ℝ)..(1 : ℝ), gaussianRemainderScale t x) = 3 * t / 8 := by
    calc
      _ = ∫ x in (1 / 2 : ℝ)..(1 : ℝ), t * x := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Icc (1 / 2 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] using hx
        exact congrArg (t * ·) (max_eq_left (by linarith [hx'.1] : 1 - x ≤ x))
      _ = _ := by rw [intervalIntegral.integral_const_mul]; simp; ring
  rw [gaussianUnitMeasure, integral_prod _ (gaussian_remainder_scale_integrable t)]
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
    ENNReal.toReal_ofReal zero_le_one, one_smul]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 (1 / 2))
    (hcont.intervalIntegrable (1 / 2) 1), hleft, hright]
  ring

theorem gaussian_remainder_unit_measurable (t m : ℝ) (z : ℂ) :
    Measurable (gaussianRemainderUnitIntegrand t m z) := by
  unfold gaussianRemainderUnitIntegrand gaussianWmin gaussianRemainderScale
  fun_prop

theorem gaussian_remainder_unit_integrable {t m : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    Integrable (gaussianRemainderUnitIntegrand t m z) gaussianUnitMeasure := by
  apply (((gaussian_remainder_scale_integrable t).mul_const ‖z‖).mul_const
    (Real.exp (t * ‖z‖))).mono' (gaussian_remainder_unit_measurable t m z).aestronglyMeasurable
  filter_upwards [gaussian_unit_parameters] with p hp
  exact gaussian_remainder_unit_bound ht z hp.1 hp.2

theorem gaussian_remainder_entire {t m : ℝ} (ht : 0 ≤ t) :
    Differentiable ℂ (gaussianRemainder t m) := by
  have h : DifferentiableOn ℂ
      (fun z => ∫ p, gaussianRemainderUnitIntegrand t m z p ∂gaussianUnitMeasure) univ := by
    apply holomorphy_from_local_graph_majorants isOpen_univ
      (fun z _ => (gaussian_remainder_unit_measurable t m z).aestronglyMeasurable)
    · exact Eventually.of_forall (fun p => by unfold gaussianRemainderUnitIntegrand; fun_prop)
    · intro c _
      refine ⟨1, zero_lt_one, subset_univ _, fun p => gaussianRemainderScale t p.1 * (‖c‖ + 1) *
        Real.exp (t * (‖c‖ + 1)),
        ((gaussian_remainder_scale_integrable t).mul_const (‖c‖ + 1)).mul_const _, ?_⟩
      filter_upwards [gaussian_unit_parameters] with p hp
      intro z hz
      have hA := (gaussian_remainder_scale_bounds ht hp.1).2.1
      have hz' : ‖z‖ ≤ ‖c‖ + 1 := by
        have hd : ‖z - c‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hz
        have hn := norm_add_le (z - c) c
        rw [sub_add_cancel] at hn
        linarith
      exact (gaussian_remainder_unit_bound ht z hp.1 hp.2).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left hz' hA)
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz' ht))
          (Real.exp_nonneg _) (mul_nonneg hA (by positivity)))
  intro z
  exact ((differentiableOn_univ.mp h) z).const_mul _

theorem gaussian_remainder_zero (t m : ℝ) : gaussianRemainder t m 0 = 0 := by
  simp [gaussianRemainder, gaussianRemainderUnitIntegrand]

theorem gaussian_remainder_norm_bound {t m : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    ‖gaussianRemainder t m z‖ ≤ 3 * t * ‖z‖ / (64 * Real.pi ^ 2) * Real.exp (t * ‖z‖) := by
  have hM := ((gaussian_remainder_scale_integrable t).mul_const ‖z‖).mul_const (Real.exp (t * ‖z‖))
  have hb : ‖∫ p, gaussianRemainderUnitIntegrand t m z p ∂gaussianUnitMeasure‖ ≤
      ∫ p, gaussianRemainderScale t p.1 * ‖z‖ * Real.exp (t * ‖z‖) ∂gaussianUnitMeasure := by
    apply norm_integral_le_of_norm_le hM
    filter_upwards [gaussian_unit_parameters] with p hp
    exact gaussian_remainder_unit_bound ht z hp.1 hp.2
  unfold gaussianRemainder
  rw [norm_mul, norm_inv]
  have hnorm : ‖(16 * Real.pi ^ 2 : ℂ)‖ = 16 * Real.pi ^ 2 := by
    norm_cast
    rw [Real.norm_of_nonneg (by positivity)]
  rw [hnorm]
  calc
    _ ≤ (16 * Real.pi ^ 2)⁻¹ *
        (∫ p, gaussianRemainderScale t p.1 * ‖z‖ * Real.exp (t * ‖z‖) ∂gaussianUnitMeasure) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [integral_mul_const, integral_mul_const, gaussian_remainder_scale_integral]; ring

def gaussianRemainderProperIntegrand (m : ℝ) (z : ℂ) (x W : ℝ) : ℂ :=
  ((Real.exp (-m ^ 2 * W) / W : ℝ) : ℂ) *
    (1 - Complex.exp (((W * (x * (1 - x)) : ℝ) : ℂ) * z))

theorem gaussian_remainder_rescaling {t m x : ℝ} (ht : 0 < t)
    (hx : x ∈ Ioo (0 : ℝ) 1) (z : ℂ) (v : ℝ) :
    gaussianRemainderUnitIntegrand t m z (x, v) =
      gaussianWmin t x • gaussianRemainderProperIntegrand m z x (gaussianWmin t x * v) := by
  have hW : gaussianWmin t x ≠ 0 := ne_of_gt (div_pos ht (lt_min hx.1 (sub_pos.mpr hx.2)))
  have hc := gaussian_Wmin_coefficient (t := t) hx
  have harg : gaussianWmin t x * v * (x * (1 - x)) = v * gaussianRemainderScale t x := by
    rw [← hc]
    ring
  by_cases hv : v = 0
  · subst v
    simp [gaussianRemainderUnitIntegrand, gaussianRemainderProperIntegrand]
  · unfold gaussianRemainderUnitIntegrand gaussianRemainderProperIntegrand
    rw [harg, Complex.real_smul]
    push_cast
    have hcast : (gaussianWmin t x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hW
    have hvcast : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv
    rw [mul_comm (gaussianWmin t x : ℂ) (v : ℂ)]
    field_simp

theorem gaussian_remainder_proper_representation {t m : ℝ} (ht : 0 < t) (z : ℂ) :
    gaussianRemainder t m z = (16 * Real.pi ^ 2 : ℂ)⁻¹ *
      ∫ x in Ioo (0 : ℝ) 1, ∫ W in (0 : ℝ)..gaussianWmin t x,
        gaussianRemainderProperIntegrand m z x W := by
  unfold gaussianRemainder
  congr 1
  rw [gaussianUnitMeasure, integral_prod _ (gaussian_remainder_unit_integrable ht.le z)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  calc
    _ = ∫ v in (0 : ℝ)..1, gaussianWmin t x •
        gaussianRemainderProperIntegrand m z x (gaussianWmin t x * v) := by
      apply intervalIntegral.integral_congr
      intro v _
      exact gaussian_remainder_rescaling ht hx z v
    _ = gaussianWmin t x • ∫ v in (0 : ℝ)..1,
        gaussianRemainderProperIntegrand m z x (gaussianWmin t x * v) :=
      intervalIntegral.integral_smul _ _
    _ = _ := by
      rw [intervalIntegral.smul_integral_comp_mul_left]
      simp

theorem gaussian_remainder_real (t m s : ℝ) :
    gaussianRemainder t m (s : ℂ) =
      ((16 * Real.pi ^ 2)⁻¹ * ∫ p, Real.exp (-m ^ 2 * (p.2 * gaussianWmin t p.1)) / p.2 *
        (1 - Real.exp ((p.2 * gaussianRemainderScale t p.1) * s)) ∂gaussianUnitMeasure : ℝ) := by
  have he : gaussianRemainderUnitIntegrand t m (s : ℂ) = fun p =>
      ((Real.exp (-m ^ 2 * (p.2 * gaussianWmin t p.1)) / p.2 *
        (1 - Real.exp ((p.2 * gaussianRemainderScale t p.1) * s)) : ℝ) : ℂ) := by
    funext p
    simp [gaussianRemainderUnitIntegrand, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_exp]
  simp only [gaussianRemainder, he, integral_complex_ofReal]
  push_cast
  rfl

theorem gaussian_remainder_proper_bound {t m x : ℝ} (ht : 0 ≤ t)
    (hx : x ∈ Ioo (0 : ℝ) 1) (z : ℂ) {W : ℝ} (hW : W ∈ Ioo (0 : ℝ) (gaussianWmin t x)) :
    ‖gaussianRemainderProperIntegrand m z x W‖ ≤
      (x * (1 - x)) * ‖z‖ * Real.exp (t * ‖z‖) := by
  have hc : 0 ≤ x * (1 - x) := mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le)
  have hWc : 0 ≤ W * (x * (1 - x)) := mul_nonneg hW.1.le hc
  have hWct : W * (x * (1 - x)) ≤ t := by
    calc
      _ ≤ gaussianWmin t x * (x * (1 - x)) := mul_le_mul_of_nonneg_right hW.2.le hc
      _ = gaussianRemainderScale t x := gaussian_Wmin_coefficient hx
      _ ≤ t := (gaussian_remainder_scale_bounds ht hx).2.2
  have hmass : Real.exp (-m ^ 2 * W) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg m)) hW.1.le)
  have hdiff := Complex.norm_exp_sub_sum_le_norm_mul_exp (((W * (x * (1 - x)) : ℝ) : ℂ) * z) 1
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one] at hdiff
  rw [norm_sub_rev, norm_mul, Complex.norm_real, Real.norm_of_nonneg hWc] at hdiff
  have he : Real.exp ((W * (x * (1 - x))) * ‖z‖) ≤ Real.exp (t * ‖z‖) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hWct (norm_nonneg _))
  unfold gaussianRemainderProperIntegrand
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (Real.exp_nonneg _) hW.1.le)]
  calc
    _ ≤ (1 / W) * ((W * (x * (1 - x))) * ‖z‖ * Real.exp (t * ‖z‖)) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_right hmass hW.1.le
      · exact hdiff.trans (mul_le_mul_of_nonneg_left he (mul_nonneg hWc (norm_nonneg _)))
      · exact norm_nonneg _
      · exact div_nonneg zero_le_one hW.1.le
    _ = _ := by field_simp [ne_of_gt hW.1]

theorem gaussian_remainder_proper_integrable {t m x : ℝ} (ht : 0 ≤ t)
    (hx : x ∈ Ioo (0 : ℝ) 1) (z : ℂ) :
    IntervalIntegrable (gaussianRemainderProperIntegrand m z x) volume 0 (gaussianWmin t x) := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (gaussian_remainder_scale_bounds ht hx).1]
  apply (integrable_const ((x * (1 - x)) * ‖z‖ * Real.exp (t * ‖z‖))).mono'
  · apply Measurable.aestronglyMeasurable
    unfold gaussianRemainderProperIntegrand
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with W hW
    exact gaussian_remainder_proper_bound ht hx z hW

def gaussianPositiveUnitIntegrand (t m s : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-m ^ 2 * (p.2 * gaussianWmin t p.1)) / p.2 *
    (Real.exp ((p.2 * gaussianRemainderScale t p.1) * s) - 1)

def gaussianPositiveProperIntegrand (m s x W : ℝ) : ℝ :=
  Real.exp (-m ^ 2 * W) / W * (Real.exp ((W * (x * (1 - x))) * s) - 1)

theorem gaussian_positive_unit_re (t m s : ℝ) (p : ℝ × ℝ) :
    gaussianPositiveUnitIntegrand t m s p = -(gaussianRemainderUnitIntegrand t m (s : ℂ) p).re := by
  have he : gaussianRemainderUnitIntegrand t m (s : ℂ) p =
      ((Real.exp (-m ^ 2 * (p.2 * gaussianWmin t p.1)) / p.2 *
        (1 - Real.exp ((p.2 * gaussianRemainderScale t p.1) * s)) : ℝ) : ℂ) := by
    simp [gaussianRemainderUnitIntegrand, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_exp]
  rw [he, Complex.ofReal_re]
  unfold gaussianPositiveUnitIntegrand
  ring

theorem gaussian_positive_proper_re (m s x W : ℝ) :
    gaussianPositiveProperIntegrand m s x W = -(gaussianRemainderProperIntegrand m (s : ℂ) x W).re := by
  have he : gaussianRemainderProperIntegrand m (s : ℂ) x W =
      ((Real.exp (-m ^ 2 * W) / W * (1 - Real.exp ((W * (x * (1 - x))) * s)) : ℝ) : ℂ) := by
    simp [gaussianRemainderProperIntegrand, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_exp]
  rw [he, Complex.ofReal_re]
  unfold gaussianPositiveProperIntegrand
  ring

theorem gaussian_positive_unit_integrable {t m : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    Integrable (gaussianPositiveUnitIntegrand t m s) gaussianUnitMeasure := by
  have he : gaussianPositiveUnitIntegrand t m s =
      fun p => -(gaussianRemainderUnitIntegrand t m (s : ℂ) p).re := funext (gaussian_positive_unit_re t m s)
  rw [he]
  exact (gaussian_remainder_unit_integrable (m := m) ht (s : ℂ)).re.neg

theorem gaussian_positive_proper_integrable {t m x : ℝ} (ht : 0 ≤ t)
    (hx : x ∈ Ioo (0 : ℝ) 1) (s : ℝ) :
    IntervalIntegrable (gaussianPositiveProperIntegrand m s x) volume 0 (gaussianWmin t x) := by
  have hi := gaussian_remainder_proper_integrable (m := m) ht hx (s : ℂ)
  have he : gaussianPositiveProperIntegrand m s x =
      fun W => -(gaussianRemainderProperIntegrand m (s : ℂ) x W).re := funext (gaussian_positive_proper_re m s x)
  rw [he]
  constructor
  · exact hi.1.re.neg
  · exact hi.2.re.neg

theorem gaussian_positive_rescaling {t m x : ℝ} (ht : 0 < t)
    (hx : x ∈ Ioo (0 : ℝ) 1) (s v : ℝ) :
    gaussianPositiveUnitIntegrand t m s (x, v) =
      gaussianWmin t x * gaussianPositiveProperIntegrand m s x (gaussianWmin t x * v) := by
  rw [gaussian_positive_unit_re, gaussian_remainder_rescaling ht hx, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    gaussian_positive_proper_re]
  ring

theorem gaussian_positive_inner_representation {t m x : ℝ} (ht : 0 < t)
    (hx : x ∈ Ioo (0 : ℝ) 1) (s : ℝ) :
    (∫ v in Ioo (0 : ℝ) 1, gaussianPositiveUnitIntegrand t m s (x, v)) =
      ∫ W in (0 : ℝ)..gaussianWmin t x, gaussianPositiveProperIntegrand m s x W := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  calc
    _ = ∫ v in (0 : ℝ)..1, gaussianWmin t x *
        gaussianPositiveProperIntegrand m s x (gaussianWmin t x * v) := by
      apply intervalIntegral.integral_congr
      intro v _
      exact gaussian_positive_rescaling ht hx s v
    _ = _ := by
      rw [intervalIntegral.integral_const_mul]
      simpa only [smul_eq_mul, mul_zero, mul_one] using
        intervalIntegral.smul_integral_comp_mul_left
          (f := gaussianPositiveProperIntegrand m s x) (a := (0 : ℝ)) (b := (1 : ℝ)) (gaussianWmin t x)

theorem gaussian_positive_outer_integrable {t m : ℝ} (ht : 0 < t) (s : ℝ) :
    IntegrableOn (fun x => ∫ W in (0 : ℝ)..gaussianWmin t x,
      gaussianPositiveProperIntegrand m s x W) (Ioo (0 : ℝ) 1) := by
  have hi := (gaussian_positive_unit_integrable (m := m) ht.le s).integral_prod_left
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact gaussian_positive_inner_representation ht hx s

theorem gaussian_remainder_positive_representation {t m : ℝ} (ht : 0 < t) (s : ℝ) :
    -(gaussianRemainder t m (s : ℂ)).re = (16 * Real.pi ^ 2)⁻¹ *
      ∫ x in Ioo (0 : ℝ) 1, ∫ W in (0 : ℝ)..gaussianWmin t x,
        gaussianPositiveProperIntegrand m s x W := by
  rw [gaussian_remainder_real]
  simp only [Complex.ofReal_re]
  rw [← mul_neg, ← integral_neg]
  have he : (fun p : ℝ × ℝ => -(Real.exp (-m ^ 2 * (p.2 * gaussianWmin t p.1)) / p.2 *
      (1 - Real.exp ((p.2 * gaussianRemainderScale t p.1) * s)))) = gaussianPositiveUnitIntegrand t m s := by
    funext p
    unfold gaussianPositiveUnitIntegrand
    ring
  rw [he, gaussianUnitMeasure, integral_prod _ (gaussian_positive_unit_integrable ht.le s)]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact gaussian_positive_inner_representation ht hx s

theorem gaussian_Wmin_ge_twice {t x : ℝ} (ht : 0 ≤ t) (hx : x ∈ Ioo (0 : ℝ) 1) :
    2 * t ≤ gaussianWmin t x := by
  have hm : 0 < min x (1 - x) := lt_min hx.1 (sub_pos.mpr hx.2)
  have hhalf : min x (1 - x) ≤ (1 / 2 : ℝ) := by
    by_cases h : x ≤ (1 / 2 : ℝ)
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (by linarith)
  apply (le_div_iff₀ hm).mpr
  nlinarith

theorem gaussian_positive_proper_nonneg {m s x W : ℝ} (hs : 0 ≤ s)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hW : 0 ≤ W) : 0 ≤ gaussianPositiveProperIntegrand m s x W := by
  unfold gaussianPositiveProperIntegrand
  apply mul_nonneg (div_nonneg (Real.exp_nonneg _) hW)
  apply sub_nonneg.mpr
  exact Real.one_le_exp (mul_nonneg (mul_nonneg hW (mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le))) hs)

def gaussianGrowthFactor (t m s : ℝ) : ℝ :=
  Real.exp (-2 * t * m ^ 2) * (Real.exp (2 * t * s / 9) - 1)

theorem gaussian_growth_factor_nonneg {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (m : ℝ) :
    0 ≤ gaussianGrowthFactor t m s := by
  unfold gaussianGrowthFactor
  exact mul_nonneg (Real.exp_nonneg _) (sub_nonneg.mpr (Real.one_le_exp (by positivity)))

theorem gaussian_rectangle_point_bound {t m s x W : ℝ} (ht : 0 < t) (hs : 0 ≤ s)
    (hx : x ∈ Icc (1 / 3 : ℝ) (2 / 3)) (hW : W ∈ Icc t (2 * t)) :
    gaussianGrowthFactor t m s / W ≤ gaussianPositiveProperIntegrand m s x W := by
  have hW0 : 0 < W := ht.trans_le hW.1
  have hc : (2 / 9 : ℝ) ≤ x * (1 - x) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)]
  have hmass : Real.exp (-2 * t * m ^ 2) ≤ Real.exp (-m ^ 2 * W) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hW.2 (sq_nonneg m)]
  have hexp : Real.exp (2 * t * s / 9) - 1 ≤ Real.exp ((W * (x * (1 - x))) * s) - 1 := by
    apply sub_le_sub_right
    apply Real.exp_le_exp.mpr
    have hprod : t * (2 / 9 : ℝ) ≤ W * (x * (1 - x)) :=
      mul_le_mul hW.1 hc (by norm_num) hW0.le
    nlinarith [mul_le_mul_of_nonneg_right hprod hs]
  unfold gaussianGrowthFactor gaussianPositiveProperIntegrand
  calc
    _ = (Real.exp (-2 * t * m ^ 2) / W) * (Real.exp (2 * t * s / 9) - 1) := by ring
    _ ≤ _ := mul_le_mul (div_le_div_of_nonneg_right hmass hW0.le) hexp
      (sub_nonneg.mpr (Real.one_le_exp (by positivity))) (div_nonneg (Real.exp_nonneg _) hW0.le)

theorem gaussian_rectangle_inner_lower {t m s x : ℝ} (ht : 0 < t) (hs : 0 ≤ s)
    (hx : x ∈ Icc (1 / 3 : ℝ) (2 / 3)) :
    gaussianGrowthFactor t m s * Real.log 2 ≤
      ∫ W in (0 : ℝ)..gaussianWmin t x, gaussianPositiveProperIntegrand m s x W := by
  have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hi := gaussian_positive_proper_integrable (m := m) ht.le hx01 s
  have htw := gaussian_Wmin_ge_twice ht.le hx01
  have hsub : IntervalIntegrable (gaussianPositiveProperIntegrand m s x) volume t (2 * t) :=
    hi.mono_set (by
      rw [uIcc_of_le (by linarith : t ≤ 2 * t), uIcc_of_le (gaussian_remainder_scale_bounds ht.le hx01).1]
      exact Icc_subset_Icc ht.le htw)
  have hinv : IntervalIntegrable (fun W : ℝ => gaussianGrowthFactor t m s / W) volume t (2 * t) := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div continuousOn_id (fun W hW => by
      have hW' : W ∈ Icc t (2 * t) := by simpa only [uIcc_of_le (by linarith : t ≤ 2 * t)] using hW
      exact ne_of_gt (ht.trans_le hW'.1))
  have hrect : (∫ W in t..(2 * t), gaussianGrowthFactor t m s / W) ≤
      ∫ W in t..(2 * t), gaussianPositiveProperIntegrand m s x W :=
    intervalIntegral.integral_mono_on (by linarith) hinv hsub
      (fun W hW => gaussian_rectangle_point_bound ht hs hx hW)
  have hlog : (∫ W in t..(2 * t), gaussianGrowthFactor t m s / W) =
      gaussianGrowthFactor t m s * Real.log 2 := by
    simp only [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ht (by positivity)]
    congr 2
    field_simp
  rw [hlog] at hrect
  apply hrect.trans
  apply intervalIntegral.integral_mono_interval ht.le (by linarith) htw _ hi
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with W hW
  exact gaussian_positive_proper_nonneg hs hx01 hW.1.le

theorem gaussian_remainder_growth_lower {t m s : ℝ} (ht : 0 < t) (hs : 0 ≤ s) :
    Real.log 2 / (48 * Real.pi ^ 2) * Real.exp (-2 * t * m ^ 2) *
      (Real.exp (2 * t * s / 9) - 1) ≤ -(gaussianRemainder t m (s : ℂ)).re := by
  let f : ℝ → ℝ := fun x => ∫ W in (0 : ℝ)..gaussianWmin t x, gaussianPositiveProperIntegrand m s x W
  have hfi : IntegrableOn f (Ioo (0 : ℝ) 1) := gaussian_positive_outer_integrable ht s
  have hcentral : Icc (1 / 3 : ℝ) (2 / 3) ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    apply intervalIntegral.integral_nonneg (gaussian_remainder_scale_bounds ht.le hx).1
    intro W hW
    exact gaussian_positive_proper_nonneg hs hx hW.1
  have houter : gaussianGrowthFactor t m s * Real.log 2 / 3 ≤ ∫ x in Ioo (0 : ℝ) 1, f x := by
    have hc := setIntegral_ge_of_const_le (μ := volume) measurableSet_Icc
      (s := Icc (1 / 3 : ℝ) (2 / 3)) (by simp)
      (fun x hx => gaussian_rectangle_inner_lower ht hs hx) (hfi.mono_set hcentral)
    have hlen : volume.real (Icc (1 / 3 : ℝ) (2 / 3)) = (1 / 3 : ℝ) := by
      simp [Measure.real]
      norm_num
    rw [hlen] at hc
    have hset := setIntegral_mono_set hfi hnonneg hcentral.eventuallyLE
    have hbase : gaussianGrowthFactor t m s * Real.log 2 / 3 ≤
        ∫ x in Icc (1 / 3 : ℝ) (2 / 3), f x := by
      convert hc using 1
      ring
    exact hbase.trans hset
  rw [gaussian_remainder_positive_representation ht s]
  calc
    _ = (16 * Real.pi ^ 2)⁻¹ * (gaussianGrowthFactor t m s * Real.log 2 / 3) := by
      unfold gaussianGrowthFactor
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left houter (by positivity)

/-- The literal entire remainder grows faster than every polynomial power on
the positive real axis. This uses the rectangle lower bound, not a growth
hypothesis about the remainder. -/
theorem gaussian_remainder_exceeds_every_power {t m : ℝ} (ht : 0 < t) (N : ℕ) :
    Tendsto (fun s : ℝ => -(gaussianRemainder t m (s : ℂ)).re / s ^ N) atTop atTop := by
  let a : ℝ := 2 * t / 9
  let C : ℝ := Real.log 2 / (48 * Real.pi ^ 2) * Real.exp (-2 * t * m ^ 2)
  have ha : 0 < a := by dsimp [a]; positivity
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (div_pos (Real.log_pos (by norm_num)) (by positivity)) (Real.exp_pos _)
  have hscale : Tendsto (fun s : ℝ => a * s) atTop atTop := tendsto_id.const_mul_atTop ha
  have hexp := ((Real.tendsto_mul_exp_add_div_pow_atTop C (-C) N hC).comp hscale).const_mul_atTop (pow_pos ha N)
  have hlim : Tendsto (fun s : ℝ => C * (Real.exp (a * s) - 1) / s ^ N) atTop atTop := by
    convert hexp using 1
    funext s
    simp only [Function.comp_apply, mul_pow]
    calc
      _ = (C * Real.exp (a * s) + -C) / s ^ N := by ring
      _ = _ := by rw [← mul_div_assoc, mul_div_mul_left _ _ (pow_ne_zero N ha.ne')]
  apply tendsto_atTop_mono' atTop _ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  apply div_le_div_of_nonneg_right _ (pow_nonneg hs.le N)
  have h := gaussian_remainder_growth_lower (m := m) ht hs.le
  have harg : a * s = 2 * t * s / 9 := by dsimp [a]; ring
  simpa only [C, harg] using h

theorem gaussian_remainder_not_polynomially_bounded {t m : ℝ} (ht : 0 < t) :
    ¬ ∃ K : ℝ, ∃ N : ℕ, ∀ᶠ s : ℝ in atTop, ‖gaussianRemainder t m (s : ℂ)‖ ≤ K * s ^ N := by
  rintro ⟨K, N, hb⟩
  have hg := (gaussian_remainder_exceeds_every_power (m := m) ht N).eventually (eventually_gt_atTop K)
  obtain ⟨s, hs, hnorm, hlarge⟩ := (eventually_gt_atTop (0 : ℝ)).and (hb.and hg) |>.exists
  have hreal : -(gaussianRemainder t m (s : ℂ)).re ≤ ‖gaussianRemainder t m (s : ℂ)‖ :=
    (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  have hquot : -(gaussianRemainder t m (s : ℂ)).re / s ^ N ≤ K :=
    (div_le_iff₀ (pow_pos hs N)).mpr (hreal.trans hnorm)
  exact (not_lt_of_ge hquot) hlarge

end UV
