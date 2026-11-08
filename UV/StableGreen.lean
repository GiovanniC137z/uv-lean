import UV.HeatFourier

/-! The positive massive Green measure is the actual proper-time mixture
of heat Gaussians. Its mass, exponential moments and characteristic
function are computed from that measure. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal InnerProductSpace

namespace UV

def stableGreenTimeMeasure (m : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (Real.exp (-(m ^ 2) * t)))

theorem stableGreenTimeMeasure_integral (m : ℝ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) :
    (∫ t, f t ∂stableGreenTimeMeasure m) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-(m ^ 2) * t) • f t := by
  unfold stableGreenTimeMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le]

theorem stableGreenTimeMeasure_integrable_iff (m : ℝ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) :
    Integrable f (stableGreenTimeMeasure m) ↔
      Integrable (fun t => Real.exp (-(m ^ 2) * t) • f t) (volume.restrict (Ioi (0 : ℝ))) := by
  unfold stableGreenTimeMeasure
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le]

theorem stableGreenTimeMeasure_mass {m : ℝ} (hm : 0 < m) :
    stableGreenTimeMeasure m univ = ENNReal.ofReal (1 / m ^ 2) := by
  unfold stableGreenTimeMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (sq_pos_of_pos hm)) 0)
      (Eventually.of_forall (fun _ => (Real.exp_pos _).le)),
    integral_exp_mul_Ioi (neg_lt_zero.mpr (sq_pos_of_pos hm)) 0]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]

theorem stableGreenTimeMeasure_finite {m : ℝ} (hm : 0 < m) :
    IsFiniteMeasure (stableGreenTimeMeasure m) := by
  constructor
  rw [stableGreenTimeMeasure_mass hm]
  exact ENNReal.ofReal_lt_top

theorem stableGreenTimeMeasure_exponential_integrable (m : ℝ) {b : ℝ} (hb : b < m ^ 2) :
    Integrable (fun t : ℝ => Real.exp (b * t)) (stableGreenTimeMeasure m) := by
  apply (stableGreenTimeMeasure_integrable_iff m _).mpr
  have he : (fun t : ℝ => Real.exp (-(m ^ 2) * t) • Real.exp (b * t)) =
      (fun t : ℝ => Real.exp ((b - m ^ 2) * t)) := by
    funext t
    rw [smul_eq_mul, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact integrableOn_exp_mul_Ioi (sub_neg.mpr hb) 0

theorem stableGreenTimeMeasure_exponential_integral (m : ℝ) {b : ℝ} (hb : b < m ^ 2) :
    (∫ t : ℝ, Real.exp (b * t) ∂stableGreenTimeMeasure m) = 1 / (m ^ 2 - b) := by
  rw [stableGreenTimeMeasure_integral]
  have he : (fun t : ℝ => Real.exp (-(m ^ 2) * t) • Real.exp (b * t)) =
      (fun t : ℝ => Real.exp ((b - m ^ 2) * t)) := by
    funext t
    rw [smul_eq_mul, ← Real.exp_add]
    congr 1
    ring
  rw [he, integral_exp_mul_Ioi (sub_neg.mpr hb) 0]
  simp only [mul_zero, Real.exp_zero]
  rw [show b - m ^ 2 = -(m ^ 2 - b) by ring, neg_div_neg_eq]

theorem stableGreen_sqrt_young (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (z : ScalarMomentum) :
    c * ‖Real.sqrt t • z‖ ≤ ‖z‖ ^ 2 / 8 + 2 * c ^ 2 * t := by
  rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hs : (c * Real.sqrt t) ^ 2 = c ^ 2 * t := by rw [mul_pow, Real.sq_sqrt ht]
  nlinarith [sq_nonneg (‖z‖ - 4 * c * Real.sqrt t)]

theorem stableGreenTimeMeasure_positive (m : ℝ) : ∀ᵐ t ∂stableGreenTimeMeasure m, 0 < t := by
  rw [stableGreenTimeMeasure, ae_withDensity_iff (by fun_prop)]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact fun _ => ht

def stableGreenHeatScale (p : ℝ × ScalarMomentum) : ScalarMomentum := Real.sqrt p.1 • p.2

@[measurability, fun_prop] theorem stableGreenHeatScale_measurable : Measurable stableGreenHeatScale := by
  unfold stableGreenHeatScale
  fun_prop

def stableGreenMeasureOf (m : ℝ) (γ : Measure ScalarMomentum) : Measure ScalarMomentum :=
  Measure.map stableGreenHeatScale ((stableGreenTimeMeasure m).prod γ)

theorem stableGreenMeasureOf_mass (γ : Measure ScalarMomentum) [IsFiniteMeasure γ]
    {m : ℝ} (hm : 0 < m) :
    stableGreenMeasureOf m γ univ = ENNReal.ofReal (1 / m ^ 2) * γ univ := by
  letI := stableGreenTimeMeasure_finite hm
  rw [stableGreenMeasureOf, Measure.map_apply stableGreenHeatScale_measurable MeasurableSet.univ,
    preimage_univ, ← univ_prod_univ, Measure.prod_prod, stableGreenTimeMeasure_mass hm]

theorem stableGreenMeasureOf_finite (γ : Measure ScalarMomentum) [IsFiniteMeasure γ]
    {m : ℝ} (hm : 0 < m) : IsFiniteMeasure (stableGreenMeasureOf m γ) := by
  letI := stableGreenTimeMeasure_finite hm
  unfold stableGreenMeasureOf
  infer_instance

theorem stableGreenMeasureOf_integral (m : ℝ) (γ : Measure ScalarMomentum)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ScalarMomentum → E}
    (hf : StronglyMeasurable f) :
    (∫ x, f x ∂stableGreenMeasureOf m γ) =
      ∫ p, f (stableGreenHeatScale p) ∂(stableGreenTimeMeasure m).prod γ := by
  exact integral_map stableGreenHeatScale_measurable.aemeasurable hf.aestronglyMeasurable

theorem stableGreenMeasureOf_exponential (γ : Measure ScalarMomentum) [IsFiniteMeasure γ]
    {m c : ℝ} (hm : 0 < m) (hc : 2 * c ^ 2 < m ^ 2)
    (hγ : Integrable (fun z : ScalarMomentum => Real.exp (‖z‖ ^ 2 / 8)) γ) :
    Integrable (fun x : ScalarMomentum => Real.exp (c * ‖x‖)) (stableGreenMeasureOf m γ) ∧
      (∫ x : ScalarMomentum, Real.exp (c * ‖x‖) ∂stableGreenMeasureOf m γ) ≤
        (1 / (m ^ 2 - 2 * c ^ 2)) * ∫ z : ScalarMomentum, Real.exp (‖z‖ ^ 2 / 8) ∂γ := by
  letI := stableGreenTimeMeasure_finite hm
  have hmajorant := (stableGreenTimeMeasure_exponential_integrable m hc).mul_prod hγ
  have hbound : ∀ᵐ p : ℝ × ScalarMomentum ∂(stableGreenTimeMeasure m).prod γ,
      ‖Real.exp (c * ‖stableGreenHeatScale p‖)‖ ≤
        Real.exp (2 * c ^ 2 * p.1) * Real.exp (‖p.2‖ ^ 2 / 8) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst).ae (stableGreenTimeMeasure_positive m)] with p hp
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    exact (stableGreen_sqrt_young c hp.le p.2).trans_eq (by ring)
  have hi : Integrable (fun p : ℝ × ScalarMomentum => Real.exp (c * ‖stableGreenHeatScale p‖))
      ((stableGreenTimeMeasure m).prod γ) := hmajorant.mono' (by fun_prop) hbound
  refine ⟨(integrable_map_measure (by fun_prop) stableGreenHeatScale_measurable.aemeasurable).mpr hi, ?_⟩
  rw [stableGreenMeasureOf_integral _ _
    (by fun_prop : Continuous (fun x : ScalarMomentum => Real.exp (c * ‖x‖))).stronglyMeasurable]
  calc
    _ ≤ ∫ p : ℝ × ScalarMomentum, Real.exp (2 * c ^ 2 * p.1) * Real.exp (‖p.2‖ ^ 2 / 8)
        ∂(stableGreenTimeMeasure m).prod γ :=
      integral_mono_ae hi hmajorant (hbound.mono fun p hp => (le_abs_self _).trans hp)
    _ = _ := by
      rw [integral_prod_mul (fun t : ℝ => Real.exp (2 * c ^ 2 * t))
        (fun z : ScalarMomentum => Real.exp (‖z‖ ^ 2 / 8)),
        stableGreenTimeMeasure_exponential_integral m hc]

def stableGreenWave (q x : ScalarMomentum) : ℂ :=
  Complex.exp (Complex.I * (inner ℝ q x : ℂ))

@[simp] theorem stableGreenWave_norm (q x : ScalarMomentum) : ‖stableGreenWave q x‖ = 1 := by
  unfold stableGreenWave
  rw [Complex.norm_exp]
  simp

theorem stableGreenMeasureOf_characteristic (γ : Measure ScalarMomentum) [IsFiniteMeasure γ]
    (hγ : ∀ q : ScalarMomentum, (∫ z, stableGreenWave q z ∂γ) = (Real.exp (-‖q‖ ^ 2) : ℂ))
    {m : ℝ} (hm : 0 < m) (q : ScalarMomentum) :
    (∫ x, stableGreenWave q x ∂stableGreenMeasureOf m γ) =
      ((1 / (‖q‖ ^ 2 + m ^ 2) : ℝ) : ℂ) := by
  letI := stableGreenTimeMeasure_finite hm
  have hi : Integrable (fun p : ℝ × ScalarMomentum => stableGreenWave q (stableGreenHeatScale p))
      ((stableGreenTimeMeasure m).prod γ) := by
    apply (integrable_const (μ := (stableGreenTimeMeasure m).prod γ) (1 : ℝ)).mono'
      (by unfold stableGreenWave stableGreenHeatScale; fun_prop)
    filter_upwards with p
    rw [stableGreenWave_norm]
  rw [stableGreenMeasureOf_integral _ _
    (by unfold stableGreenWave; fun_prop : Continuous (stableGreenWave q)).stronglyMeasurable,
    integral_prod _ hi]
  have he : (fun t : ℝ => ∫ z, stableGreenWave q (stableGreenHeatScale (t, z)) ∂γ) =ᵐ[
      stableGreenTimeMeasure m] (fun t => (Real.exp (-t * ‖q‖ ^ 2) : ℂ)) := by
    filter_upwards [stableGreenTimeMeasure_positive m] with t ht
    have hw : (fun z : ScalarMomentum => stableGreenWave q (stableGreenHeatScale (t, z))) =
        (fun z => stableGreenWave (Real.sqrt t • q) z) := by
      funext z
      unfold stableGreenWave stableGreenHeatScale
      simp only [inner_smul_right, real_inner_smul_left]
    rw [hw, hγ]
    simp only [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt ht.le, neg_mul]
  rw [integral_congr_ae he, integral_complex_ofReal]
  have hlap := stableGreenTimeMeasure_exponential_integral m (b := -‖q‖ ^ 2)
    (by nlinarith [sq_nonneg ‖q‖, sq_pos_of_pos hm])
  have hd : m ^ 2 - -‖q‖ ^ 2 = ‖q‖ ^ 2 + m ^ 2 := by ring
  rw [hd] at hlap
  congr 1
  convert hlap using 1
  congr 1
  funext t
  congr 1
  ring

def stableGreenGaussianTilt (z : ScalarMomentum) : ℝ :=
  (Real.exp (-‖z‖ ^ 2 / 4) / (16 * Real.pi ^ 2)) * Real.exp (‖z‖ ^ 2 / 8)

theorem stableGreenGaussianTilt_eq (z : ScalarMomentum) :
    stableGreenGaussianTilt z = (1 / (16 * Real.pi ^ 2)) *
      Real.exp (-(1 / 8 : ℝ) * ‖z‖ ^ 2) := by
  unfold stableGreenGaussianTilt
  rw [div_mul_eq_mul_div, ← Real.exp_add,
    show -‖z‖ ^ 2 / 4 + ‖z‖ ^ 2 / 8 = -(1 / 8 : ℝ) * ‖z‖ ^ 2 by ring]
  ring

theorem stableGreenGaussianTilt_integrable : Integrable stableGreenGaussianTilt := by
  change Integrable (fun z : ScalarMomentum => stableGreenGaussianTilt z)
  simp_rw [stableGreenGaussianTilt_eq]
  exact (scalar_gaussian_integrable (by norm_num : 0 < (1 / 8 : ℝ))).const_mul _

theorem stableGreenGaussianTilt_integral : (∫ z : ScalarMomentum, stableGreenGaussianTilt z) = 4 := by
  simp_rw [stableGreenGaussianTilt_eq]
  rw [integral_const_mul, scalar_gaussian_integral (by norm_num : 0 < (1 / 8 : ℝ))]
  field_simp
  ring

theorem stableUnitGaussian_norm_square_tilt_integrable :
    Integrable (fun z : ScalarMomentum => Real.exp (‖z‖ ^ 2 / 8)) stableUnitGaussian := by
  unfold stableUnitGaussian
  rw [integrable_withDensity_iff_integrable_smul' (stableHeatKernel_measurable 1).ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (stableHeatKernel_nonneg 1 _), smul_eq_mul]
  simpa only [stableHeatKernel, mul_one, one_pow, stableGreenGaussianTilt] using
    stableGreenGaussianTilt_integrable

theorem stableUnitGaussian_norm_square_tilt_integral :
    (∫ z : ScalarMomentum, Real.exp (‖z‖ ^ 2 / 8) ∂stableUnitGaussian) = 4 := by
  rw [stableUnitGaussian_integral]
  simpa only [stableHeatKernel, mul_one, one_pow, smul_eq_mul, stableGreenGaussianTilt] using
    stableGreenGaussianTilt_integral

def stableGreenMeasure (m : ℝ) : Measure ScalarMomentum :=
  stableGreenMeasureOf m stableUnitGaussian

theorem stableGreenMeasure_mass {m : ℝ} (hm : 0 < m) :
    stableGreenMeasure m univ = ENNReal.ofReal (1 / m ^ 2) := by
  rw [stableGreenMeasure, stableGreenMeasureOf_mass _ hm, measure_univ, mul_one]

theorem stableGreenMeasure_real_mass {m : ℝ} (hm : 0 < m) :
    (stableGreenMeasure m univ).toReal = 1 / m ^ 2 := by
  rw [stableGreenMeasure_mass hm, ENNReal.toReal_ofReal (by positivity)]

theorem stableGreenMeasure_finite {m : ℝ} (hm : 0 < m) : IsFiniteMeasure (stableGreenMeasure m) :=
  stableGreenMeasureOf_finite _ hm

theorem stableGreenMeasure_ne_zero {m : ℝ} (hm : 0 < m) : stableGreenMeasure m ≠ 0 := by
  intro hz
  have he := stableGreenMeasure_mass hm
  rw [hz] at he
  change 0 = ENNReal.ofReal (1 / m ^ 2) at he
  exact (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity : 0 < 1 / m ^ 2))) he.symm

theorem stableGreenMeasure_exponential_integrable {m c : ℝ}
    (hm : 0 < m) (hc : 2 * c ^ 2 < m ^ 2) :
    Integrable (fun x : ScalarMomentum => Real.exp (c * ‖x‖)) (stableGreenMeasure m) :=
  (stableGreenMeasureOf_exponential _ hm hc stableUnitGaussian_norm_square_tilt_integrable).1

theorem stableGreenMeasure_exponential_integral_le {m c : ℝ}
    (hm : 0 < m) (hc : 2 * c ^ 2 < m ^ 2) :
    (∫ x : ScalarMomentum, Real.exp (c * ‖x‖) ∂stableGreenMeasure m) ≤
      4 / (m ^ 2 - 2 * c ^ 2) := by
  have h := (stableGreenMeasureOf_exponential _ hm hc stableUnitGaussian_norm_square_tilt_integrable).2
  rw [stableUnitGaussian_norm_square_tilt_integral] at h
  convert h using 1
  ring

theorem stableGreenMeasure_has_exponential_moment {m : ℝ} (hm : 0 < m) :
    ∃ c > 0, Integrable (fun x : ScalarMomentum => Real.exp (c * ‖x‖)) (stableGreenMeasure m) := by
  refine ⟨m / 2, by positivity, stableGreenMeasure_exponential_integrable hm ?_⟩
  nlinarith [sq_pos_of_pos hm]

theorem stableGreenMeasure_characteristic {m : ℝ} (hm : 0 < m) (q : ScalarMomentum) :
    (∫ x, stableFourierPhase q x ∂stableGreenMeasure m) =
      ((1 / (‖q‖ ^ 2 + m ^ 2) : ℝ) : ℂ) := by
  apply stableGreenMeasureOf_characteristic stableUnitGaussian _ hm
  intro y
  exact stableUnitGaussian_characteristic y

end UV
