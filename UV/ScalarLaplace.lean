import UV.ScalarTube
import UV.ScalarGaussian
import UV.HeatMeasure
import UV.MassiveNeighbourhood
import UV.JointMajorant
import UV.PositiveLaplace

/-! The proper-time positive measure of the literal scalar bubble.
Source: prop:OQED-scalar-CM-enclosure. Heat proper time already includes
the exact pushforward τ ↦ a²τ from `oqedHeatMeasure`. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace UV

abbrev ScalarLineTime := ℝ × ℝ
abbrev ScalarTwoTime := ScalarLineTime × ScalarLineTime

def scalarProperLineBase (ρ : Measure ℝ) : Measure ScalarLineTime :=
  ρ.prod (volume.restrict (Ioi 0))

def scalarProperBase (ρ : Measure ℝ) : Measure ScalarTwoTime :=
  (scalarProperLineBase ρ).prod (scalarProperLineBase ρ)

instance scalarProperLineBase_sigmaFinite (ρ : Measure ℝ) [SigmaFinite ρ] :
    SigmaFinite (scalarProperLineBase ρ) := by unfold scalarProperLineBase; infer_instance

instance scalarProperBase_sigmaFinite (ρ : Measure ℝ) [SigmaFinite ρ] :
    SigmaFinite (scalarProperBase ρ) := by unfold scalarProperBase; infer_instance

def scalarProperWidth (t : ScalarLineTime) : ℝ := t.1 + t.2

def scalarProperLambda (p : ScalarTwoTime) : ℝ :=
  scalarProperWidth p.1 * scalarProperWidth p.2 / (scalarProperWidth p.1 + scalarProperWidth p.2)

def scalarProperDensity (m : ℝ) (p : ScalarTwoTime) : ℝ :=
  Real.exp (-(m ^ 2) * (p.1.2 + p.2.2)) /
    (16 * Real.pi ^ 2 * (scalarProperWidth p.1 + scalarProperWidth p.2) ^ 2)

def scalarProperWeightedMeasure (ρ : Measure ℝ) (m : ℝ) : Measure ScalarTwoTime :=
  (scalarProperBase ρ).withDensity (fun p => ENNReal.ofReal (scalarProperDensity m p))

def scalarLaplaceMeasure (ρ : Measure ℝ) (m : ℝ) : Measure ℝ :=
  Measure.map scalarProperLambda (scalarProperWeightedMeasure ρ m)

def oqedScalarLaplaceMeasure (a M m : ℝ) : Measure ℝ :=
  scalarLaplaceMeasure (oqedHeatMeasure a M) m

@[measurability, fun_prop] theorem scalarProperLambda_measurable : Measurable scalarProperLambda := by
  unfold scalarProperLambda scalarProperWidth
  fun_prop

@[measurability, fun_prop] theorem scalarProperDensity_measurable (m : ℝ) :
    Measurable (scalarProperDensity m) := by
  unfold scalarProperDensity scalarProperWidth
  fun_prop

theorem scalarProperDensity_nonneg (m : ℝ) (p : ScalarTwoTime) : 0 ≤ scalarProperDensity m p := by
  unfold scalarProperDensity
  positivity

theorem scalarProperLambda_pos {p : ScalarTwoTime}
    (h₁ : 0 < scalarProperWidth p.1) (h₂ : 0 < scalarProperWidth p.2) : 0 < scalarProperLambda p :=
  div_pos (mul_pos h₁ h₂) (add_pos h₁ h₂)

theorem scalarProperLambda_upper {p : ScalarTwoTime}
    (h : 0 < scalarProperWidth p.1 + scalarProperWidth p.2) :
    scalarProperLambda p ≤ (scalarProperWidth p.1 + scalarProperWidth p.2) / 4 := by
  unfold scalarProperLambda
  apply (div_le_iff₀ h).mpr
  nlinarith [sq_nonneg (scalarProperWidth p.1 - scalarProperWidth p.2)]

theorem scalarProperLineBase_positive (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0) :
    ∀ᵐ t ∂scalarProperLineBase ρ, 0 < t.1 ∧ 0 < t.2 := by
  have hs : MeasurableSet {t : ScalarLineTime | 0 < t.1 ∧ 0 < t.2} :=
    ((isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_const continuous_snd)).measurableSet
  rw [scalarProperLineBase, Measure.ae_prod_iff_ae_ae hs]
  filter_upwards [ae_positive_of_support_no_atom ρ hneg hzero] with τ hτ
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
  exact ⟨hτ, hα⟩

theorem scalarProperBase_positive (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0) :
    ∀ᵐ p ∂scalarProperBase ρ, (0 < p.1.1 ∧ 0 < p.1.2) ∧ (0 < p.2.1 ∧ 0 < p.2.2) := by
  have hs : MeasurableSet {p : ScalarTwoTime | (0 < p.1.1 ∧ 0 < p.1.2) ∧ (0 < p.2.1 ∧ 0 < p.2.2)} :=
    (((isOpen_lt continuous_const (continuous_fst.comp continuous_fst)).inter
      (isOpen_lt continuous_const (continuous_snd.comp continuous_fst))).inter
      ((isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).inter
        (isOpen_lt continuous_const (continuous_snd.comp continuous_snd)))).measurableSet
  rw [scalarProperBase, Measure.ae_prod_iff_ae_ae hs]
  filter_upwards [scalarProperLineBase_positive ρ hneg hzero] with t₁ ht₁
  filter_upwards [scalarProperLineBase_positive ρ hneg hzero] with t₂ ht₂
  exact ⟨ht₁, ht₂⟩

theorem positive_inverse_square_integrable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0) (hM : inverseMoment ρ 2 < ⊤) :
    Integrable (fun τ : ℝ => (τ ^ 2)⁻¹) ρ := by
  have hp := ae_positive_of_support_no_atom ρ hneg hzero
  have hr : ρ.restrict (Ioi 0) = ρ := Measure.restrict_eq_self_of_ae_mem hp
  unfold inverseMoment at hM
  rw [hr] at hM
  have hi : (∫⁻ τ : ℝ, ENNReal.ofReal ((τ ^ 2)⁻¹) ∂ρ) < ⊤ := by
    convert hM using 1
    apply lintegral_congr_ae
    filter_upwards [hp] with τ hτ
    rw [Real.rpow_neg hτ.le, Real.rpow_two]
  refine ⟨by apply Measurable.aestronglyMeasurable; fun_prop, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun τ : ℝ => by positivity))).mpr hi

theorem scalarProperDensity_integrable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0) (hM : inverseMoment ρ 2 < ⊤)
    {m : ℝ} (hm : 0 < m) : Integrable (scalarProperDensity m) (scalarProperBase ρ) := by
  have hα : IntegrableOn (fun α : ℝ => Real.exp (-(m ^ 2) * α)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (sq_pos_of_pos hm)) 0
  have h₁ : Integrable (fun t : ScalarLineTime => (t.1 ^ 2)⁻¹ * Real.exp (-(m ^ 2) * t.2))
      (scalarProperLineBase ρ) := (positive_inverse_square_integrable ρ hneg hzero hM).mul_prod hα
  have h₂ : Integrable (fun t : ScalarLineTime => Real.exp (-(m ^ 2) * t.2))
      (scalarProperLineBase ρ) := by
    simpa only [one_mul] using (integrable_const (μ := ρ) (1 : ℝ)).mul_prod hα
  apply ((h₁.mul_prod h₂).const_mul ((16 * Real.pi ^ 2)⁻¹)).mono'
  · exact (scalarProperDensity_measurable m).aestronglyMeasurable
  · filter_upwards [scalarProperBase_positive ρ hneg hzero] with p hp
    rw [Real.norm_of_nonneg (scalarProperDensity_nonneg m p)]
    have ht : 0 < p.1.1 := hp.1.1
    have hs : p.1.1 ≤ scalarProperWidth p.1 + scalarProperWidth p.2 := by
      unfold scalarProperWidth
      linarith [hp.1.2, hp.2.1, hp.2.2]
    unfold scalarProperDensity
    calc
      _ ≤ Real.exp (-(m ^ 2) * (p.1.2 + p.2.2)) / (16 * Real.pi ^ 2 * p.1.1 ^ 2) := by
        apply div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.le hs 2) (by positivity)
      _ = _ := by
        rw [show -(m ^ 2) * (p.1.2 + p.2.2) = -(m ^ 2) * p.1.2 + -(m ^ 2) * p.2.2 by ring,
          Real.exp_add]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring

def scalarProperLineFactor (m u : ℝ) (t : ScalarLineTime) : ℝ :=
  Real.exp (-t.1 * u) * (Real.exp (-(m ^ 2) * t.2) * Real.exp (-t.2 * u))

theorem massiveSchwingerCovariance_eq {u m : ℝ} (hu : 0 ≤ u) (hm : 0 < m) :
    schwingerCovariance (fun α => Real.exp (-(m ^ 2) * α)) u = 1 / (u + m ^ 2) := by
  unfold schwingerCovariance
  have he : (fun α : ℝ => Real.exp (-(m ^ 2) * α) * Real.exp (-α * u)) =
      (fun α => Real.exp (-(u + m ^ 2) * α)) := by
    funext α
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, integral_exp_mul_Ioi (by have := sq_pos_of_pos hm; linarith) 0]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]

theorem scalarProperLineFactor_integrable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0) {u m : ℝ} (hu : 0 ≤ u) (hm : 0 < m) :
    Integrable (scalarProperLineFactor m u) (scalarProperLineBase ρ) := by
  have hE := integrableOn_exp_mul_Ioi (a := -(m ^ 2)) (neg_lt_zero.mpr (sq_pos_of_pos hm)) 0
  simpa only [scalarProperLineFactor, scalarProperLineBase, one_pow, one_mul] using
    schwinger_laplace_parameter_integrable ρ hneg hzero hE
      (fun α _ => (Real.exp_pos (-(m ^ 2) * α)).le) (a := 1) hu

theorem scalarProperLineFactor_integral (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {u m : ℝ} (hu : 0 ≤ u) (hm : 0 < m) :
    (∫ t, scalarProperLineFactor m u t ∂scalarProperLineBase ρ) = laplace ρ u / (u + m ^ 2) := by
  have h := schwinger_laplace_parameter_integral ρ (fun α => Real.exp (-(m ^ 2) * α)) 1 u
  simpa only [one_pow, one_mul, massiveSchwingerCovariance_eq hu hm, div_eq_mul_inv,
    scalarProperLineFactor, scalarProperLineBase] using h

def scalarProperJoint (m : ℝ) (P : ScalarMomentum) (p : ScalarTwoTime) (q : ScalarMomentum) : ℝ :=
  (2 * Real.pi) ^ (-4 : ℤ) *
    (scalarProperLineFactor m (‖q‖ ^ 2) p.1 * scalarProperLineFactor m (‖q + P‖ ^ 2) p.2)

theorem scalarProperJoint_factor (m : ℝ) (P : ScalarMomentum) (p : ScalarTwoTime) (q : ScalarMomentum) :
    scalarProperJoint m P p q = (2 * Real.pi) ^ (-4 : ℤ) *
      Real.exp (-(m ^ 2) * (p.1.2 + p.2.2)) *
        Real.exp (-scalarProperWidth p.1 * ‖q‖ ^ 2 - scalarProperWidth p.2 * ‖q + P‖ ^ 2) := by
  unfold scalarProperJoint scalarProperLineFactor scalarProperWidth
  have he : -(m ^ 2) * (p.1.2 + p.2.2) +
      (-(p.1.1 + p.1.2) * ‖q‖ ^ 2 - (p.2.1 + p.2.2) * ‖q + P‖ ^ 2) =
        (-p.1.1 * ‖q‖ ^ 2) + (-(m ^ 2) * p.1.2) + (-p.1.2 * ‖q‖ ^ 2) +
          (-p.2.1 * ‖q + P‖ ^ 2) + (-(m ^ 2) * p.2.2) + (-p.2.2 * ‖q + P‖ ^ 2) := by ring
  rw [mul_assoc ((2 * Real.pi) ^ (-4 : ℤ))]
  conv_rhs => rw [← Real.exp_add, he]
  simp only [Real.exp_add]
  ring

theorem scalarProperJoint_nonneg (m : ℝ) (P : ScalarMomentum) (p : ScalarTwoTime) (q : ScalarMomentum) :
    0 ≤ scalarProperJoint m P p q := by
  unfold scalarProperJoint scalarProperLineFactor
  positivity

theorem scalarProperJoint_gaussian_integral (m : ℝ) (P : ScalarMomentum) {p : ScalarTwoTime}
    (hp : 0 < scalarProperWidth p.1 + scalarProperWidth p.2) :
    (∫ q, scalarProperJoint m P p q) =
      scalarProperDensity m p * Real.exp (-scalarProperLambda p * ‖P‖ ^ 2) := by
  simp_rw [scalarProperJoint_factor]
  rw [integral_const_mul, two_line_gaussian_integral hp P]
  unfold scalarProperDensity scalarProperLambda
  rw [zpow_neg, zpow_ofNat]
  field_simp [Real.pi_ne_zero, hp.ne']
  ring

theorem scalarProperWidths_positive (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0) :
    ∀ᵐ p ∂scalarProperBase ρ, 0 < scalarProperWidth p.1 ∧ 0 < scalarProperWidth p.2 := by
  filter_upwards [scalarProperBase_positive ρ hneg hzero] with p hp
  exact ⟨add_pos hp.1.1 hp.1.2, add_pos hp.2.1 hp.2.2⟩

theorem scalarProperWeightedMeasure_finite (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0) (hM : inverseMoment ρ 2 < ⊤)
    {m : ℝ} (hm : 0 < m) : IsFiniteMeasure (scalarProperWeightedMeasure ρ m) := by
  unfold scalarProperWeightedMeasure
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal (scalarProperDensity_integrable ρ hneg hzero hM hm)
    (Eventually.of_forall (scalarProperDensity_nonneg m))]
  exact ENNReal.ofReal_ne_top

theorem scalarLaplaceMeasure_finite (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0) (hM : inverseMoment ρ 2 < ⊤)
    {m : ℝ} (hm : 0 < m) : IsFiniteMeasure (scalarLaplaceMeasure ρ m) := by
  letI := scalarProperWeightedMeasure_finite ρ hneg hzero hM hm
  unfold scalarLaplaceMeasure
  infer_instance

theorem scalarLaplaceMeasure_positive (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0) (m : ℝ) :
    ∀ᵐ ell ∂scalarLaplaceMeasure ρ m, 0 < ell := by
  rw [ae_iff]
  unfold scalarLaplaceMeasure
  have hs : MeasurableSet {ell : ℝ | ¬0 < ell} := by
    simpa only [not_lt] using (measurableSet_Iic : MeasurableSet (Iic (0 : ℝ)))
  rw [Measure.map_apply scalarProperLambda_measurable hs]
  apply withDensity_absolutelyContinuous
  change (scalarProperBase ρ) {p | ¬0 < scalarProperLambda p} = 0
  rw [← ae_iff]
  filter_upwards [scalarProperWidths_positive ρ hneg hzero] with p hp
  exact scalarProperLambda_pos hp.1 hp.2

theorem scalarLaplaceMeasure_integral (ρ : Measure ℝ) (m : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ ell, f ell ∂scalarLaplaceMeasure ρ m) =
      ∫ p, scalarProperDensity m p * f (scalarProperLambda p) ∂scalarProperBase ρ := by
  unfold scalarLaplaceMeasure scalarProperWeightedMeasure
  rw [integral_map scalarProperLambda_measurable.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (scalarProperDensity_measurable m).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (scalarProperDensity_nonneg _ _), smul_eq_mul]

theorem scalarLaplaceMeasure_integrable_iff (ρ : Measure ℝ) (m : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    Integrable f (scalarLaplaceMeasure ρ m) ↔
      Integrable (fun p => scalarProperDensity m p * f (scalarProperLambda p)) (scalarProperBase ρ) := by
  unfold scalarLaplaceMeasure scalarProperWeightedMeasure
  rw [integrable_map_measure hf.aestronglyMeasurable scalarProperLambda_measurable.aemeasurable,
    integrable_withDensity_iff_integrable_smul' (scalarProperDensity_measurable m).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (scalarProperDensity_nonneg _ _), smul_eq_mul, Function.comp_def]

theorem scalarProperJoint_integrable_loop (m : ℝ) (P : ScalarMomentum) {p : ScalarTwoTime}
    (hp : 0 < scalarProperWidth p.1 + scalarProperWidth p.2) :
    Integrable (scalarProperJoint m P p) := by
  change Integrable (fun q => scalarProperJoint m P p q)
  simp_rw [scalarProperJoint_factor]
  exact (two_line_gaussian_integrable hp P).const_mul
    ((2 * Real.pi) ^ (-4 : ℤ) * Real.exp (-(m ^ 2) * (p.1.2 + p.2.2)))

theorem scalarProperJoint_integrable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0) (hM : inverseMoment ρ 2 < ⊤)
    {m : ℝ} (hm : 0 < m) (P : ScalarMomentum) :
    Integrable (fun z : ScalarTwoTime × ScalarMomentum => scalarProperJoint m P z.1 z.2)
      ((scalarProperBase ρ).prod volume) := by
  have hmeas : StronglyMeasurable (fun z : ScalarTwoTime × ScalarMomentum => scalarProperJoint m P z.1 z.2) := by
    unfold scalarProperJoint scalarProperLineFactor
    fun_prop
  apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [scalarProperWidths_positive ρ hneg hzero] with p hp
    exact scalarProperJoint_integrable_loop m P (add_pos hp.1 hp.2)
  · apply (scalarProperDensity_integrable ρ hneg hzero hM hm).mono'
    · exact hmeas.norm.integral_prod_right.aestronglyMeasurable
    · filter_upwards [scalarProperWidths_positive ρ hneg hzero] with p hp
      have hnorm : (fun q => ‖scalarProperJoint m P p q‖) = scalarProperJoint m P p :=
        funext (fun q => Real.norm_of_nonneg (scalarProperJoint_nonneg m P p q))
      rw [hnorm, scalarProperJoint_gaussian_integral m P (add_pos hp.1 hp.2),
        Real.norm_of_nonneg (mul_nonneg (scalarProperDensity_nonneg _ _) (Real.exp_pos _).le)]
      apply mul_le_of_le_one_right (scalarProperDensity_nonneg _ _)
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (scalarProperLambda_pos hp.1 hp.2).le) (sq_nonneg ‖P‖)

theorem scalarProperJoint_parameter_integral (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {m : ℝ} (hm : 0 < m) (P q : ScalarMomentum) :
    (∫ p, scalarProperJoint m P p q ∂scalarProperBase ρ) =
      (2 * Real.pi) ^ (-4 : ℤ) *
        (laplace ρ (‖q‖ ^ 2) / (‖q‖ ^ 2 + m ^ 2) *
          (laplace ρ (‖q + P‖ ^ 2) / (‖q + P‖ ^ 2 + m ^ 2))) := by
  unfold scalarProperJoint scalarProperBase
  rw [integral_const_mul, integral_prod_mul, scalarProperLineFactor_integral ρ (sq_nonneg _) hm,
    scalarProperLineFactor_integral ρ (sq_nonneg _) hm]

def scalarMeasureBubble (ρ : Measure ℝ) (m : ℝ) (P : ScalarMomentum) : ℝ :=
  (2 * Real.pi) ^ (-4 : ℤ) * ∫ q,
    (laplace ρ (‖q‖ ^ 2) / (‖q‖ ^ 2 + m ^ 2)) *
      (laplace ρ (‖q + P‖ ^ 2) / (‖q + P‖ ^ 2 + m ^ 2))

/-- The positive proper-time representation is obtained by absolute Fubini
and actual four-dimensional Gaussian integration. -/
theorem scalarMeasureBubble_laplace (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0) (hM : inverseMoment ρ 2 < ⊤)
    {m : ℝ} (hm : 0 < m) (P : ScalarMomentum) :
    scalarMeasureBubble ρ m P =
      ∫ ell, Real.exp (-ell * ‖P‖ ^ 2) ∂scalarLaplaceMeasure ρ m := by
  rw [scalarLaplaceMeasure_integral ρ m (by fun_prop)]
  have hJ := scalarProperJoint_integrable ρ hneg hzero hM hm P
  have he : (∫ p, scalarProperDensity m p * Real.exp (-scalarProperLambda p * ‖P‖ ^ 2)
      ∂scalarProperBase ρ) = ∫ p, (∫ q, scalarProperJoint m P p q) ∂scalarProperBase ρ := by
    apply integral_congr_ae
    filter_upwards [scalarProperWidths_positive ρ hneg hzero] with p hp
    exact (scalarProperJoint_gaussian_integral m P (add_pos hp.1 hp.2)).symm
  rw [he, integral_integral_swap hJ]
  simp_rw [scalarProperJoint_parameter_integral ρ hm P]
  rw [integral_const_mul]
  rfl

theorem oqedHeatMeasure_no_negative {a : ℝ} (ha : 0 < a) (M : ℝ) :
    oqedHeatMeasure a M (Iio 0) = 0 :=
  measure_mono_null Iio_subset_Iic_self (oqedHeatMeasure_nonnegative_support ha M)

theorem scalarMeasureBubble_oqed {a : ℝ} (ha : 0 ≤ a) (M m : ℝ) (P : ScalarMomentum) :
    scalarMeasureBubble (oqedHeatMeasure a M) m P = scalarBubble a M m P := by
  unfold scalarMeasureBubble scalarBubble scalarBubbleIntegrand scalarCovariance
  simp_rw [oqedHeatMeasure_laplace ha (sq_nonneg _) M]

theorem scalarBubble_positive_laplace {a M m : ℝ} (ha : 0 < a) (hm : 0 < m) (P : ScalarMomentum) :
    scalarBubble a M m P =
      ∫ ell, Real.exp (-ell * ‖P‖ ^ 2) ∂oqedScalarLaplaceMeasure a M m := by
  rw [← scalarMeasureBubble_oqed ha.le M m P]
  exact scalarMeasureBubble_laplace (oqedHeatMeasure a M) (oqedHeatMeasure_no_negative ha M)
    (oqedHeatMeasure_no_atom_zero ha M) (oqedHeatMeasure_inverseMoment_finite ha M (by norm_num)) hm P

theorem oqedScalarLaplaceMeasure_finite {a M m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    IsFiniteMeasure (oqedScalarLaplaceMeasure a M m) :=
  scalarLaplaceMeasure_finite (oqedHeatMeasure a M) (oqedHeatMeasure_no_negative ha M)
    (oqedHeatMeasure_no_atom_zero ha M) (oqedHeatMeasure_inverseMoment_finite ha M (by norm_num)) hm

theorem oqedScalarLaplaceMeasure_positive {a M : ℝ} (ha : 0 < a) (m : ℝ) :
    ∀ᵐ ell ∂oqedScalarLaplaceMeasure a M m, 0 < ell :=
  scalarLaplaceMeasure_positive (oqedHeatMeasure a M) (oqedHeatMeasure_no_negative ha M)
    (oqedHeatMeasure_no_atom_zero ha M) m

theorem oqedScalarLaplaceMeasure_mass {a M m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    (oqedScalarLaplaceMeasure a M m univ).toReal = scalarBubble a M m 0 := by
  have he := scalarBubble_positive_laplace (M := M) ha hm (0 : ScalarMomentum)
  simpa using he.symm

theorem oqedScalarLaplaceMeasure_ne_zero {a M m : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M) (hm : 0 < m) : oqedScalarLaplaceMeasure a M m ≠ 0 := by
  have hb : 0 < scalarBubble a M m 0 := by
    simpa using scalarBubble_strict_complete_monotonicity ha hM hm 0 (0 : ScalarMomentum)
  intro hz
  have he := oqedScalarLaplaceMeasure_mass (M := M) ha hm
  rw [hz] at he
  simp only [Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero] at he
  linarith

theorem scalarInvariantBubble_positive_laplace_real {a M m w : ℝ}
    (ha : 0 < a) (hm : 0 < m) (hw : 0 ≤ w) :
    scalarInvariantBubble a M m (w : ℂ) =
      (((∫ ell, Real.exp (-ell * w) ∂oqedScalarLaplaceMeasure a M m) : ℝ) : ℂ) := by
  let P := scalarAxis (Real.sqrt w)
  have hn : ‖P‖ ^ 2 = w := by
    rw [show P = scalarAxis (Real.sqrt w) from rfl, scalarAxis_norm, abs_of_nonneg (Real.sqrt_nonneg w), Real.sq_sqrt hw]
  have he := scalarInvariantBubble_ofReal_momentum a M m P
  rw [hn, scalarBubble_positive_laplace ha hm P] at he
  simpa only [hn] using he

theorem oqedHeatMeasure_exponentialMoment_finite (a M : ℝ) {b : ℝ} (hb : b ≤ M ^ 2) :
    (∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (b * t)) ∂oqedHeatMeasure a M) < ⊤ := by
  unfold oqedHeatMeasure
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  have hc : b * a ^ 2 ≤ (a * M) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hb (sq_nonneg a)]
  convert oqedExponentialMoment_finite (a * M) hc using 1
  apply lintegral_congr
  intro t
  congr 2
  ring

theorem scalarProperBase_massiveTilt (ρ : Measure ℝ) [SigmaFinite ρ] (lam : ℝ) :
    scalarProperBase (massiveTilt ρ lam) = (scalarProperBase ρ).withDensity
      (fun p => ENNReal.ofReal (Real.exp (lam * (p.1.1 + p.2.1)))) := by
  have hm : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (lam * t))) := by fun_prop
  have hmLine : Measurable (fun t : ScalarLineTime => ENNReal.ofReal (Real.exp (lam * t.1))) := by fun_prop
  unfold scalarProperBase scalarProperLineBase massiveTilt
  simp_rw [prod_withDensity_left hm]
  rw [prod_withDensity₀ hmLine.aemeasurable hmLine.aemeasurable]
  apply withDensity_congr_ae
  filter_upwards with p
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

theorem scalarProperDensity_tilt_identity {m m' lam : ℝ} (hm' : m' ^ 2 = m ^ 2 - lam) (p : ScalarTwoTime) :
    Real.exp (lam * (p.1.1 + p.2.1)) * scalarProperDensity m' p =
      scalarProperDensity m p * Real.exp (lam * (scalarProperWidth p.1 + scalarProperWidth p.2)) := by
  unfold scalarProperDensity scalarProperWidth
  rw [hm']
  have he : lam * (p.1.1 + p.2.1) + (-(m ^ 2 - lam) * (p.1.2 + p.2.2)) =
      -(m ^ 2) * (p.1.2 + p.2.2) + lam * ((p.1.1 + p.1.2) + (p.2.1 + p.2.2)) := by ring
  calc
    _ = Real.exp (lam * (p.1.1 + p.2.1) + (-(m ^ 2 - lam) * (p.1.2 + p.2.2))) /
        (16 * Real.pi ^ 2 * ((p.1.1 + p.1.2) + (p.2.1 + p.2.2)) ^ 2) := by rw [Real.exp_add]; ring
    _ = _ := by rw [he, Real.exp_add]; ring

theorem scalarProperDensity_tilt_integrable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0) {lam m' : ℝ}
    [IsFiniteMeasure (massiveTilt ρ lam)] (hInv : inverseMoment (massiveTilt ρ lam) 2 < ⊤)
    (hm' : 0 < m') : Integrable
      (fun p => Real.exp (lam * (p.1.1 + p.2.1)) * scalarProperDensity m' p) (scalarProperBase ρ) := by
  have hi := scalarProperDensity_integrable (massiveTilt ρ lam)
    (massiveTilt_no_negative ρ lam hneg) (massiveTilt_no_atom ρ lam hzero) hInv hm'
  rw [scalarProperBase_massiveTilt] at hi
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop : Measurable
    (fun p : ScalarTwoTime => ENNReal.ofReal (Real.exp (lam * (p.1.1 + p.2.1)))))
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hi
  simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul] using hi

theorem scalarLaplaceMeasure_exponential_integrable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hneg : ρ (Iio 0) = 0) (hzero : ρ {0} = 0) {s m : ℝ}
    (hs : 0 < s) (_hm : 0 < m) (hsm : s < 4 * m ^ 2)
    [IsFiniteMeasure (massiveTilt ρ (s / 4))]
    (hInv : inverseMoment (massiveTilt ρ (s / 4)) 2 < ⊤) :
    Integrable (fun ell : ℝ => Real.exp (s * ell)) (scalarLaplaceMeasure ρ m) := by
  let m' := Real.sqrt (m ^ 2 - s / 4)
  have hm' : 0 < m' := Real.sqrt_pos.mpr (by linarith)
  have hm'sq : m' ^ 2 = m ^ 2 - s / 4 := Real.sq_sqrt (by linarith)
  apply (scalarLaplaceMeasure_integrable_iff ρ m (by fun_prop)).mpr
  apply (scalarProperDensity_tilt_integrable ρ hneg hzero hInv hm').mono'
  · exact ((scalarProperDensity_measurable m).mul
      ((scalarProperLambda_measurable.const_mul s).exp)).aestronglyMeasurable
  · filter_upwards [scalarProperWidths_positive ρ hneg hzero] with p hp
    rw [Real.norm_of_nonneg (mul_nonneg (scalarProperDensity_nonneg _ _) (Real.exp_pos _).le),
      scalarProperDensity_tilt_identity hm'sq]
    apply mul_le_mul_of_nonneg_left _ (scalarProperDensity_nonneg _ _)
    apply Real.exp_le_exp.mpr
    have hl := scalarProperLambda_upper (add_pos hp.1 hp.2)
    nlinarith

theorem oqedScalarLaplaceMeasure_exponential_integrable {a M m s : ℝ}
    (ha : 0 < a) (hM : 0 < M) (hm : 0 < m) (hs : 0 < s) (hsR : s < 4 * (min m M) ^ 2) :
    Integrable (fun ell : ℝ => Real.exp (s * ell)) (oqedScalarLaplaceMeasure a M m) := by
  let ρ := oqedHeatMeasure a M
  have hneg := oqedHeatMeasure_no_negative ha M
  have hzero := oqedHeatMeasure_no_atom_zero ha M
  have hmin : 0 ≤ min m M := le_min hm.le hM.le
  have hs_m : s < 4 * m ^ 2 := hsR.trans_le (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hmin (min_le_left m M) 2) (by norm_num))
  have hs_M : s < 4 * M ^ 2 := hsR.trans_le (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hmin (min_le_right m M) 2) (by norm_num))
  have hexp := oqedHeatMeasure_exponentialMoment_finite a M (b := s / 4) (by linarith)
  letI : IsFiniteMeasure (massiveTilt ρ (s / 4)) :=
    massiveTilt_finite ρ (s / 4) (s / 4) hneg hzero le_rfl hexp
  have hInv : inverseMoment (massiveTilt ρ (s / 4)) 2 < ⊤ :=
    massiveTilt_inverseMoment_finite ρ (by linarith : 0 ≤ s / 4) le_rfl (by norm_num)
      (oqedHeatMeasure_inverseMoment_finite ha M (by norm_num)) hexp
  exact scalarLaplaceMeasure_exponential_integrable ρ hneg hzero hs hm hs_m hInv

def scalarLaplaceExtension (a M m : ℝ) : ℂ → ℂ :=
  positiveComplexLaplace (oqedScalarLaplaceMeasure a M m)

def scalarRealLaplaceBubble (a M m : ℝ) : ℝ → ℝ :=
  positiveRealLaplace (oqedScalarLaplaceMeasure a M m)

def scalarLaplaceCoefficient (a M m : ℝ) (n : ℕ) : ℝ :=
  positiveLaplaceCoeff (oqedScalarLaplaceMeasure a M m) n

theorem scalarLaplaceExtension_differentiableOn {a M m : ℝ}
    (ha : 0 < a) (hM : 0 < M) (hm : 0 < m) :
    DifferentiableOn ℂ (scalarLaplaceExtension a M m) {z : ℂ | -(4 * (min m M) ^ 2) < z.re} := by
  have hR : 0 < 4 * (min m M) ^ 2 := by have hmin := lt_min hm hM; positivity
  exact positive_complex_laplace_differentiableOn hR (oqedScalarLaplaceMeasure_positive (M := M) ha m)
    (fun s hs hsR => oqedScalarLaplaceMeasure_exponential_integrable ha hM hm hs hsR)

/-- The positive proper-time transform supplies a genuine half-plane
continuation of the invariant bubble, rather than an outside-tube loop integral. -/
theorem scalarLaplaceExtension_analyticOnNhd {a M m : ℝ}
    (ha : 0 < a) (hM : 0 < M) (hm : 0 < m) :
    AnalyticOnNhd ℂ (scalarLaplaceExtension a M m) {z : ℂ | -(4 * (min m M) ^ 2) < z.re} :=
  (scalarLaplaceExtension_differentiableOn ha hM hm).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

theorem scalarLaplaceExtension_ofReal_nonneg {a M m w : ℝ}
    (ha : 0 < a) (hm : 0 < m) (hw : 0 ≤ w) :
    scalarLaplaceExtension a M m (w : ℂ) = scalarInvariantBubble a M m (w : ℂ) := by
  rw [scalarLaplaceExtension, positive_complex_laplace_ofReal]
  simpa only [positiveRealLaplace] using (scalarInvariantBubble_positive_laplace_real (M := M) ha hm hw).symm

theorem scalarLaplaceExtension_eqOn_invariant_disk {a M m : ℝ}
    (ha : 0 < a) (hM : 0 < M) (hm : 0 < m) :
    EqOn (scalarLaplaceExtension a M m) (scalarInvariantBubble a M m)
      (Metric.ball 0 (4 * (min m M) ^ 2)) := by
  let R := 4 * (min m M) ^ 2
  have hR : 0 < R := by have hmin := lt_min hm hM; dsimp [R]; positivity
  have hL : AnalyticOnNhd ℂ (scalarLaplaceExtension a M m) (Metric.ball 0 R) := by
    apply (scalarLaplaceExtension_analyticOnNhd ha hM hm).mono
    intro z hz
    have hn : ‖z‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hre := (abs_le.mp (Complex.abs_re_le_norm z)).1
    change -R < z.re
    linarith
  apply hL.eqOn_of_preconnected_of_mem_closure (z₀ := (0 : ℂ))
    (scalarInvariantBubble_analyticOnNhd ha hm hM) (convex_ball (0 : ℂ) R).isPreconnected
    (by simpa only [Metric.mem_ball, dist_self] using hR)
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let x : ℝ := min R ε / 2
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hxε : x < ε := by have hh := min_le_right R ε; dsimp [x]; linarith
  refine ⟨(x : ℂ), ⟨scalarLaplaceExtension_ofReal_nonneg (M := M) ha hm hx0.le, ?_⟩, ?_⟩
  · simpa only [mem_singleton_iff, Complex.ofReal_eq_zero] using hx0.ne'
  · simpa only [dist_zero_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] using hxε

theorem scalarInvariantCoefficient_as_laplace {a M m : ℝ}
    (ha : 0 < a) (hM : 0 < M) (hm : 0 < m) (n : ℕ) :
    scalarInvariantCoefficient a M m n = (scalarLaplaceCoefficient a M m n : ℂ) := by
  have hR : 0 < 4 * (min m M) ^ 2 := by have hmin := lt_min hm hM; positivity
  have heq : scalarInvariantBubble a M m =ᶠ[𝓝 (0 : ℂ)] scalarLaplaceExtension a M m := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hR] with z hz
    exact (scalarLaplaceExtension_eqOn_invariant_disk ha hM hm hz).symm
  unfold scalarInvariantCoefficient poleTaylorCoeff
  rw [heq.iteratedDeriv_eq n]
  exact positive_complex_laplace_coefficient hR (oqedScalarLaplaceMeasure_positive (M := M) ha m)
    (fun s hs hsR => oqedScalarLaplaceMeasure_exponential_integrable ha hM hm hs hsR) n

theorem scalarRealLaplaceBubble_actual {a M m w : ℝ}
    (ha : 0 < a) (hm : 0 < m) (hw : 0 ≤ w) :
    scalarRealLaplaceBubble a M m w = (scalarInvariantBubble a M m (w : ℂ)).re := by
  have he := scalarInvariantBubble_positive_laplace_real (M := M) ha hm hw
  simpa only [scalarRealLaplaceBubble, positiveRealLaplace, Complex.ofReal_re] using
    (congrArg Complex.re he).symm

theorem scalarRealLaplaceBubble_strictCM {a M m w : ℝ}
    (ha : 0 < a) (hM : 0 < M) (hm : 0 < m) (hw : 0 ≤ w) (n : ℕ) :
    0 < (-1 : ℝ) ^ n * iteratedDeriv n (scalarRealLaplaceBubble a M m) w := by
  have hR : 0 < 4 * (min m M) ^ 2 := by have hmin := lt_min hm hM; positivity
  exact positive_real_laplace_strictCM hR (oqedScalarLaplaceMeasure_positive (M := M) ha m)
    (oqedScalarLaplaceMeasure_ne_zero ha hM.le hm)
    (fun s hs hsR => oqedScalarLaplaceMeasure_exponential_integrable ha hM hm hs hsR) n (by linarith)

theorem scalarLaplaceCoefficient_alternates {a M m : ℝ}
    (ha : 0 < a) (hM : 0 < M) (hm : 0 < m) (n : ℕ) :
    0 < (-1 : ℝ) ^ n * scalarLaplaceCoefficient a M m n := by
  have hR : 0 < 4 * (min m M) ^ 2 := by have hmin := lt_min hm hM; positivity
  exact positive_laplace_coefficient_alternates hR (oqedScalarLaplaceMeasure_positive (M := M) ha m)
    (oqedScalarLaplaceMeasure_ne_zero ha hM.le hm)
    (fun s hs hsR => oqedScalarLaplaceMeasure_exponential_integrable ha hM hm hs hsR) n

/-- Signed finite Taylor enclosure with the actual invariant Taylor
coefficients. Only a finite polynomial is exchanged with the integral. -/
theorem scalarLaplace_signed_taylor {a M m w : ℝ}
    (ha : 0 < a) (hM : 0 < M) (hm : 0 < m) (hw : 0 ≤ w) (N : ℕ) :
    0 ≤ (-1 : ℝ) ^ (N + 1) * (scalarRealLaplaceBubble a M m w -
      ∑ n ∈ Finset.range (N + 1), scalarLaplaceCoefficient a M m n * w ^ n) ∧
    (-1 : ℝ) ^ (N + 1) * (scalarRealLaplaceBubble a M m w -
      ∑ n ∈ Finset.range (N + 1), scalarLaplaceCoefficient a M m n * w ^ n) ≤
        ‖scalarInvariantCoefficient a M m (N + 1)‖ * w ^ (N + 1) := by
  have hR : 0 < 4 * (min m M) ^ 2 := by have hmin := lt_min hm hM; positivity
  rw [scalarInvariantCoefficient_as_laplace ha hM hm]
  simpa only [scalarRealLaplaceBubble, scalarLaplaceCoefficient, Complex.norm_real, Real.norm_eq_abs] using
    positive_laplace_signed_taylor hR (oqedScalarLaplaceMeasure_positive (M := M) ha m)
      (fun s hs hsR => oqedScalarLaplaceMeasure_exponential_integrable ha hM hm hs hsR) N hw

/-- The full signed scalar approximation proposition for the actual bubble:
the positive measure, its exponential moments and half-plane continuation,
strict complete monotonicity and actual finite Taylor enclosures. -/
theorem oqed_scalar_CM_enclosure {a M m : ℝ} (ha : 0 < a) (hM : 0 < M) (hm : 0 < m) :
    IsFiniteMeasure (oqedScalarLaplaceMeasure a M m) ∧
    (∀ᵐ ell ∂oqedScalarLaplaceMeasure a M m, 0 < ell) ∧
    oqedScalarLaplaceMeasure a M m ≠ 0 ∧
    (∀ w : ℝ, 0 ≤ w → scalarInvariantBubble a M m (w : ℂ) =
      (((∫ ell, Real.exp (-ell * w) ∂oqedScalarLaplaceMeasure a M m) : ℝ) : ℂ)) ∧
    (∀ s, 0 < s → s < 4 * (min m M) ^ 2 →
      Integrable (fun ell : ℝ => Real.exp (s * ell)) (oqedScalarLaplaceMeasure a M m)) ∧
    AnalyticOnNhd ℂ (scalarLaplaceExtension a M m) {z : ℂ | -(4 * (min m M) ^ 2) < z.re} ∧
    EqOn (scalarLaplaceExtension a M m) (scalarInvariantBubble a M m) (Metric.ball 0 (4 * (min m M) ^ 2)) ∧
    (∀ n, scalarInvariantCoefficient a M m n = (scalarLaplaceCoefficient a M m n : ℂ) ∧
      0 < (-1 : ℝ) ^ n * scalarLaplaceCoefficient a M m n) ∧
    (∀ w, 0 ≤ w → ∀ n, 0 < (-1 : ℝ) ^ n * iteratedDeriv n (scalarRealLaplaceBubble a M m) w) ∧
    (∀ N w, 0 ≤ w →
      0 ≤ (-1 : ℝ) ^ (N + 1) * (scalarRealLaplaceBubble a M m w -
        ∑ n ∈ Finset.range (N + 1), scalarLaplaceCoefficient a M m n * w ^ n) ∧
      (-1 : ℝ) ^ (N + 1) * (scalarRealLaplaceBubble a M m w -
        ∑ n ∈ Finset.range (N + 1), scalarLaplaceCoefficient a M m n * w ^ n) ≤
          ‖scalarInvariantCoefficient a M m (N + 1)‖ * w ^ (N + 1)) := by
  refine ⟨oqedScalarLaplaceMeasure_finite ha hm, oqedScalarLaplaceMeasure_positive (M := M) ha m,
    oqedScalarLaplaceMeasure_ne_zero ha hM.le hm, ?_, ?_, scalarLaplaceExtension_analyticOnNhd ha hM hm,
    scalarLaplaceExtension_eqOn_invariant_disk ha hM hm, ?_, ?_, ?_⟩
  · intro w hw
    exact scalarInvariantBubble_positive_laplace_real ha hm hw
  · intro s hs hsR
    exact oqedScalarLaplaceMeasure_exponential_integrable ha hM hm hs hsR
  · intro n
    exact ⟨scalarInvariantCoefficient_as_laplace ha hM hm n, scalarLaplaceCoefficient_alternates ha hM hm n⟩
  · intro w hw n
    exact scalarRealLaplaceBubble_strictCM ha hM hm hw n
  · intro N w hw
    exact scalarLaplace_signed_taylor ha hM hm hw N

end UV
