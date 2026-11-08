import UV.GaussianRemainder
import UV.ScalarLaplace
import UV.FeynmanTime
import UV.Frullani
import UV.StandardBubble

/-! Matching the finite normalized Gaussian proper-time benchmark to the
literal four-dimensional Euclidean loop. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace UV

def gaussianBubbleEuclidean (t m : ℝ) (P : ScalarMomentum) : ℝ :=
  (2 * Real.pi) ^ (-4 : ℤ) * ∫ q : ScalarMomentum,
    (Real.exp (-t * ‖q‖ ^ 2) / (‖q‖ ^ 2 + m ^ 2)) *
      (Real.exp (-t * ‖q + P‖ ^ 2) / (‖q + P‖ ^ 2 + m ^ 2))

def gaussianProperCoefficient (t m w : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-m ^ 2 * (p.1 + p.2)) /
    (16 * Real.pi ^ 2 * ((t + p.1) + (t + p.2)) ^ 2) *
      Real.exp (-((t + p.1) * (t + p.2) / ((t + p.1) + (t + p.2))) * w)

theorem gaussian_bubble_as_heat_measure (t m : ℝ) (P : ScalarMomentum) :
    gaussianBubbleEuclidean t m P = scalarMeasureBubble (Measure.dirac t) m P := by
  simp only [gaussianBubbleEuclidean, scalarMeasureBubble, laplace, integral_dirac]

theorem gaussian_dirac_no_negative {t : ℝ} (ht : 0 < t) : (Measure.dirac t) (Iio (0 : ℝ)) = 0 := by
  simp [Measure.dirac_apply', not_lt_of_ge ht.le]

theorem gaussian_dirac_no_atom {t : ℝ} (ht : 0 < t) : (Measure.dirac t) {0} = 0 := by
  simp [Measure.dirac_apply', ht.ne']

theorem gaussian_dirac_inverseMoment_finite {t : ℝ} (ht : 0 < t) (r : ℝ) :
    inverseMoment (Measure.dirac t) r < ⊤ := by
  simp [inverseMoment, restrict_dirac, ht]

theorem gaussian_proper_base (t : ℝ) : scalarProperBase (Measure.dirac t) =
    Measure.map (fun p : ℝ × ℝ => ((t, p.1), (t, p.2)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  unfold scalarProperBase scalarProperLineBase
  rw [Measure.dirac_prod, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  rfl

theorem gaussian_bubble_proper_representation {t m : ℝ} (ht : 0 < t) (hm : 0 < m)
    (P : ScalarMomentum) : gaussianBubbleEuclidean t m P =
      ∫ p, gaussianProperCoefficient t m (‖P‖ ^ 2) p
        ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))) := by
  rw [gaussian_bubble_as_heat_measure, scalarMeasureBubble_laplace (Measure.dirac t)
    (gaussian_dirac_no_negative ht) (gaussian_dirac_no_atom ht)
      (gaussian_dirac_inverseMoment_finite ht 2) hm P]
  rw [scalarLaplaceMeasure_integral _ _ (by fun_prop), gaussian_proper_base,
    integral_map (by fun_prop) (by
      apply Measurable.aestronglyMeasurable
      exact (scalarProperDensity_measurable m).mul ((scalarProperLambda_measurable.neg.mul_const (‖P‖ ^ 2)).exp))]
  rfl

theorem gaussian_proper_coefficient_integrable {t m w : ℝ} (ht : 0 < t) (hm : 0 < m) (hw : 0 ≤ w) :
    Integrable (gaussianProperCoefficient t m w)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hi := scalarProperDensity_integrable (Measure.dirac t) (gaussian_dirac_no_negative ht)
    (gaussian_dirac_no_atom ht) (gaussian_dirac_inverseMoment_finite ht 2) hm
  rw [gaussian_proper_base] at hi
  have hi' := (integrable_map_measure (scalarProperDensity_measurable m).aestronglyMeasurable
    (by fun_prop : Measurable (fun p : ℝ × ℝ => ((t, p.1), (t, p.2)))).aemeasurable).mp hi
  apply hi'.mono'
  · apply Measurable.aestronglyMeasurable
    unfold gaussianProperCoefficient
    fun_prop
  · filter_upwards [((Measure.quasiMeasurePreserving_fst).ae (ae_restrict_mem measurableSet_Ioi)).and
      ((Measure.quasiMeasurePreserving_snd).ae (ae_restrict_mem measurableSet_Ioi))] with p hp
    have hp1 : 0 < p.1 := hp.1
    have hp2 : 0 < p.2 := hp.2
    have hsum : 0 < (t + p.1) + (t + p.2) := by linarith
    have hlam : 0 ≤ (t + p.1) * (t + p.2) / ((t + p.1) + (t + p.2)) := by positivity
    change ‖gaussianProperCoefficient t m w p‖ ≤ scalarProperDensity m ((t, p.1), (t, p.2))
    unfold gaussianProperCoefficient scalarProperDensity scalarProperWidth
    dsimp only
    rw [Real.norm_of_nonneg (by positivity)]
    apply mul_le_of_le_one_right (by positivity)
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlam) hw)

theorem gaussian_shifted_positive_measure (t : ℝ) :
    Measure.map (fun a : ℝ => t + a) (volume.restrict (Ioi (0 : ℝ))) = volume.restrict (Ioi t) := by
  have h := Measure.restrict_map (μ := volume) (f := fun a : ℝ => t + a)
    (measurable_const.add measurable_id) (s := Ioi t) measurableSet_Ioi
  have hpre : (fun a : ℝ => t + a) ⁻¹' Ioi t = Ioi (0 : ℝ) := by
    ext a
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro h' <;> linarith
  rw [map_add_left_eq_self volume t, hpre] at h
  exact h.symm

theorem gaussian_two_time_shift (t : ℝ) (f : ℝ × ℝ → ℝ) (hf : Measurable f) :
    (∫ p, f (t + p.1, t + p.2)
      ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) =
      ∫ p, f p ∂(volume.restrict (Ioi t)).prod (volume.restrict (Ioi t)) := by
  rw [← gaussian_shifted_positive_measure t, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) hf.aestronglyMeasurable]
  rfl

def gaussianWidthDifference (m w : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-m ^ 2 * (p.1 + p.2)) / (p.1 + p.2) ^ 2 *
    (1 - Real.exp (-(p.1 * p.2 / (p.1 + p.2)) * w))

theorem gaussian_width_difference_measurable (m w : ℝ) : Measurable (gaussianWidthDifference m w) := by
  unfold gaussianWidthDifference
  fun_prop

theorem gaussian_width_difference_nonneg {m w : ℝ} (hw : 0 ≤ w) {p : ℝ × ℝ}
    (hp : 0 < p.1 ∧ 0 < p.2) : 0 ≤ gaussianWidthDifference m w p := by
  have hp1 : 0 < p.1 := hp.1
  have hp2 : 0 < p.2 := hp.2
  unfold gaussianWidthDifference
  apply mul_nonneg (by positivity)
  apply sub_nonneg.mpr
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hw

theorem gaussian_normalized_difference_pointwise (t m w : ℝ) (p : ℝ × ℝ) :
    Real.exp (-2 * t * m ^ 2) *
      (gaussianProperCoefficient t m 0 p - gaussianProperCoefficient t m w p) =
      (16 * Real.pi ^ 2)⁻¹ * gaussianWidthDifference m w (t + p.1, t + p.2) := by
  unfold gaussianProperCoefficient gaussianWidthDifference
  dsimp only
  simp only [mul_zero, Real.exp_zero, mul_one]
  have hexp : Real.exp (-2 * t * m ^ 2) * Real.exp (-m ^ 2 * (p.1 + p.2)) =
      Real.exp (-m ^ 2 * ((t + p.1) + (t + p.2))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-2 * t * m ^ 2) * Real.exp (-m ^ 2 * (p.1 + p.2))) /
        (16 * Real.pi ^ 2 * ((t + p.1) + (t + p.2)) ^ 2) *
        (1 - Real.exp (-((t + p.1) * (t + p.2) / ((t + p.1) + (t + p.2))) * w)) := by ring
    _ = _ := by rw [hexp]; simp only [div_eq_mul_inv, mul_inv_rev]; ring

theorem gaussian_normalized_subtraction_proper {t m : ℝ} (ht : 0 < t) (hm : 0 < m)
    (P : ScalarMomentum) :
    Real.exp (-2 * t * m ^ 2) * (gaussianBubbleEuclidean t m 0 - gaussianBubbleEuclidean t m P) =
      (16 * Real.pi ^ 2)⁻¹ * ∫ p, gaussianWidthDifference m (‖P‖ ^ 2) p
        ∂(volume.restrict (Ioi t)).prod (volume.restrict (Ioi t)) := by
  rw [gaussian_bubble_proper_representation ht hm 0, gaussian_bubble_proper_representation ht hm P]
  simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
  rw [← integral_sub (gaussian_proper_coefficient_integrable ht hm (by norm_num : (0 : ℝ) ≤ 0))
    (gaussian_proper_coefficient_integrable ht hm (sq_nonneg _)), ← integral_const_mul]
  simp_rw [gaussian_normalized_difference_pointwise]
  rw [integral_const_mul, gaussian_two_time_shift _ _ (gaussian_width_difference_measurable _ _)]

theorem gaussian_width_cutoff_integral {t m w : ℝ} (ht : 0 < t) (hw : 0 ≤ w) :
    (∫ p, gaussianWidthDifference m w p ∂(volume.restrict (Ioi t)).prod (volume.restrict (Ioi t))) =
      ∫ p, p.1 * (if t < p.1 * p.2 ∧ t < p.1 * (1 - p.2) then
          gaussianWidthDifference m w (p.1 * p.2, p.1 * (1 - p.2)) else 0)
        ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1)) := by
  let Q : Set (ℝ × ℝ) := (Ioi t) ×ˢ (Ioi t)
  have hQ : MeasurableSet Q := measurableSet_Ioi.prod measurableSet_Ioi
  have hf : Measurable (Q.indicator (gaussianWidthDifference m w)) :=
    (gaussian_width_difference_measurable m w).indicator hQ
  have hsub : Q ⊆ (Ioi (0 : ℝ)) ×ˢ (Ioi (0 : ℝ)) := by
    intro p hp
    exact ⟨ht.trans hp.1, ht.trans hp.2⟩
  have hleft : (∫ p, Q.indicator (gaussianWidthDifference m w) p
      ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) =
      ∫ p, gaussianWidthDifference m w p ∂(volume.restrict (Ioi t)).prod (volume.restrict (Ioi t)) := by
    simp only [Measure.prod_restrict]
    rw [integral_indicator hQ, Measure.restrict_restrict hQ, inter_eq_left.mpr hsub]
  rw [← hleft, positive_feynman_time_real _ hf]
  · apply integral_congr_ae
    filter_upwards with p
    simp only [Q, indicator, mem_prod, mem_Ioi]
  · intro a ha b hb
    by_cases h : (a, b) ∈ Q
    · rw [indicator_of_mem h]
      exact gaussian_width_difference_nonneg hw ⟨ha, hb⟩
    · rw [indicator_of_notMem h]

theorem gaussian_width_cutoff_iff {t S x : ℝ} (hS : 0 < S) (hx : x ∈ Ioo (0 : ℝ) 1) :
    (t < S * x ∧ t < S * (1 - x)) ↔ gaussianWmin t x < S := by
  have hm : 0 < min x (1 - x) := lt_min hx.1 (sub_pos.mpr hx.2)
  rw [gaussianWmin, div_lt_iff₀ hm]
  by_cases h : x ≤ 1 - x
  · rw [min_eq_left h]
    have hp := mul_le_mul_of_nonneg_left h hS.le
    constructor
    · exact fun hh => hh.1
    · exact fun hh => ⟨hh, hh.trans_le hp⟩
  · have h' := le_of_lt (lt_of_not_ge h)
    rw [min_eq_right h']
    have hp := mul_le_mul_of_nonneg_left h' hS.le
    constructor
    · exact fun hh => hh.2
    · exact fun hh => ⟨hh.trans_le hp, hh⟩

theorem gaussian_feynman_width_difference {m w S x : ℝ} (hS : 0 < S) :
    S * gaussianWidthDifference m w (S * x, S * (1 - x)) =
      frullaniIntegrand (m ^ 2) (x * (1 - x) * w) S := by
  have hsum : S * x + S * (1 - x) = S := by ring
  have hlam : (S * x) * (S * (1 - x)) / S = S * (x * (1 - x)) := by
    field_simp [hS.ne']
  unfold gaussianWidthDifference frullaniIntegrand
  dsimp only
  rw [hsum, hlam]
  have harg : -(S * (x * (1 - x))) * w = -(x * (1 - x) * w) * S := by ring
  rw [harg]
  field_simp [hS.ne']

theorem gaussian_frullani_joint_integrable {m w : ℝ} (hm : 0 < m) (hw : 0 ≤ w) :
    Integrable (fun p : ℝ × ℝ => frullaniIntegrand (m ^ 2) (p.2 * (1 - p.2) * w) p.1)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hi : IntegrableOn (fun S : ℝ => Real.exp (-m ^ 2 * S)) (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (sq_pos_of_pos hm)) 0
  apply ((hi.comp_fst (volume.restrict (Ioo (0 : ℝ) 1))).const_mul (w / 4)).mono'
  · apply Measurable.aestronglyMeasurable
    unfold frullaniIntegrand
    fun_prop
  · have hp : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1)),
        p.1 ∈ Ioi (0 : ℝ) ∧ p.2 ∈ Ioo (0 : ℝ) 1 :=
      ((Measure.quasiMeasurePreserving_fst).ae (ae_restrict_mem measurableSet_Ioi)).and
        ((Measure.quasiMeasurePreserving_snd).ae (ae_restrict_mem measurableSet_Ioo))
    filter_upwards [hp] with p hp'
    have hS : 0 < p.1 := hp'.1
    have hx : p.2 ∈ Ioo (0 : ℝ) 1 := hp'.2
    have hc : 0 ≤ p.2 * (1 - p.2) * w := mul_nonneg (mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le)) hw
    have hcupper : p.2 * (1 - p.2) * w ≤ w / 4 := by
      have hquarter : p.2 * (1 - p.2) ≤ (1 / 4 : ℝ) := by nlinarith [sq_nonneg (p.2 - 1 / 2)]
      nlinarith [mul_le_mul_of_nonneg_right hquarter hw]
    rw [Real.norm_of_nonneg (frullani_integrand_nonneg hc hS.le)]
    unfold frullaniIntegrand
    have hdiff : 1 - Real.exp (-(p.2 * (1 - p.2) * w) * p.1) ≤ (p.2 * (1 - p.2) * w) * p.1 := by
      have h := Real.add_one_le_exp (-(p.2 * (1 - p.2) * w) * p.1)
      linarith
    calc
      _ ≤ Real.exp (-m ^ 2 * p.1) * ((p.2 * (1 - p.2) * w) * p.1) / p.1 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdiff (Real.exp_nonneg _)) hS.le
      _ = (p.2 * (1 - p.2) * w) * Real.exp (-m ^ 2 * p.1) := by field_simp [hS.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right hcupper (Real.exp_nonneg _)

theorem gaussian_feynman_parameters :
    ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1)),
      0 < p.1 ∧ p.2 ∈ Ioo (0 : ℝ) 1 :=
  ((Measure.quasiMeasurePreserving_fst).ae (ae_restrict_mem measurableSet_Ioi)).and
    ((Measure.quasiMeasurePreserving_snd).ae (ae_restrict_mem measurableSet_Ioo))

theorem gaussian_width_difference_tail {t m w : ℝ} (ht : 0 < t) (hm : 0 < m) (hw : 0 ≤ w) :
    (∫ p, gaussianWidthDifference m w p ∂(volume.restrict (Ioi t)).prod (volume.restrict (Ioi t))) =
      ∫ x in Ioo (0 : ℝ) 1, ∫ S in Ioi (gaussianWmin t x),
        frullaniIntegrand (m ^ 2) (x * (1 - x) * w) S := by
  let G : ℝ × ℝ → ℝ := fun p => if gaussianWmin t p.2 < p.1 then
    frullaniIntegrand (m ^ 2) (p.2 * (1 - p.2) * w) p.1 else 0
  have hGm : Measurable G := by
    apply Measurable.ite
    · exact measurableSet_lt (by unfold gaussianWmin; fun_prop) measurable_fst
    · unfold frullaniIntegrand
      fun_prop
    · exact measurable_const
  have hGi : Integrable G
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    apply (gaussian_frullani_joint_integrable hm hw).mono' hGm.aestronglyMeasurable
    filter_upwards [gaussian_feynman_parameters] with p hp
    have hc : 0 ≤ p.2 * (1 - p.2) * w :=
      mul_nonneg (mul_nonneg hp.2.1.le (sub_nonneg.mpr hp.2.2.le)) hw
    have hpos := frullani_integrand_nonneg (b := m ^ 2) hc hp.1.le
    unfold G
    split_ifs
    · rw [Real.norm_of_nonneg hpos]
    · simpa only [norm_zero] using hpos
  rw [gaussian_width_cutoff_integral ht hw]
  have he : (fun p : ℝ × ℝ => p.1 * (if t < p.1 * p.2 ∧ t < p.1 * (1 - p.2) then
      gaussianWidthDifference m w (p.1 * p.2, p.1 * (1 - p.2)) else 0)) =ᵐ[
        (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1))] G := by
    filter_upwards [gaussian_feynman_parameters] with p hp
    unfold G
    simp only [gaussian_width_cutoff_iff hp.1 hp.2]
    split_ifs
    · exact gaussian_feynman_width_difference hp.1
    · exact mul_zero _
  rw [integral_congr_ae he, integral_prod_symm G hGi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hfun : (fun S => G (S, x)) = (Ioi (gaussianWmin t x)).indicator
      (frullaniIntegrand (m ^ 2) (x * (1 - x) * w)) := by
    funext S
    simp only [G, indicator, mem_Ioi]
  rw [hfun, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  rw [inter_eq_left.mpr (show Ioi (gaussianWmin t x) ⊆ Ioi (0 : ℝ) from
    fun S hS => (gaussian_remainder_scale_bounds ht.le hx).1.trans_lt hS)]

theorem gaussian_bubble_subtraction_tail {t m : ℝ} (ht : 0 < t) (hm : 0 < m)
    (P : ScalarMomentum) :
    Real.exp (-2 * t * m ^ 2) * (gaussianBubbleEuclidean t m 0 - gaussianBubbleEuclidean t m P) =
      (16 * Real.pi ^ 2)⁻¹ * ∫ x in Ioo (0 : ℝ) 1, ∫ S in Ioi (gaussianWmin t x),
        frullaniIntegrand (m ^ 2) (x * (1 - x) * ‖P‖ ^ 2) S := by
  rw [gaussian_normalized_subtraction_proper ht hm P, gaussian_width_difference_tail ht hm (sq_nonneg _)]

theorem gaussian_frullani_tail_joint_integrable {t m w : ℝ} (hm : 0 < m) (hw : 0 ≤ w) :
    Integrable (fun p : ℝ × ℝ => if gaussianWmin t p.2 < p.1 then
      frullaniIntegrand (m ^ 2) (p.2 * (1 - p.2) * w) p.1 else 0)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  apply (gaussian_frullani_joint_integrable hm hw).mono'
  · apply Measurable.aestronglyMeasurable
    apply Measurable.ite
    · exact measurableSet_lt (by unfold gaussianWmin; fun_prop) measurable_fst
    · unfold frullaniIntegrand
      fun_prop
    · exact measurable_const
  · filter_upwards [gaussian_feynman_parameters] with p hp
    have hc : 0 ≤ p.2 * (1 - p.2) * w :=
      mul_nonneg (mul_nonneg hp.2.1.le (sub_nonneg.mpr hp.2.2.le)) hw
    have hpos := frullani_integrand_nonneg (b := m ^ 2) hc hp.1.le
    split_ifs
    · rw [Real.norm_of_nonneg hpos]
    · simpa only [norm_zero] using hpos

theorem gaussian_frullani_tail_outer_integrable {t m w : ℝ} (ht : 0 < t) (hm : 0 < m) (hw : 0 ≤ w) :
    IntegrableOn (fun x => ∫ S in Ioi (gaussianWmin t x),
      frullaniIntegrand (m ^ 2) (x * (1 - x) * w) S) (Ioo (0 : ℝ) 1) := by
  have hi := (gaussian_frullani_tail_joint_integrable (t := t) hm hw).integral_prod_right
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hfun : (fun S => if gaussianWmin t x < S then
      frullaniIntegrand (m ^ 2) (x * (1 - x) * w) S else 0) =
      (Ioi (gaussianWmin t x)).indicator (frullaniIntegrand (m ^ 2) (x * (1 - x) * w)) := by
    funext S
    simp only [indicator, mem_Ioi]
  rw [hfun, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  rw [inter_eq_left.mpr (show Ioi (gaussianWmin t x) ⊆ Ioi (0 : ℝ) from
    fun S hS => (gaussian_remainder_scale_bounds ht.le hx).1.trans_lt hS)]

theorem gaussian_frullani_full_outer_integrable {m w : ℝ} (hm : 0 < m) (hw : 0 ≤ w) :
    IntegrableOn (fun x => Real.log (1 + x * (1 - x) * w / m ^ 2)) (Ioo (0 : ℝ) 1) := by
  apply (gaussian_frullani_joint_integrable hm hw).integral_prod_right.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact frullani_integral (sq_pos_of_pos hm)
    (mul_nonneg (mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le)) hw)

theorem gaussian_frullani_split {t m w x : ℝ} (ht : 0 < t) (hm : 0 < m) (hw : 0 ≤ w)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    Real.log (1 + x * (1 - x) * w / m ^ 2) =
      (∫ S in (0 : ℝ)..gaussianWmin t x, frullaniIntegrand (m ^ 2) (x * (1 - x) * w) S) +
      ∫ S in Ioi (gaussianWmin t x), frullaniIntegrand (m ^ 2) (x * (1 - x) * w) S := by
  have hc : 0 ≤ x * (1 - x) * w := mul_nonneg (mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le)) hw
  have hi := frullani_integrable (sq_pos_of_pos hm) hc
  have hW : 0 ≤ gaussianWmin t x := (gaussian_remainder_scale_bounds ht.le hx).1
  rw [← frullani_integral (sq_pos_of_pos hm) hc,
    ← Ioc_union_Ioi_eq_Ioi hW, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hi.mono_set (show Ioc (0 : ℝ) (gaussianWmin t x) ⊆ Ioi (0 : ℝ) from fun _ h => h.1))
      (hi.mono_set (show Ioi (gaussianWmin t x) ⊆ Ioi (0 : ℝ) from fun _ h => hW.trans_lt h)),
    ← intervalIntegral.integral_of_le hW]

theorem gaussian_remainder_euclidean_real {t m : ℝ} (ht : 0 < t) (w : ℝ) :
    (gaussianRemainder t m (-(w : ℂ))).re = (16 * Real.pi ^ 2)⁻¹ *
      ∫ x in Ioo (0 : ℝ) 1, ∫ S in (0 : ℝ)..gaussianWmin t x,
        frullaniIntegrand (m ^ 2) (x * (1 - x) * w) S := by
  have h := gaussian_remainder_positive_representation (m := m) ht (-w)
  have he : ∀ x, gaussianPositiveProperIntegrand m (-w) x =
      fun S => -frullaniIntegrand (m ^ 2) (x * (1 - x) * w) S := by
    intro x
    funext S
    unfold gaussianPositiveProperIntegrand frullaniIntegrand
    have harg : (S * (x * (1 - x))) * (-w) = -(x * (1 - x) * w) * S := by ring
    rw [harg]
    ring
  simp_rw [he, intervalIntegral.integral_neg, integral_neg] at h
  simpa only [Complex.ofReal_neg, mul_neg, neg_inj] using h

theorem gaussian_frullani_omitted_outer_integrable {t m w : ℝ} (ht : 0 < t) (hm : 0 < m) (hw : 0 ≤ w) :
    IntegrableOn (fun x => ∫ S in (0 : ℝ)..gaussianWmin t x,
      frullaniIntegrand (m ^ 2) (x * (1 - x) * w) S) (Ioo (0 : ℝ) 1) := by
  apply ((gaussian_frullani_full_outer_integrable hm hw).sub
    (gaussian_frullani_tail_outer_integrable ht hm hw)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have h := gaussian_frullani_split ht hm hw hx
  dsimp only [Pi.sub_apply]
  linarith

theorem gaussian_frullani_integral_split {t m w : ℝ} (ht : 0 < t) (hm : 0 < m) (hw : 0 ≤ w) :
    (∫ x in Ioo (0 : ℝ) 1, Real.log (1 + x * (1 - x) * w / m ^ 2)) =
      (∫ x in Ioo (0 : ℝ) 1, ∫ S in (0 : ℝ)..gaussianWmin t x,
        frullaniIntegrand (m ^ 2) (x * (1 - x) * w) S) +
      ∫ x in Ioo (0 : ℝ) 1, ∫ S in Ioi (gaussianWmin t x),
        frullaniIntegrand (m ^ 2) (x * (1 - x) * w) S := by
  rw [← integral_add (gaussian_frullani_omitted_outer_integrable ht hm hw)
    (gaussian_frullani_tail_outer_integrable ht hm hw)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact gaussian_frullani_split ht hm hw hx

/-- Exact matching to the actual Gaussian loop on every real Euclidean
momentum. The normalization, logarithm, and entire remainder are all derived
from convergent integrals; the candidate continuation is not assumed. -/
theorem gaussian_normalized_euclidean_decomposition {t m : ℝ} (ht : 0 < t) (hm : 0 < m)
    (P : ScalarMomentum) :
    Real.exp (-2 * t * m ^ 2) * (gaussianBubbleEuclidean t m P - gaussianBubbleEuclidean t m 0) =
      -((16 * Real.pi ^ 2)⁻¹ * ∫ x in Ioo (0 : ℝ) 1,
          Real.log (1 + x * (1 - x) * ‖P‖ ^ 2 / m ^ 2)) +
        (gaussianRemainder t m (-((‖P‖ ^ 2 : ℝ) : ℂ))).re := by
  have htail := gaussian_bubble_subtraction_tail ht hm P
  rw [gaussian_remainder_euclidean_real ht,
    gaussian_frullani_integral_split ht hm (sq_nonneg _)]
  linear_combination -htail

theorem gaussian_remainder_euclidean_isReal (t m w : ℝ) :
    (((gaussianRemainder t m (-(w : ℂ))).re : ℝ) : ℂ) = gaussianRemainder t m (-(w : ℂ)) := by
  rw [← Complex.ofReal_neg, gaussian_remainder_real]
  simp only [Complex.ofReal_re]

theorem gaussian_remainder_uniform_zero_on_bounded (m : ℝ) {K : Set ℂ}
    (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn (fun t z => gaussianRemainder t m z) (fun _ => (0 : ℂ)) (𝓝[>] (0 : ℝ)) K := by
  obtain ⟨R, hR, hbound⟩ := hK.exists_pos_norm_le
  have hc : Continuous (fun t : ℝ => 3 * t * R / (64 * Real.pi ^ 2) * Real.exp (t * R)) := by fun_prop
  have hlim : Tendsto (fun t : ℝ => 3 * t * R / (64 * Real.pi ^ 2) * Real.exp (t * R))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, zero_mul, zero_div] using
      (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε), self_mem_nhdsWithin] with t ht htpos
  intro z hz
  rw [dist_zero_left]
  have ht0 : 0 ≤ t := (show 0 < t from htpos).le
  apply (gaussian_remainder_norm_bound ht0 z).trans_lt
  apply lt_of_le_of_lt _ ht
  gcongr
  · exact hbound z hz
  · exact hbound z hz

/-- The normalized analytic continuation is fixed by the actual Euclidean
loop matching proved below. -/
def gaussianNormalizedBubble (t m : ℝ) (z : ℂ) : ℂ := standardBubble m z + gaussianRemainder t m z

def gaussianBubbleContinuation (t m : ℝ) (z : ℂ) : ℂ :=
  (Real.exp (2 * t * m ^ 2) : ℂ) * gaussianNormalizedBubble t m z +
    (gaussianBubbleEuclidean t m 0 : ℂ)

theorem gaussian_normalized_bubble_zero (t m : ℝ) : gaussianNormalizedBubble t m 0 = 0 := by
  simp [gaussianNormalizedBubble, standardBubble, standardBubbleLog, gaussian_remainder_zero]

theorem gaussian_bubble_continuation_zero (t m : ℝ) :
    gaussianBubbleContinuation t m 0 = (gaussianBubbleEuclidean t m 0 : ℂ) := by
  simp [gaussianBubbleContinuation, gaussian_normalized_bubble_zero]

theorem gaussian_normalized_bubble_holomorphic {t m : ℝ} (ht : 0 < t) (hm : 0 < m) :
    AnalyticOnNhd ℂ (gaussianNormalizedBubble t m) (bubbleCutDomain m) := by
  exact (standardBubble_holomorphic hm).add
    ((gaussian_remainder_entire ht.le).differentiableOn.analyticOnNhd (bubbleCutDomain_open m))

theorem gaussian_bubble_continuation_holomorphic {t m : ℝ} (ht : 0 < t) (hm : 0 < m) :
    AnalyticOnNhd ℂ (gaussianBubbleContinuation t m) (bubbleCutDomain m) := by
  exact (analyticOnNhd_const.mul (gaussian_normalized_bubble_holomorphic ht hm)).add analyticOnNhd_const

theorem gaussian_normalized_bubble_actual {t m : ℝ} (ht : 0 < t) (hm : 0 < m) (P : ScalarMomentum) :
    gaussianNormalizedBubble t m (-((‖P‖ ^ 2 : ℝ) : ℂ)) =
      ((Real.exp (-2 * t * m ^ 2) * (gaussianBubbleEuclidean t m P - gaussianBubbleEuclidean t m 0) : ℝ) : ℂ) := by
  rw [gaussianNormalizedBubble, standardBubble_real_euclidean hm (sq_nonneg _), integral_Icc_eq_integral_Ioo]
  have h := congrArg (fun r : ℝ => (r : ℂ)) (gaussian_normalized_euclidean_decomposition ht hm P)
  simp only [Complex.ofReal_add, Complex.ofReal_neg, gaussian_remainder_euclidean_isReal] at h
  simpa only [bubbleFeynmanWeight] using h.symm

theorem gaussian_bubble_continuation_actual {t m : ℝ} (ht : 0 < t) (hm : 0 < m) (P : ScalarMomentum) :
    gaussianBubbleContinuation t m (-((‖P‖ ^ 2 : ℝ) : ℂ)) = (gaussianBubbleEuclidean t m P : ℂ) := by
  rw [gaussianBubbleContinuation, gaussian_normalized_bubble_actual ht hm P]
  have he : Real.exp (2 * t * m ^ 2) * Real.exp (-2 * t * m ^ 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  have hreal : Real.exp (2 * t * m ^ 2) *
      (Real.exp (-2 * t * m ^ 2) * (gaussianBubbleEuclidean t m P - gaussianBubbleEuclidean t m 0)) +
      gaussianBubbleEuclidean t m 0 = gaussianBubbleEuclidean t m P := by
    rw [← mul_assoc, he, one_mul, sub_add_cancel]
  exact_mod_cast hreal

theorem gaussian_bubble_finite_normalization (t m : ℝ) (z : ℂ) :
    (Real.exp (-2 * t * m ^ 2) : ℂ) *
      (gaussianBubbleContinuation t m z - gaussianBubbleContinuation t m 0) = gaussianNormalizedBubble t m z := by
  rw [gaussian_bubble_continuation_zero]
  unfold gaussianBubbleContinuation
  rw [add_sub_cancel_right, ← mul_assoc, ← Complex.ofReal_mul]
  have he : Real.exp (-2 * t * m ^ 2) * Real.exp (2 * t * m ^ 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  rw [he, Complex.ofReal_one, one_mul]

theorem gaussian_normalized_bubble_compact_limit (m : ℝ) {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun t z => gaussianNormalizedBubble t m z) (standardBubble m) (𝓝[>] (0 : ℝ)) K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have h := Metric.tendstoUniformlyOn_iff.mp
    (gaussian_remainder_uniform_zero_on_bounded m hK.isBounded) ε hε
  filter_upwards [h] with t ht
  intro z hz
  simpa [gaussianNormalizedBubble, dist_eq_norm] using ht z hz

theorem gaussian_normalized_continuation_unique {t m : ℝ} (ht : 0 < t) (hm : 0 < m)
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F (bubbleCutDomain m))
    (hactual : ∀ P : ScalarMomentum, F (-((‖P‖ ^ 2 : ℝ) : ℂ)) =
      ((Real.exp (-2 * t * m ^ 2) * (gaussianBubbleEuclidean t m P - gaussianBubbleEuclidean t m 0) : ℝ) : ℂ)) :
    EqOn F (gaussianNormalizedBubble t m) (bubbleCutDomain m) := by
  apply bubble_cut_continuation_unique hm hF (gaussian_normalized_bubble_holomorphic ht hm)
  intro w hw
  let P := scalarAxis (Real.sqrt w)
  have hnorm : ‖P‖ ^ 2 = w := by
    rw [show P = scalarAxis (Real.sqrt w) from rfl, scalarAxis_norm,
      abs_of_nonneg (Real.sqrt_nonneg w), Real.sq_sqrt hw]
  have h₁ := hactual P
  have h₂ := gaussian_normalized_bubble_actual ht hm P
  rw [hnorm] at h₁ h₂
  exact h₁.trans h₂.symm

theorem gaussian_bubble_continuation_unique {t m : ℝ} (ht : 0 < t) (hm : 0 < m)
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F (bubbleCutDomain m))
    (hactual : ∀ P : ScalarMomentum, F (-((‖P‖ ^ 2 : ℝ) : ℂ)) = (gaussianBubbleEuclidean t m P : ℂ)) :
    EqOn F (gaussianBubbleContinuation t m) (bubbleCutDomain m) := by
  apply bubble_cut_continuation_unique hm hF (gaussian_bubble_continuation_holomorphic ht hm)
  intro w hw
  let P := scalarAxis (Real.sqrt w)
  have hnorm : ‖P‖ ^ 2 = w := by
    rw [show P = scalarAxis (Real.sqrt w) from rfl, scalarAxis_norm,
      abs_of_nonneg (Real.sqrt_nonneg w), Real.sq_sqrt hw]
  have h₁ := hactual P
  have h₂ := gaussian_bubble_continuation_actual ht hm P
  rw [hnorm] at h₁ h₂
  exact h₁.trans h₂.symm

/-- Source finite-normalization/entire-remainder proposition for the unique
analytic continuation of the actual Gaussian Euclidean bubble. The raw
four-dimensional integral is the matching condition fixing that continuation. -/
theorem gaussian_entire_bubble_remainder {t m : ℝ} (ht : 0 < t) (hm : 0 < m) :
    AnalyticOnNhd ℂ (gaussianBubbleContinuation t m) (bubbleCutDomain m) ∧
    (∀ P : ScalarMomentum, gaussianBubbleContinuation t m (-((‖P‖ ^ 2 : ℝ) : ℂ)) =
      (gaussianBubbleEuclidean t m P : ℂ)) ∧
    (∀ z : ℂ, (Real.exp (-2 * t * m ^ 2) : ℂ) *
      (gaussianBubbleContinuation t m z - gaussianBubbleContinuation t m 0) =
        standardBubble m z + gaussianRemainder t m z) ∧
    Differentiable ℂ (gaussianRemainder t m) ∧
    gaussianRemainder t m 0 = 0 ∧
    (∀ s : ℝ, (gaussianRemainder t m (s : ℂ)).im = 0) ∧
    (∀ z : ℂ, ‖gaussianRemainder t m z‖ ≤
      3 * t * ‖z‖ / (64 * Real.pi ^ 2) * Real.exp (t * ‖z‖)) := by
  refine ⟨gaussian_bubble_continuation_holomorphic ht hm, gaussian_bubble_continuation_actual ht hm,
    gaussian_bubble_finite_normalization t m, gaussian_remainder_entire ht.le,
    gaussian_remainder_zero t m, ?_, gaussian_remainder_norm_bound ht.le⟩
  intro s
  rw [gaussian_remainder_real]
  exact Complex.ofReal_im _

theorem complex_polynomial_real_axis_bound (p : Polynomial ℂ) {s : ℝ} (hs : 1 ≤ s) :
    ‖p.eval (s : ℂ)‖ ≤ (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖) * s ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  calc
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i * (s : ℂ) ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ * s ^ p.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (zero_le_one.trans hs)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hs (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
        (norm_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- Adding any actual finite complex polynomial cannot make the Gaussian
entire remainder polynomially bounded on the positive real axis. -/
theorem gaussian_remainder_add_polynomial_not_bounded {t m : ℝ} (ht : 0 < t) (p : Polynomial ℂ) :
    ¬ ∃ K : ℝ, ∃ N : ℕ, ∀ᶠ s : ℝ in atTop,
      ‖gaussianRemainder t m (s : ℂ) + p.eval (s : ℂ)‖ ≤ K * s ^ N := by
  rintro ⟨K, N, hb⟩
  let C : ℝ := ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => norm_nonneg (p.coeff i))
  apply gaussian_remainder_not_polynomially_bounded (m := m) ht
  refine ⟨|K| + C, N + p.natDegree, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with s hs hs1
  have hs0 : 0 ≤ s := zero_le_one.trans hs1
  have hleft : K * s ^ N ≤ |K| * s ^ (N + p.natDegree) := by
    calc
      _ ≤ |K| * s ^ N := mul_le_mul_of_nonneg_right (le_abs_self K) (pow_nonneg hs0 N)
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hs1 (Nat.le_add_right N p.natDegree)) (abs_nonneg K)
  have hright : ‖p.eval (s : ℂ)‖ ≤ C * s ^ (N + p.natDegree) :=
    (complex_polynomial_real_axis_bound p hs1).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hs1 (Nat.le_add_left p.natDegree N)) hC)
  calc
    _ ≤ ‖gaussianRemainder t m (s : ℂ) + p.eval (s : ℂ)‖ + ‖p.eval (s : ℂ)‖ := by
      simpa only [add_sub_cancel_right] using
        norm_sub_le (gaussianRemainder t m (s : ℂ) + p.eval (s : ℂ)) (p.eval (s : ℂ))
    _ ≤ |K| * s ^ (N + p.natDegree) + C * s ^ (N + p.natDegree) := add_le_add (hs.trans hleft) hright
    _ = _ := by ring

end UV
