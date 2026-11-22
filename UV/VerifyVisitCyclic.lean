import UV.RevisionBoundaryHeat
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Group.Integral

/-! Integrating the basepoint in the free normal trace tests coincidence
at every relative position. The normal coordinate and its Lebesgue
measure are the same on both half-time legs. -/

noncomputable section

open MeasureTheory Filter Set Real
open scoped ENNReal Topology

namespace UV.VerifyVisitCyclic

open UV.RevisionBoundary

def relativeNormal (p : ℝ × ℝ) : ℝ := p.2 - p.1

private theorem relative_normal_measurable : Measurable relativeNormal := by
  unfold relativeNormal
  fun_prop

def cyclicJointReturn (T : ℝ) (μ : Measure (ℝ × ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) *
    ∫⁻ t in Ioc 0 T, ∫⁻ p, ENNReal.ofReal (returnIntegrand (relativeNormal p) t) ∂μ

/-- Moving to the measured relative coordinate is an exact
pushforward of the common joint law of the two positions. -/
theorem cyclic_joint_return_eq (T : ℝ) (μ : Measure (ℝ × ℝ)) :
    cyclicJointReturn T μ = integratedNormalReturn T (μ.map relativeNormal) := by
  unfold cyclicJointReturn integratedNormalReturn
  congr 1
  apply lintegral_congr
  intro t
  rw [lintegral_map (by unfold returnIntegrand; fun_prop) relative_normal_measurable]

theorem cyclic_joint_relative_diagonal_criterion {T : ℝ} (hT : 0 < T)
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] :
    cyclicJointReturn T μ ≠ ⊤ ↔
      μ {p | p.2 = p.1} = 0 ∧
        IntegrableOn (fun p : ℝ × ℝ => 1 / (p.2 - p.1) ^ (2 : ℕ))
          (relativeNormal ⁻¹' Icc (-1) 1) μ := by
  letI : IsFiniteMeasure (μ.map relativeNormal) := Measure.isFiniteMeasure_map μ _
  rw [cyclic_joint_return_eq, marked_return_finiteness_iff hT, Measure.map_apply
    relative_normal_measurable (measurableSet_singleton _)]
  have hD : relativeNormal ⁻¹' {(0 : ℝ)} = {p : ℝ × ℝ | p.2 = p.1} := by
    ext p
    simp [relativeNormal, sub_eq_zero]
  rw [hD]
  apply and_congr_right
  intro _
  rw [IntegrableOn, Measure.restrict_map relative_normal_measurable measurableSet_Icc]
  exact integrable_map_measure (show Measurable (fun x : ℝ => 1 / x ^ (2 : ℕ)) by fun_prop).aestronglyMeasurable
    relative_normal_measurable.aemeasurable

def cyclicPairDensity (t : ℝ) (n : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-(relativeNormal p) ^ (2 : ℕ) / t) / (2 * Real.pi * t) * n p.2

private theorem translate_gaussian_integral (y : ℝ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun r : ℝ => Real.exp (-(y - r) ^ (2 : ℕ) / t)) ∧
      (∫ r : ℝ, Real.exp (-(y - r) ^ (2 : ℕ) / t)) = Real.sqrt (Real.pi * t) := by
  let g := fun r : ℝ => Real.exp (-(1 / t) * r ^ (2 : ℕ))
  have heq (r : ℝ) : Real.exp (-(y - r) ^ (2 : ℕ) / t) = g (y - r) := by
    unfold g
    congr 1
    ring
  have hi : Integrable g := integrable_exp_neg_mul_sq (one_div_pos.mpr ht)
  refine ⟨?_, ?_⟩
  · simp_rw [heq]
    exact (volume.measurePreserving_sub_left y).integrable_comp
      hi.aestronglyMeasurable |>.mpr hi
  · simp_rw [heq]
    rw [integral_sub_left_eq_self g volume y]
    unfold g
    rw [integral_gaussian, div_div_eq_mul_div, div_one]

private theorem gaussian_basepoint_density (y : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫⁻ r : ℝ, ENNReal.ofReal (Real.exp (-(y - r) ^ (2 : ℕ) / t) / (2 * Real.pi * t))) =
      ENNReal.ofReal ((Real.sqrt (4 * Real.pi * t))⁻¹) := by
  have hden : 0 < 2 * Real.pi * t := by positivity
  have hg := (translate_gaussian_integral y ht).1.div_const (2 * Real.pi * t)
  rw [← ofReal_integral_eq_lintegral_ofReal hg (Eventually.of_forall fun _ =>
    div_nonneg (Real.exp_nonneg _) hden.le), integral_div,
    (translate_gaussian_integral y ht).2]
  congr 1
  have hpt : 0 < Real.pi * t := mul_pos Real.pi_pos ht
  have hroot : Real.sqrt (4 * Real.pi * t) = 2 * Real.sqrt (Real.pi * t) := by
    rw [mul_assoc, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [← show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h4]
  rw [hroot]
  field_simp [(Real.sqrt_pos.mpr hpt).ne', Real.pi_ne_zero, ht.ne']
  nlinarith [Real.sq_sqrt hpt.le]

/-- The actual unconstrained basepoint integral of the midpoint
insertion has the free one-dimensional diagonal heat normalization. -/
theorem cyclic_gaussian_insertion_exact {t : ℝ} (ht : 0 < t) {n : ℝ → ℝ}
    (hn : Measurable n) (hn0 : ∀ y, 0 ≤ n y) (hni : Integrable n)
    (hnorm : (∫ y : ℝ, n y) = 1) :
    Integrable (cyclicPairDensity t n) ((volume : Measure ℝ).prod volume) ∧
      (∫ p : ℝ × ℝ, cyclicPairDensity t n p ∂(volume.prod volume)) =
        (Real.sqrt (4 * Real.pi * t))⁻¹ := by
  let f := cyclicPairDensity t n
  have hm : Measurable f := by unfold f cyclicPairDensity relativeNormal; fun_prop
  have hpos : ∀ p, 0 ≤ f p := fun p =>
    mul_nonneg (div_nonneg (Real.exp_nonneg _) (by positivity)) (hn0 p.2)
  have hF : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (f p) ∂(volume.prod volume)) =
      ENNReal.ofReal ((Real.sqrt (4 * Real.pi * t))⁻¹) := by
    rw [lintegral_prod_symm' _ hm.ennreal_ofReal]
    have hinner (y : ℝ) :
        (∫⁻ r : ℝ, ENNReal.ofReal (f (r, y))) =
          ENNReal.ofReal (n y) * ENNReal.ofReal ((Real.sqrt (4 * Real.pi * t))⁻¹) := by
      have he (r : ℝ) : ENNReal.ofReal (f (r, y)) = ENNReal.ofReal (n y) *
          ENNReal.ofReal (Real.exp (-(y - r) ^ (2 : ℕ) / t) / (2 * Real.pi * t)) := by
        change ENNReal.ofReal ((Real.exp (-(y - r) ^ (2 : ℕ) / t) / (2 * Real.pi * t)) * n y) = _
        rw [mul_comm, ENNReal.ofReal_mul (hn0 y)]
      simp_rw [he]
      rw [lintegral_const_mul _ (by fun_prop), gaussian_basepoint_density y ht]
    simp_rw [hinner]
    rw [lintegral_mul_const _ hn.ennreal_ofReal, ← ofReal_integral_eq_lintegral_ofReal hni
      (Eventually.of_forall hn0), hnorm, ENNReal.ofReal_one, one_mul]
  have hi : Integrable f ((volume : Measure ℝ).prod volume) :=
    (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
      (Eventually.of_forall hpos)).mp (hF.trans_ne ENNReal.ofReal_ne_top)
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hpos)] at hF
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hpos) (by positivity)).mp hF

/-- The full cyclic trace retains the short-time magnetic divergence
even when the normalized insertion has a node. -/
theorem cyclic_normal_trace_time_diverges {T : ℝ} (hT : 0 < T) :
    (∫⁻ t in Ioc (0 : ℝ) T,
      ENNReal.ofReal ((Real.sqrt (4 * Real.pi * t))⁻¹ / t)) = ⊤ := by
  by_contra hfin
  have hm : Measurable (fun t : ℝ => (Real.sqrt (4 * Real.pi * t))⁻¹ / t) := by fun_prop
  have hi : IntegrableOn (fun t => (Real.sqrt (4 * Real.pi * t))⁻¹ / t) (Ioc 0 T) :=
    (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact div_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) ht.1.le)).mp hfin
  let s := min T 1
  have hs : 0 < s := lt_min hT one_pos
  have hi' : IntegrableOn (fun t : ℝ => t ^ (-1 : ℝ)) (Ioo 0 s) := by
    refine ((hi.mono_set (Ioo_subset_Ioc_self.trans (Ioc_subset_Ioc_right (min_le_left _ _)))).const_mul
      (Real.sqrt (4 * Real.pi))).mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht1 : t ≤ 1 := ht.2.le.trans (min_le_right _ _)
    have hc : 0 < Real.sqrt (4 * Real.pi * t) := Real.sqrt_pos.mpr
      (mul_pos (mul_pos (by norm_num) Real.pi_pos) ht.1)
    rw [Real.rpow_neg_one, Real.norm_of_nonneg (inv_nonneg.mpr ht.1.le)]
    change t⁻¹ ≤ Real.sqrt (4 * Real.pi) * ((Real.sqrt (4 * Real.pi * t))⁻¹ / t)
    have hcomp : Real.sqrt (4 * Real.pi * t) ≤ Real.sqrt (4 * Real.pi) :=
      Real.sqrt_le_sqrt (mul_le_of_le_one_right (by positivity) ht1)
    rw [← mul_div_assoc, ← div_eq_mul_inv, ← one_div t]
    apply div_le_div_of_nonneg_right _ ht.1.le
    exact (le_div_iff₀ hc).mpr (by simpa using hcomp)
  exact (lt_irrefl (-1 : ℝ)) ((intervalIntegral.integrableOn_Ioo_rpow_iff hs).mp hi')

end UV.VerifyVisitCyclic
