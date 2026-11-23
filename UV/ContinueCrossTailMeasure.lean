import UV.VerifySpectrumCrossMeasure

/-! The absolute cross density and the total variation of its actual
Jordan measures. Here (s) is the spectral mass squared on the fixed
sector plane and (m₂=m^2). -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace UV.RevisionSpectrum

def crossTailDensity (a M m₂ s : ℝ) : ℝ :=
  |verifyCrossContinuum a M m₂ s|

def crossTailVariation (a M m₂ : ℝ) : Measure ℝ :=
  verifyCrossPositive a M m₂ + verifyCrossNegative a M m₂

def crossTailTransform (a M m₂ x : ℝ) : ℝ :=
  diagonalStieltjes (crossTailVariation a M m₂) x

theorem crossTailDensity_measurable (a M m₂ : ℝ) :
    Measurable (crossTailDensity a M m₂) :=
  continuous_abs.measurable.comp (verify_cross_continuum_measurable a M m₂)

theorem crossTailDensity_nonneg (a M m₂ s : ℝ) : 0 ≤ crossTailDensity a M m₂ s :=
  abs_nonneg _

theorem crossTailDensity_zero_below {a M m₂ s : ℝ} (hs : s ≤ M^2) :
    crossTailDensity a M m₂ s = 0 := by
  have h : ¬ (s = m₂ ∧ M^2 < m₂) := by rintro ⟨rfl, h⟩; exact h.not_ge hs
  simp [crossTailDensity, verifyCrossContinuum, h, crossDensity, not_lt_of_ge hs]

theorem crossTailDensity_large_bound {a M m₂ s : ℝ} (hs : 0 < s)
    (hM : M^2 < s) (hm : 2*m₂ ≤ s) :
    crossTailDensity a M m₂ s ≤ (2*Real.exp (a*M)/Real.pi)/s := by
  have hne : s ≠ m₂ := by
    intro he
    rw [← he] at hm
    linarith
  simpa only [crossTailDensity, verifyCrossContinuum, hne, false_and, if_false] using
    crossDensity_large_bound a M m₂ s hs hM hm

private theorem crossTail_ofReal_sum (r : ℝ) :
    ENNReal.ofReal r + ENNReal.ofReal (-r) = ENNReal.ofReal |r| := by
  rcases le_total r 0 with hr | hr
  · simp [ENNReal.ofReal_eq_zero.mpr hr, abs_of_nonpos hr]
  · simp [ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr hr), abs_of_nonneg hr]

theorem crossTailVariation_eq (a M m₂ : ℝ) :
    crossTailVariation a M m₂ =
      ENNReal.ofReal |verifyCrossResidue a M m₂| • Measure.dirac m₂ +
        volume.withDensity (fun s => ENNReal.ofReal (crossTailDensity a M m₂ s)) := by
  unfold crossTailVariation verifyCrossPositive verifyCrossNegative
  rw [add_add_add_comm, ← add_smul, crossTail_ofReal_sum, ← withDensity_add_left
    (verify_cross_continuum_measurable a M m₂).ennreal_ofReal, ← withDensity_indicator measurableSet_Ioi]
  congr 2
  funext s
  by_cases hs : M^2 < s
  · rw [indicator_of_mem (show s ∈ Ioi (M^2) from hs)]
    exact crossTail_ofReal_sum _
  · rw [indicator_of_notMem (show s ∉ Ioi (M^2) from hs), crossTailDensity_zero_below (not_lt.mp hs),
      ENNReal.ofReal_zero]

theorem crossTailVariation_cutoff_Icc_eq_Iic {a M m₂ : ℝ} (hm₂ : 0 ≤ m₂) (x : ℝ) :
    (crossTailVariation a M m₂).real (Icc 0 x) =
      (crossTailVariation a M m₂).real (Iic x) := by
  have h := verify_cross_jordan_support (a := a) (M := M) hm₂
  have hs : ∀ᵐ s ∂crossTailVariation a M m₂, 0 ≤ s := ae_add_measure_iff.2 h
  rw [measureReal_def, measureReal_def]
  congr 1
  apply measure_congr
  filter_upwards [hs] with s hs
  exact show (0 ≤ s ∧ s ≤ x) = (s ≤ x) from propext (and_iff_right hs)

theorem crossTailDensity_weight_integrable {a M m₂ x : ℝ} (ha : 0 < a)
    (hm₂ : 0 ≤ m₂) (hx : 0 < x)
    (hadm : m₂ ≤ M^2 ∨ Real.sin (a*Real.sqrt (m₂-M^2)) = 0) :
    Integrable (fun s => crossTailDensity a M m₂ s * stieltjesWeight x s) := by
  have h := (verify_cross_stieltjes ha hm₂ hx hadm).1.norm
  have hI : IntegrableOn (fun s => crossTailDensity a M m₂ s * stieltjesWeight x s)
      (Ioi (M^2)) := by
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hz : 0 < x+s := add_pos_of_pos_of_nonneg hx ((sq_nonneg M).trans hs.le)
    simp [Real.norm_eq_abs, crossTailDensity, stieltjesWeight, abs_of_pos hz, div_eq_mul_inv]
  apply (hI.integrable_indicator measurableSet_Ioi).congr
  filter_upwards with s
  by_cases hs : M^2 < s
  · exact indicator_of_mem (show s ∈ Ioi (M^2) from hs) _
  · rw [indicator_of_notMem (show s ∉ Ioi (M^2) from hs), crossTailDensity_zero_below (not_lt.mp hs),
      zero_mul]

theorem crossTailDensity_integrableOn_Iic {a M m₂ : ℝ} (ha : 0 < a)
    (hm₂ : 0 ≤ m₂) (hadm : m₂ ≤ M^2 ∨ Real.sin (a*Real.sqrt (m₂-M^2)) = 0) (x : ℝ) :
    IntegrableOn (crossTailDensity a M m₂) (Iic x) := by
  have h := (crossTailDensity_weight_integrable ha hm₂ zero_lt_one hadm).const_mul (1+max x 0)
  apply h.integrableOn.mono'
    (crossTailDensity_measurable a M m₂).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Iic] with s hs
  rw [Real.norm_of_nonneg (crossTailDensity_nonneg _ _ _ _)]
  by_cases hₛ : 0 ≤ s
  · have hpos : 0 < 1+s := by positivity
    have hfac : 1 ≤ (1+max x 0) * stieltjesWeight 1 s := by
      rw [stieltjesWeight, ← div_eq_mul_inv, le_div_iff₀ hpos]
      simpa only [one_mul, add_le_add_iff_left] using (mem_Iic.mp hs).trans (le_max_left x 0)
    rw [mul_left_comm]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hfac (crossTailDensity_nonneg a M m₂ s)
  · rw [crossTailDensity_zero_below ((le_of_not_ge hₛ).trans (sq_nonneg M)), zero_mul, mul_zero]

theorem crossTailTransform_eq {a M m₂ x : ℝ} (ha : 0 < a) (hm₂ : 0 ≤ m₂) (hx : 0 < x)
    (hadm : m₂ ≤ M^2 ∨ Real.sin (a*Real.sqrt (m₂-M^2)) = 0) :
    crossTailTransform a M m₂ x =
      |verifyCrossResidue a M m₂| * stieltjesWeight x m₂ +
        ∫ s, crossTailDensity a M m₂ s * stieltjesWeight x s := by
  have hd := crossTailDensity_measurable a M m₂
  have hi := crossTailDensity_weight_integrable ha hm₂ hx hadm
  have hν : Integrable (stieltjesWeight x)
      (volume.withDensity fun s => ENNReal.ofReal (crossTailDensity a M m₂ s)) := by
    rw [integrable_withDensity_iff_integrable_smul' hd.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simpa only [ENNReal.toReal_ofReal (crossTailDensity_nonneg _ _ _ _), smul_eq_mul] using hi
  have hatom : Integrable (stieltjesWeight x)
      (ENNReal.ofReal |verifyCrossResidue a M m₂| • Measure.dirac m₂) :=
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  rw [crossTailTransform, crossTailVariation_eq, diagonalStieltjes, integral_add_measure hatom hν,
    integral_smul_measure, integral_dirac,
    integral_withDensity_eq_integral_toReal_smul hd.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (crossTailDensity_nonneg _ _ _ _),
    ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]

theorem crossTailVariation_cutoff_eq {a M m₂ : ℝ} (ha : 0 < a) (hm₂ : 0 ≤ m₂)
    (hadm : m₂ ≤ M^2 ∨ Real.sin (a*Real.sqrt (m₂-M^2)) = 0) {x : ℝ} (hx : m₂ ≤ x) :
    (crossTailVariation a M m₂).real (Iic x) =
      |verifyCrossResidue a M m₂| + ∫ s in Iic x, crossTailDensity a M m₂ s := by
  have hi := crossTailDensity_integrableOn_Iic ha hm₂ hadm x
  have hfin : (∫⁻ s in Iic x, ENNReal.ofReal (crossTailDensity a M m₂ s)) < ∞ :=
    (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun s => crossTailDensity_nonneg a M m₂ s)).1 hi.2
  rw [crossTailVariation_eq, measureReal_def, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (show m₂ ∈ Iic x from hx), smul_eq_mul, mul_one,
    withDensity_apply _ measurableSet_Iic, ENNReal.toReal_add ENNReal.ofReal_ne_top hfin.ne,
    ENNReal.toReal_ofReal (abs_nonneg _)]
  exact congrArg (_ + ·) (integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun s => crossTailDensity_nonneg a M m₂ s) hi.1).symm

end UV.RevisionSpectrum
