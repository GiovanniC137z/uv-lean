import UV.BesselMoments
import UV.RevisionJointHeatMoments

/-! The declared depth-selector law and its exact normalization, moments and
Laplace multiplier. The integration variable is strictly positive depth. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal BigOperators

namespace UV.RevisionJointHeat

/-- Unnormalized selector with its actual collective-measure power. -/
def selectorDensity (A B v r : ℝ) : ℝ := r ^ (v - 1) * exp (-(A * r + B / r))

def selectorZ (A B v : ℝ) : ℝ := ∫ r in Ioi 0, selectorDensity A B v r

private theorem selectorDensity_nonneg (A B v : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ selectorDensity A B v r :=
  mul_nonneg (Real.rpow_nonneg hr _) (exp_nonneg _)

/-- The shifted exponential endpoint alone suffices at positive order. -/
private theorem selectorDensity_integrable_pos {A B v : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hv : 0 < v) :
    IntegrableOn (selectorDensity A B v) (Ioi 0) := by
  have he := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1)
    (s := v - 1) (by linarith) le_rfl hA
  apply he.mono' (by unfold selectorDensity; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  dsimp [selectorDensity]
  rw [abs_of_nonneg (by simpa only [selectorDensity] using selectorDensity_nonneg A B v hr.le), Real.rpow_one, neg_mul]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hr.le _)
  exact exp_le_exp.mpr (by linarith [div_nonneg hB hr.le])

private theorem selectorDensity_inv (A B v : ℝ) {r : ℝ} (hr : 0 < r) :
    (|(-1 : ℝ)| * r ^ ((-1 : ℝ) - 1)) • selectorDensity B A (-v) (r ^ (-1 : ℝ)) =
      selectorDensity A B v r := by
  unfold selectorDensity
  simp only [abs_neg, abs_one, one_mul, smul_eq_mul]
  rw [← Real.rpow_mul hr.le, ← mul_assoc, ← Real.rpow_add hr]
  congr 1
  · congr 1
    ring
  · rw [Real.rpow_neg_one]
    congr 1
    field_simp
    ring

theorem selectorDensity_integrable {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (v : ℝ) :
    IntegrableOn (selectorDensity A B v) (Ioi 0) := by
  rcases lt_trichotomy 0 v with hv | rfl | hv
  · exact selectorDensity_integrable_pos hA hB.le hv
  · have hn : IntegrableOn (selectorDensity A B (-1)) (Ioi 0) := by
      apply ((integrableOn_Ioi_comp_rpow_iff (selectorDensity B A (-(-1)))
        (p := -1) (by norm_num)).mpr (selectorDensity_integrable_pos hB hA.le (by norm_num))).congr_fun
        (fun _ hr => selectorDensity_inv A B (-1) hr) measurableSet_Ioi
    have hp : IntegrableOn (selectorDensity A B 1) (Ioi 0) :=
      selectorDensity_integrable_pos hA hB.le one_pos
    apply (hp.add hn).mono' (by unfold selectorDensity; fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hx : r ^ (0 - 1 : ℝ) ≤ r ^ (1 - 1 : ℝ) + r ^ (-1 - 1 : ℝ) := by
      convert inversePower_lower_order (show (0 : ℝ) ≤ 1 by norm_num)
        (show (1 : ℝ) ≤ 2 by norm_num) hr using 1 <;> norm_num
    dsimp [selectorDensity]
    rw [abs_of_nonneg (by simpa only [selectorDensity] using selectorDensity_nonneg A B 0 hr.le), ← add_mul]
    exact mul_le_mul_of_nonneg_right hx (exp_nonneg _)
  · apply ((integrableOn_Ioi_comp_rpow_iff (selectorDensity B A (-v))
      (p := -1) (by norm_num)).mpr (selectorDensity_integrable_pos hB hA.le (by linarith))).congr_fun
      (fun _ hr => selectorDensity_inv A B v hr) measurableSet_Ioi

theorem selectorZ_pos {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (v : ℝ) :
    0 < selectorZ A B v := by
  unfold selectorZ
  have hpos : ∀ r ∈ Ioi (0 : ℝ), 0 < selectorDensity A B v r := by
    intro r hr
    unfold selectorDensity
    exact mul_pos (Real.rpow_pos_of_pos hr _) (exp_pos _)
  rw [integral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_mem measurableSet_Ioi).mono fun _ h => (hpos _ h).le)
    (selectorDensity_integrable hA hB v)]
  have hsub : Ioo (0 : ℝ) 1 ⊆ Ioi 0 ∩ Function.support (selectorDensity A B v) := by
    intro r hr
    exact ⟨hr.1, (hpos _ hr.1).ne'⟩
  rw [Measure.restrict_apply' measurableSet_Ioi]
  have hm : (0 : ℝ≥0∞) < volume (Ioo (0 : ℝ) 1) := by simp
  exact hm.trans_le (measure_mono (by simpa only [inter_comm] using hsub))

/-- Positive scaling of the Schläfli integral gives the exact normalization. -/
theorem selectorZ_bessel {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (v : ℝ) :
    selectorZ A B v = 2 * (B / A) ^ (v / 2) * modifiedBesselK v (2 * sqrt (A * B)) := by
  let s := sqrt (B / A)
  have hs : 0 < s := sqrt_pos.mpr (div_pos hB hA)
  have hAs : A * s = sqrt (A * B) := by
    have hsq : s ^ 2 = B / A := sq_sqrt (by positivity)
    have hsq' : (A * s) ^ 2 = A * B := by
      rw [mul_pow, hsq]
      field_simp
    apply (sq_eq_sq₀ (mul_nonneg hA.le hs.le) (sqrt_nonneg _)).mp
    rw [hsq', sq_sqrt (by positivity)]
  have hBs : B / s = sqrt (A * B) := by
    rw [← hAs, div_eq_iff hs.ne']
    have hsq : s ^ 2 = B / A := sq_sqrt (by positivity)
    rw [mul_assoc, ← pow_two, hsq]
    field_simp
  unfold selectorZ
  calc
    _ = s * ∫ t in Ioi 0, selectorDensity A B v (s * t) := by
      rw [integral_comp_mul_left_Ioi (selectorDensity A B v) 0 hs,
        smul_eq_mul, mul_zero, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
    _ = s * ∫ t : ℝ in Ioi 0, s ^ (v - 1) * (t ^ (v - 1) *
        exp (-(sqrt (A * B)) * (t + t⁻¹))) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      unfold selectorDensity
      dsimp only
      rw [Real.mul_rpow hs.le ht.le]
      have h : A * (s * t) + B / (s * t) = sqrt (A * B) * (t + t⁻¹) := by
        rw [← mul_assoc, hAs, ← div_div, hBs, div_eq_mul_inv, mul_add]
      rw [h]
      ring_nf
    _ = _ := by
      have hsProd : s * s ^ (v - 1) = s ^ v := by
        conv_lhs =>
          arg 1
          rw [← Real.rpow_one s]
        rw [← Real.rpow_add hs]
        congr 1
        ring
      rw [integral_const_mul, ← mul_assoc, hsProd]
      have hpow : s ^ v = (B / A) ^ (v / 2) := by
        dsimp [s]
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
        congr 1
        ring
      rw [hpow]
      unfold modifiedBesselK
      rw [show 2 * sqrt (A * B) / 2 = sqrt (A * B) by ring]
      ring

/-- Probability density with respect to positive-depth Lebesgue measure. -/
def selectorLaw (A B v : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun r => ENNReal.ofReal (selectorDensity A B v r / selectorZ A B v))

theorem selectorLaw_lintegral (A B v : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hZ : 0 < selectorZ A B v) :
    (∫⁻ r, ENNReal.ofReal (f r) ∂selectorLaw A B v) =
      ENNReal.ofReal ((selectorZ A B v)⁻¹) *
        ∫⁻ r in Ioi 0, ENNReal.ofReal (f r * selectorDensity A B v r) := by
  have hdm : Measurable (selectorDensity A B v) := by unfold selectorDensity; fun_prop
  unfold selectorLaw
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf.ennreal_ofReal,
    ← lintegral_const_mul _ (hf.mul hdm).ennreal_ofReal]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hd := selectorDensity_nonneg A B v hr.le
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hZ.le), ← ENNReal.ofReal_mul (div_nonneg hd hZ.le)]
  congr 1
  ring

theorem selectorLaw_probability {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (v : ℝ) :
    IsProbabilityMeasure (selectorLaw A B v) := by
  constructor
  rw [← lintegral_one]
  have hZ := selectorZ_pos hA hB v
  have hp := selectorLaw_lintegral A B v (fun _ => 1) measurable_const hZ
  simp only [ENNReal.ofReal_one, one_mul] at hp
  rw [hp, ← ofReal_integral_eq_lintegral_ofReal (selectorDensity_integrable hA hB v)
    ((ae_restrict_mem measurableSet_Ioi).mono fun r hr => selectorDensity_nonneg A B v hr.le),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hZ.le)]
  change ENNReal.ofReal ((selectorZ A B v)⁻¹ * selectorZ A B v) = 1
  simp [hZ.ne']

private theorem selectorLaw_ae_pos (A B v : ℝ) : ∀ᵐ r ∂selectorLaw A B v, 0 < r := by
  rw [ae_iff]
  have he : {r : ℝ | ¬ 0 < r} = Iic 0 := by ext; simp
  rw [he, selectorLaw, withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  rw [show Iic (0 : ℝ) ∩ Ioi 0 = ∅ by
    ext r
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false]
    exact ⟨fun h => (not_lt_of_ge h.1) h.2, False.elim⟩,
    Measure.restrict_empty, lintegral_zero_measure]

private theorem selectorLaw_integral (A B v : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hZ : 0 < selectorZ A B v) (hfn : ∀ r > 0, 0 ≤ f r)
    (hi : IntegrableOn (fun r => f r * selectorDensity A B v r) (Ioi 0)) :
    Integrable f (selectorLaw A B v) ∧
      (∫ r, f r ∂selectorLaw A B v) =
        (∫ r in Ioi 0, f r * selectorDensity A B v r) / selectorZ A B v := by
  have h := selectorLaw_lintegral A B v f hf hZ
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    ((ae_restrict_mem measurableSet_Ioi).mono fun r hr => by
      exact mul_nonneg (hfn r hr) (selectorDensity_nonneg A B v hr.le))] at h
  have hae := (selectorLaw_ae_pos A B v).mono fun r hr => hfn r hr
  have hi' := (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable hae).mp
    (h ▸ ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  refine ⟨hi', ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi' hae] at h
  have hn : 0 ≤ ∫ (r : ℝ) in Ioi 0, f r * selectorDensity A B v r := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg (hfn r hr) (selectorDensity_nonneg A B v hr.le)
  simpa only [ENNReal.toReal_ofReal (integral_nonneg_of_ae hae), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hZ.le), ENNReal.toReal_ofReal hn, div_eq_inv_mul]
    using congrArg ENNReal.toReal h

/-- All real moments are actual Bochner integrals of the selector law. -/
theorem selectorLaw_moment_Z {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (v u : ℝ) :
    Integrable (fun r => r ^ u) (selectorLaw A B v) ∧
    (∫ r, r ^ u ∂selectorLaw A B v) = selectorZ A B (v + u) / selectorZ A B v := by
  have he : (fun r : ℝ => r ^ u * selectorDensity A B v r) =ᵐ[volume.restrict (Ioi 0)]
      selectorDensity A B (v + u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simp only [selectorDensity, ← mul_assoc, ← Real.rpow_add hr]
    congr 2
    ring
  have hh := selectorLaw_integral A B v (fun r => r ^ u) (by fun_prop) (selectorZ_pos hA hB v)
    (fun _ hr => Real.rpow_nonneg hr.le _) ((selectorDensity_integrable hA hB (v + u)).congr he.symm)
  exact ⟨hh.1, hh.2.trans (congrArg (fun x => x / selectorZ A B v) (integral_congr_ae he))⟩

/-- Exact Bessel-K moment ratio from the source. -/
theorem selectorLaw_moment_bessel {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (v u : ℝ) :
    (∫ r, r ^ u ∂selectorLaw A B v) = (B / A) ^ (u / 2) *
      (modifiedBesselK (v + u) (2 * sqrt (A * B)) / modifiedBesselK v (2 * sqrt (A * B))) := by
  rw [(selectorLaw_moment_Z hA hB v u).2, selectorZ_bessel hA hB (v + u), selectorZ_bessel hA hB v]
  have hp : 0 < B / A := div_pos hB hA
  rw [add_div, Real.rpow_add hp]
  have hK : modifiedBesselK v (2 * sqrt (A * B)) ≠ 0 := by
    intro h
    have hZ := selectorZ_pos hA hB v
    rw [selectorZ_bessel hA hB, h, mul_zero] at hZ
    exact (lt_irrefl _) hZ
  field_simp [hK, (Real.rpow_pos_of_pos hp (v / 2)).ne']

/-- The margin is the Laplace transform of the same positive-depth law. -/
def selectorTransform (A B v ω : ℝ) : ℝ := ∫ r, exp (-ω * r) ∂selectorLaw A B v

theorem selectorTransform_Z {A B ω : ℝ} (hA : 0 < A) (hB : 0 < B) (hω : 0 ≤ ω) (v : ℝ) :
    selectorTransform A B v ω = selectorZ (A + ω) B v / selectorZ A B v := by
  have he : (fun r : ℝ => exp (-ω * r) * selectorDensity A B v r) =
      selectorDensity (A + ω) B v := by
    funext r
    unfold selectorDensity
    rw [mul_left_comm, ← exp_add]
    congr 2
    ring
  unfold selectorTransform
  have hh := selectorLaw_integral A B v (fun r => exp (-ω * r)) (by fun_prop) (selectorZ_pos hA hB v)
    (fun _ _ => exp_nonneg _) (he.symm ▸ selectorDensity_integrable (by linarith) hB v)
  rw [he] at hh
  exact hh.2

theorem selectorTransform_bessel {A B ω : ℝ} (hA : 0 < A) (hB : 0 < B) (hω : 0 ≤ ω) (v : ℝ) :
    selectorTransform A B v ω = (A / (A + ω)) ^ (v / 2) *
      (modifiedBesselK v (2 * sqrt (B * (A + ω))) / modifiedBesselK v (2 * sqrt (A * B))) := by
  have hAω : 0 < A + ω := by linarith
  have hx : B / (A + ω) = (A / (A + ω)) * (B / A) := by field_simp
  rw [selectorTransform_Z hA hB hω, selectorZ_bessel hAω hB, selectorZ_bessel hA hB,
    hx, Real.mul_rpow (by positivity) (by positivity), mul_comm _ B]
  have hK : modifiedBesselK v (2 * sqrt (A * B)) ≠ 0 := by
    intro h
    have hZ := selectorZ_pos hA hB v
    rw [selectorZ_bessel hA hB, h, mul_zero] at hZ
    exact (lt_irrefl _) hZ
  field_simp [hK, (Real.rpow_pos_of_pos (div_pos hB hA) (v / 2)).ne']

/-- At zero inverse depth coefficient the unnormalized density is integrable
exactly at positive collective order. -/
theorem selectorDensity_zero_integrable_iff {A v : ℝ} (hA : 0 < A) :
    IntegrableOn (selectorDensity A 0 v) (Ioi 0) ↔ 0 < v := by
  refine ⟨?_, selectorDensity_integrable_pos hA le_rfl⟩
  intro hi
  have hI := (hi.mono_set (Ioo_subset_Ioi_self : Ioo (0 : ℝ) 1 ⊆ Ioi 0)).const_mul (exp A)
  have hp : IntegrableOn (fun r : ℝ => r ^ (v - 1)) (Ioo 0 1) := by
    apply hI.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hn := Real.rpow_nonneg (le_of_lt hr.1) (v - 1)
    rw [Real.norm_of_nonneg hn]
    unfold selectorDensity
    rw [zero_div, add_zero, mul_left_comm, ← exp_add]
    conv_lhs => rw [← mul_one (r ^ (v - 1))]
    apply mul_le_mul_of_nonneg_left _ hn
    rw [← exp_zero]
    apply exp_le_exp.mpr
    nlinarith [mul_nonneg hA.le (sub_nonneg.mpr hr.2.le)]
  have hp' := (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mp hp
  linarith

theorem selectorZ_zero_gamma {A v : ℝ} (hA : 0 < A) (hv : 0 < v) :
    selectorZ A 0 v = A ^ (-v) * Gamma v := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := v - 1)
    one_pos (by linarith) hA
  simpa [selectorZ, selectorDensity, neg_mul, Real.rpow_one] using h

/-- Exact inverse-depth integrability threshold at the gamma endpoint. The
criterion also covers arbitrary real test exponents `u`. -/
theorem selectorLaw_zero_inverseMoment_iff {A v : ℝ} (hA : 0 < A) (hv : 0 < v) (u : ℝ) :
    Integrable (fun r => r ^ (-u)) (selectorLaw A 0 v) ↔ u < v := by
  have hZ : 0 < selectorZ A 0 v := by
    rw [selectorZ_zero_gamma hA hv]
    exact mul_pos (Real.rpow_pos_of_pos hA _) (Gamma_pos_of_pos hv)
  have hm : Measurable (fun r : ℝ => r ^ (-u)) := by fun_prop
  have hd : Measurable (selectorDensity A 0 (v - u)) := by unfold selectorDensity; fun_prop
  have hmeq : (∫⁻ r, ENNReal.ofReal (r ^ (-u)) ∂selectorLaw A 0 v) =
      ENNReal.ofReal ((selectorZ A 0 v)⁻¹) *
        ∫⁻ r in Ioi 0, ENNReal.ofReal (selectorDensity A 0 (v - u) r) := by
    rw [selectorLaw_lintegral A 0 v _ hm hZ]
    congr 1
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp only [selectorDensity, ← mul_assoc, ← Real.rpow_add hr]
    congr 3
    ring
  rw [← lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    ((selectorLaw_ae_pos A 0 v).mono fun _ hr => Real.rpow_nonneg hr.le _), hmeq]
  have hn : ENNReal.ofReal ((selectorZ A 0 v)⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr hZ)
  have he (m : ℝ≥0∞) : ENNReal.ofReal ((selectorZ A 0 v)⁻¹) * m ≠ ⊤ ↔ m ≠ ⊤ := by
    simp only [ne_eq, ENNReal.mul_eq_top, hn, ENNReal.ofReal_ne_top, not_false_eq_true, true_and, false_and, or_false]
  rw [he]
  rw [lintegral_ofReal_ne_top_iff_integrable hd.aestronglyMeasurable
    ((ae_restrict_mem measurableSet_Ioi).mono fun _ hr => selectorDensity_nonneg A 0 (v - u) hr.le),
    ← IntegrableOn, selectorDensity_zero_integrable_iff hA, sub_pos]

end UV.RevisionJointHeat
