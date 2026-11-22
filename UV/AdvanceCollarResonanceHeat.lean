import UV.AdvanceCollarResonanceBump
import UV.AdvanceCollarResonanceScale
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-! Spectral Jensen and the localized weighted norm estimate for the
literal unit bump at a collar resonance. The heat comparison and the
spectral law are supplied by the positive heat realization. -/

noncomputable section

open MeasureTheory Set Filter Real
open scoped Topology ENNReal ContDiff

namespace UV.AdvanceCollarResonanceHeat

open UV.AdvanceCollarResonanceBump UV.AdvanceCollarResonanceScale
open UV.ResumeCollarSpectral (durationLog)

/-- Jensen on the positive spectral law of a normalized radial test. -/
theorem resonance_spectral_jensen (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 ≤ t) (henergy : Integrable (fun E : ℝ => E) μ)
    (hpos : ∀ᵐ E ∂μ, 0 ≤ E) :
    Real.exp (-t * ∫ E : ℝ, E ∂μ) ≤ ∫ E : ℝ, Real.exp (-t * E) ∂μ := by
  have hi : Integrable (fun E : ℝ => Real.exp (-t * E)) μ := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    filter_upwards [hpos] with E hE
    rw [Real.norm_of_nonneg (Real.exp_nonneg _), Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hE
  have h := convexOn_exp.map_integral_le (μ := μ)
    Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun E : ℝ => mem_univ (-t * E)) (henergy.const_mul (-t)) hi
  rwa [integral_const_mul] at h

def resonanceVacuum (Z w : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Ioc (0 : ℝ) 1, ENNReal.ofReal (Z r * w r ^ (2 : ℕ))

/-- A unit bump bounds the positive weighted norm from below by its
localized pairing, with the determinant restricted to the bump support. -/
theorem resonance_weighted_norm_ge_pairing {h z y : ℝ}
    (hh : 0 < h) (h2 : 2 * h ≤ 1) (hz : 0 ≤ z) (hy : 0 ≤ y)
    {Z w : ℝ → ℝ} (hw : Measurable w)
    (hw₂ : IntegrableOn (fun r => w r ^ (2 : ℕ)) (Ioc 0 1))
    (hw₀ : ∀ r ∈ Ioc 0 1, 0 ≤ w r)
    (hZ : ∀ r ∈ Icc h (2 * h), z ≤ Z r)
    (hpair : y ≤ ∫ r in Icc h (2 * h), resonanceBump h r * w r) :
    ENNReal.ofReal (z * y ^ (2 : ℕ)) ≤ resonanceVacuum Z w := by
  let S := Icc h (2 * h)
  let μ := volume.restrict S
  have hS : S ⊆ Ioc (0 : ℝ) 1 := fun _ hr => ⟨hh.trans_le hr.1, hr.2.trans h2⟩
  have hbcont := (resonance_bump_smooth h).continuous
  have hbi : Integrable (fun r => resonanceBump h r ^ (2 : ℕ)) μ :=
    ((hbcont.pow 2).integrableOn_Icc)
  have hwi : Integrable (fun r => w r ^ (2 : ℕ)) μ := hw₂.mono_set hS
  have hb : MemLp (resonanceBump h) 2 μ :=
    (memLp_two_iff_integrable_sq hbcont.aestronglyMeasurable).mpr hbi
  have hwl : MemLp w 2 μ := (memLp_two_iff_integrable_sq hw.aestronglyMeasurable).mpr hwi
  have hw₀' : 0 ≤ᵐ[μ] w := by
    filter_upwards [ae_restrict_mem (s := S) measurableSet_Icc] with r hr
    exact hw₀ r (hS hr)
  have hhld := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (resonance_bump_nonnegative h)) hw₀'
    (by simpa using hb) (by simpa using hwl)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hhld
  change (∫ r in Icc h (2 * h), resonanceBump h r * w r) ≤
    Real.sqrt (∫ r in Icc h (2 * h), resonanceBump h r ^ (2 : ℕ)) *
      Real.sqrt (∫ r in Icc h (2 * h), w r ^ (2 : ℕ)) at hhld
  rw [resonance_bump_norm hh, Real.sqrt_one, one_mul] at hhld
  have hsi : 0 ≤ ∫ r in Icc h (2 * h), w r ^ (2 : ℕ) :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hsq := (sq_le_sq₀ hy (Real.sqrt_nonneg _)).mpr (hpair.trans hhld)
  rw [Real.sq_sqrt hsi] at hsq
  have hzI : Integrable (fun r => z * w r ^ (2 : ℕ)) μ := hwi.const_mul z
  calc
    _ ≤ ENNReal.ofReal (∫ r in Icc h (2 * h), z * w r ^ (2 : ℕ)) := by
      rw [integral_const_mul]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hsq hz)
    _ = ∫⁻ r in Icc h (2 * h), ENNReal.ofReal (z * w r ^ (2 : ℕ)) :=
      ofReal_integral_eq_lintegral_ofReal hzI
        (Filter.Eventually.of_forall fun _ => mul_nonneg hz (sq_nonneg _))
    _ ≤ ∫⁻ r in Icc h (2 * h), ENNReal.ofReal (Z r * w r ^ (2 : ℕ)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (s := S) measurableSet_Icc] with r hr
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hZ r hr) (sq_nonneg _))
    _ ≤ resonanceVacuum Z w := lintegral_mono_set hS

set_option maxHeartbeats 650000 in
/-- At fixed positive duration the actual bump and spectral preparation
give the source logarithmic scale. All heat assumptions refer to the
same positive propagation used for the incoming vector and the test. -/
theorem resonance_prepared_vacuum_lower {A t : ℝ} (hA : 0 < A) (ht : 0 < t)
    {Z : ℝ → ℝ} (hZ : ∀ r ∈ Ioc 0 1,
      Real.exp (A / r ^ (2 : ℕ) * durationLog r ^ (3 : ℕ)) ≤ Z r)
    (heat : ℝ → (ℝ → ℝ) → ℝ → ℝ)
    (hHeat : ∀ ν, 0 < ν → Measurable (heat ν resonanceIncoming) ∧
      IntegrableOn (fun r => heat ν resonanceIncoming r ^ (2 : ℕ)) (Ioc 0 1) ∧
      (∀ r ∈ Ioc 0 1, 0 ≤ heat ν resonanceIncoming r))
    (hOrder : ∀ ν h, 0 < ν → 0 < h → 2 * h ≤ 1 → ∀ a : ℝ, 0 ≤ a →
      (∀ r ∈ Ioc 0 1, a * resonanceBump h r ≤ resonanceIncoming r) →
        ∀ r ∈ Ioc 0 1, a * heat ν (resonanceBump h) r ≤ heat ν resonanceIncoming r)
    (spectralLaw : ℝ → ℝ → Measure ℝ)
    (hSpectral : ∀ ν h, 0 < ν → 0 < h → 2 * h ≤ 1 →
      IsProbabilityMeasure (spectralLaw ν h) ∧
      (∀ᵐ E ∂spectralLaw ν h, 0 ≤ E) ∧
      Integrable (fun E : ℝ => E) (spectralLaw ν h) ∧
      (∫ E : ℝ, E ∂spectralLaw ν h) = resonanceEnergy ν (resonanceBump h) ∧
      (∫ r in Icc h (2 * h), resonanceBump h r * heat ν (resonanceBump h) r) =
        ∫ E : ℝ, Real.exp (-t * E) ∂spectralLaw ν h) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ ν in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (Real.exp (c * resonanceScale ν)) ≤
        resonanceVacuum Z (heat ν resonanceIncoming) := by
  obtain ⟨B, hB, hE⟩ := resonance_bump_energy_bound
  obtain ⟨d, hd, hdom⟩ := resonance_bump_incoming_dominance
  obtain ⟨K, c, hK, hc, hopt⟩ := resonance_bump_lower_scale hA hB (sq_pos_of_pos hd) ht
  refine ⟨c, hc, ?_⟩
  filter_upwards [hopt, self_mem_nhdsWithin] with ν hv hν
  have hν0 : 0 < ν := hν
  let h := resonanceRadius K ν
  have hh : 0 < h := hv.1
  have h2 : 2 * h ≤ 1 := hv.2.1
  let a := d * (h ^ (4 : ℕ) * Real.sqrt h)
  have ha : 0 ≤ a := by positivity
  let D := d ^ (2 : ℕ) * h ^ (9 : ℕ)
  have hD : 0 < D := by positivity
  have haD : a ^ (2 : ℕ) = D := by
    unfold a D
    rw [mul_pow, mul_pow, Real.sq_sqrt hh.le, ← pow_mul]
    ring
  let E := resonanceEnergy ν (resonanceBump h)
  let Emax := B * ((h ^ (2 : ℕ))⁻¹ + ν ^ (2 : ℕ) / h ^ (8 : ℕ) + ν / h ^ (5 : ℕ))
  have hEE : E ≤ Emax := (hE ν h hν0.le hh h2).2
  let z := Real.exp (c * resonanceScale ν + 2 * t * Emax - Real.log D)
  have hz : 0 ≤ z := Real.exp_nonneg _
  have hzl (r : ℝ) (hr : r ∈ Icc h (2 * h)) : z ≤ Z r := by
    refine (Real.exp_le_exp.mpr ?_).trans (hZ r ⟨hh.trans_le hr.1, hr.2.trans h2⟩)
    have hscale : c * resonanceScale ν ≤ Real.log D +
        A / r ^ (2 : ℕ) * durationLog r ^ (3 : ℕ) - 2 * t * Emax := by
      simpa only [D, h, Emax, mul_assoc] using hv.2.2 r hr
    linarith only [hscale]
  obtain ⟨hprob, hpos, hmean, hmeanE, hread⟩ := hSpectral ν h hν0 hh h2
  letI := hprob
  have hj := resonance_spectral_jensen (spectralLaw ν h) ht.le hmean hpos
  rw [hmeanE, ← hread] at hj
  have hdomH := hOrder ν h hν0 hh h2 a ha (hdom h hh h2)
  have hs : Icc h (2 * h) ⊆ Ioc (0 : ℝ) 1 :=
    fun r hr => ⟨hh.trans_le hr.1, hr.2.trans h2⟩
  have hiB : IntegrableOn (fun r => resonanceBump h r * heat ν (resonanceBump h) r)
      (Icc h (2 * h)) := by
    by_contra hi
    rw [integral_undef hi] at hj
    exact (not_le_of_gt (Real.exp_pos _)) hj
  obtain ⟨hwm, hwi, hw0⟩ := hHeat ν hν0
  have hbi : MemLp (resonanceBump h) 2 (volume.restrict (Icc h (2 * h))) := by
    apply (memLp_two_iff_integrable_sq (resonance_bump_smooth h).continuous.aestronglyMeasurable).2
    exact ((resonance_bump_smooth h).continuous.pow 2).integrableOn_Icc
  have hwi' : MemLp (heat ν resonanceIncoming) 2 (volume.restrict (Icc h (2 * h))) :=
    (memLp_two_iff_integrable_sq hwm.aestronglyMeasurable).2 (hwi.mono_set hs)
  have hiV : IntegrableOn (fun r => resonanceBump h r * heat ν resonanceIncoming r)
      (Icc h (2 * h)) := hbi.integrable_mul hwi'
  have hrp : a * Real.exp (-t * E) ≤
      ∫ r in Icc h (2 * h), resonanceBump h r * heat ν resonanceIncoming r := by
    refine (mul_le_mul_of_nonneg_left hj ha).trans ?_
    rw [← integral_const_mul]
    apply setIntegral_mono_on (hiB.const_mul a) hiV measurableSet_Icc
    intro r hr
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hdomH r (hs hr)) (resonance_bump_nonnegative h r)
  have hExp : Real.exp (c * resonanceScale ν) ≤ z * (a * Real.exp (-t * E)) ^ (2 : ℕ) := by
    calc
      _ = z * (D * Real.exp (-2 * t * Emax)) := by
        have hDexp : D * Real.exp (-2 * t * Emax) = Real.exp (Real.log D - 2 * t * Emax) := by
          rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hD]
          congr 2
          ring
        unfold z
        rw [hDexp, ← Real.exp_add]
        congr 1
        ring
      _ ≤ z * (D * Real.exp (-2 * t * E)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hEE (by linarith))) hD.le) hz
      _ = _ := by
        rw [mul_pow, haD, ← Real.exp_nat_mul]
        congr 3
        norm_num
        ring
  exact (ENNReal.ofReal_le_ofReal hExp).trans
    (resonance_weighted_norm_ge_pairing hh h2 hz (mul_nonneg ha (Real.exp_nonneg _)) hwm hwi hw0 hzl hrp)

end UV.AdvanceCollarResonanceHeat
