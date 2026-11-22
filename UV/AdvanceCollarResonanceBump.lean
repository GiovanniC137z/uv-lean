import UV.ResumeCollarLower
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Support

/-! The normalized incoming vector and smooth supported test at a normal
angular resonance. Energies use the actual quartic normal potential. -/

noncomputable section

open MeasureTheory Set Real
open scoped ContDiff Interval

namespace UV.AdvanceCollarResonanceBump

def resonancePotential (ν r : ℝ) : ℝ :=
  ν ^ (2 : ℕ) / r ^ (8 : ℕ) + 4 * ν / r ^ (5 : ℕ)

def resonanceEnergy (ν : ℝ) (u : ℝ → ℝ) : ℝ :=
  ∫ r in Ioc 0 1, deriv u r ^ (2 : ℕ) + resonancePotential ν r * u r ^ (2 : ℕ)

def resonanceIncoming (r : ℝ) : ℝ :=
  Real.sqrt 495 * r ^ (4 : ℕ) * (1 - r)

private theorem beta_two (n : ℕ) :
    (∫ r in (0 : ℝ)..1, r ^ n * (1 - r) ^ (2 : ℕ)) =
      1 / ((n : ℝ) + 1) - 2 / ((n : ℝ) + 2) + 1 / ((n : ℝ) + 3) := by
  have h (r : ℝ) : r ^ n * (1 - r) ^ (2 : ℕ) =
      r ^ n - 2 * r ^ (n + 1) + r ^ (n + 2) := by
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ r (n + 1), pow_succ r n]
    ring
  simp_rw [h]
  have h0 (k : ℕ) : IntervalIntegrable (fun r : ℝ => r ^ k) volume 0 1 :=
    (continuous_id.pow _).intervalIntegrable _ _
  rw [intervalIntegral.integral_add ((h0 n).sub ((h0 (n + 1)).const_mul 2)) (h0 (n + 2)),
    intervalIntegral.integral_sub (h0 n) ((h0 (n + 1)).const_mul 2),
    intervalIntegral.integral_const_mul]
  simp only [integral_pow, one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  ring

theorem resonance_incoming_normalized :
    (∫ r in Ioc (0 : ℝ) 1, resonanceIncoming r ^ (2 : ℕ)) = 1 := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have h (r : ℝ) : resonanceIncoming r ^ (2 : ℕ) =
      495 * (r ^ (8 : ℕ) * (1 - r) ^ (2 : ℕ)) := by
    unfold resonanceIncoming
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), ← pow_mul]
    ring
  simp_rw [h, intervalIntegral.integral_const_mul, beta_two]
  norm_num

theorem resonance_incoming_derivative (r : ℝ) :
    HasDerivAt resonanceIncoming (Real.sqrt 495 * r ^ (3 : ℕ) * (4 - 5 * r)) r := by
  have h₁ := ((hasDerivAt_id r).pow 4).const_mul (Real.sqrt 495)
  have h₂ := (hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r)
  convert h₁.mul h₂ using 1
  simp only [Pi.sub_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub]
  ring

theorem resonance_incoming_energy (ν : ℝ) :
    IntegrableOn (fun r => deriv resonanceIncoming r ^ (2 : ℕ) +
      resonancePotential ν r * resonanceIncoming r ^ (2 : ℕ)) (Ioc 0 1) ∧
    resonanceEnergy ν resonanceIncoming = 220 / 7 + 165 * ν ^ (2 : ℕ) + 33 * ν := by
  let D := fun r : ℝ => (495 : ℝ) * (16 * r ^ (6 : ℕ) - 40 * r ^ (7 : ℕ) + 25 * r ^ (8 : ℕ))
  let P := fun r : ℝ => (495 * ν ^ (2 : ℕ)) * (r ^ (0 : ℕ) * (1 - r) ^ (2 : ℕ))
  let Q := fun r : ℝ => (1980 * ν) * (r ^ (3 : ℕ) * (1 - r) ^ (2 : ℕ))
  have hD : Continuous D := by unfold D; fun_prop
  have hP : Continuous P := by unfold P; fun_prop
  have hQ : Continuous Q := by unfold Q; fun_prop
  have he (r : ℝ) (hr : r ∈ Ioc 0 1) : deriv resonanceIncoming r ^ (2 : ℕ) +
      resonancePotential ν r * resonanceIncoming r ^ (2 : ℕ) = D r + P r + Q r := by
    rw [(resonance_incoming_derivative r).deriv]
    unfold D P Q resonancePotential resonanceIncoming
    have hs : (Real.sqrt 495) ^ (2 : ℕ) = (495 : ℝ) := Real.sq_sqrt (by norm_num)
    rw [mul_pow, mul_pow, hs, mul_pow, mul_pow, hs]
    field_simp [hr.1.ne']
    ring
  have hi : IntegrableOn (fun r => D r + P r + Q r) (Ioc 0 1) :=
    ((hD.add hP).add hQ).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  refine ⟨hi.congr_fun (fun r hr => (he r hr).symm) measurableSet_Ioc, ?_⟩
  unfold resonanceEnergy
  rw [setIntegral_congr_fun measurableSet_Ioc he, ← intervalIntegral.integral_of_le zero_le_one]
  have hD0 (k : ℕ) : IntervalIntegrable (fun r : ℝ => r ^ k) volume 0 1 :=
    (continuous_id.pow _).intervalIntegrable _ _
  rw [intervalIntegral.integral_add ((hD.add hP).intervalIntegrable _ _) (hQ.intervalIntegrable _ _),
    intervalIntegral.integral_add (hD.intervalIntegrable _ _) (hP.intervalIntegrable _ _)]
  unfold D P Q
  simp only [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add (((hD0 6).const_mul 16).sub ((hD0 7).const_mul 40))
      ((hD0 8).const_mul 25),
    intervalIntegral.integral_sub ((hD0 6).const_mul 16) ((hD0 7).const_mul 40)]
  simp only [intervalIntegral.integral_const_mul, integral_pow, beta_two]
  norm_num
  ring

theorem resonance_incoming_uniform_energy {ν : ℝ} (hν : 0 ≤ ν) (hν1 : ν ≤ 1) :
    resonanceEnergy ν resonanceIncoming ≤ 1606 / 7 := by
  rw [(resonance_incoming_energy ν).2]
  have hν2 := pow_le_pow_left₀ hν hν1 2
  nlinarith

private def rawBump : ContDiffBump (3 / 2 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

private def bumpMass : ℝ :=
  ∫ s : ℝ, rawBump s ^ (2 : ℕ)

private theorem bump_mass_pos : 0 < bumpMass := by
  unfold bumpMass
  have hc := rawBump.continuous.pow 2
  have hs : HasCompactSupport (fun s : ℝ => rawBump s ^ (2 : ℕ)) := by
    simpa only [pow_two, Pi.mul_apply] using
      (rawBump.hasCompactSupport.mul_right : HasCompactSupport ((⇑rawBump : ℝ → ℝ) * ⇑rawBump))
  refine integral_pos_of_integrable_nonneg_nonzero (x := (3 / 2 : ℝ)) hc
    (hc.integrable_of_hasCompactSupport hs) (fun s => sq_nonneg _) ?_
  rw [rawBump.one_of_mem_closedBall (Metric.mem_closedBall_self rawBump.rIn_pos.le), one_pow]
  exact one_ne_zero

def resonanceReference (s : ℝ) : ℝ :=
  (Real.sqrt bumpMass)⁻¹ * rawBump s

theorem resonance_reference_smooth :
    ContDiff ℝ ∞ resonanceReference :=
  contDiff_const.mul rawBump.contDiff

private theorem resonance_reference_norm :
    (∫ s : ℝ, resonanceReference s ^ (2 : ℕ)) = 1 := by
  simp_rw [resonanceReference, mul_pow, integral_const_mul]
  change ((Real.sqrt bumpMass)⁻¹) ^ (2 : ℕ) * bumpMass = 1
  rw [inv_pow, Real.sq_sqrt bump_mass_pos.le, inv_mul_cancel₀ bump_mass_pos.ne']

private theorem resonance_reference_zero {s : ℝ} (hs : s ∉ Ioo (5 / 4 : ℝ) (7 / 4)) :
    resonanceReference s = 0 := by
  have hz : s ∉ Function.support ⇑rawBump := by
    rw [rawBump.support_eq]
    rw [Real.ball_eq_Ioo]
    change s ∉ Ioo (3 / 2 - 1 / 4 : ℝ) (3 / 2 + 1 / 4)
    norm_num at hs ⊢
    exact hs
  simp [resonanceReference, Function.notMem_support.mp hz]

def resonanceBump (h r : ℝ) : ℝ :=
  (Real.sqrt h)⁻¹ * resonanceReference (r / h)

theorem resonance_bump_smooth (h : ℝ) : ContDiff ℝ ∞ (resonanceBump h) :=
  contDiff_const.mul (resonance_reference_smooth.comp (contDiff_id.div_const h))

theorem resonance_bump_nonnegative (h r : ℝ) : 0 ≤ resonanceBump h r := by
  unfold resonanceBump resonanceReference
  exact mul_nonneg (by positivity) (mul_nonneg (by positivity) rawBump.nonneg)

private theorem resonance_bump_zero {h r : ℝ} (hh : 0 < h)
    (hr : r ∉ Ioo (5 * h / 4) (7 * h / 4)) : resonanceBump h r = 0 := by
  have hs : r / h ∉ Ioo (5 / 4 : ℝ) (7 / 4) := by
    intro hs
    exact hr ⟨by linarith [(lt_div_iff₀ hh).mp hs.1], by linarith [(div_lt_iff₀ hh).mp hs.2]⟩
  simp [resonanceBump, resonance_reference_zero hs]

theorem resonance_bump_zero_off_support {h r : ℝ} (hh : 0 < h)
    (hr : r ∉ Ioo h (2 * h)) : resonanceBump h r = 0 :=
  resonance_bump_zero hh fun hmem => hr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩

theorem resonance_bump_norm {h : ℝ} (hh : 0 < h) :
    (∫ r in Icc h (2 * h), resonanceBump h r ^ (2 : ℕ)) = 1 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun r hr => by
    simp [resonance_bump_zero_off_support hh (fun hs => hr (Ioo_subset_Icc_self hs))])]
  simp_rw [resonanceBump, mul_pow, integral_const_mul]
  have h := Measure.integral_comp_div (fun s : ℝ => resonanceReference s ^ (2 : ℕ)) h
  rw [h, abs_of_pos hh, smul_eq_mul, resonance_reference_norm, inv_pow, Real.sq_sqrt hh.le,
    mul_one, inv_mul_cancel₀ hh.ne']

theorem resonance_bump_incoming_dominance :
    ∃ c : ℝ, 0 < c ∧ ∀ h, 0 < h → 2 * h ≤ 1 → ∀ r ∈ Ioc 0 1,
      c * (h ^ (4 : ℕ) * Real.sqrt h) * resonanceBump h r ≤ resonanceIncoming r := by
  let c := Real.sqrt 495 * Real.sqrt bumpMass / 8
  have hc : 0 < c := div_pos (mul_pos (Real.sqrt_pos.2 (by norm_num))
    (Real.sqrt_pos.2 bump_mass_pos)) (by norm_num)
  refine ⟨c, hc, fun h hh h2 r hr => ?_⟩
  by_cases hs : r ∈ Ioo (5 * h / 4) (7 * h / 4)
  · have hrh : h ≤ r := by linarith [hs.1]
    have hr8 : r ≤ 7 / 8 := by linarith [hs.2]
    have hb : resonanceBump h r ≤ (Real.sqrt h)⁻¹ * (Real.sqrt bumpMass)⁻¹ := by
      unfold resonanceBump resonanceReference
      have hi : (Real.sqrt bumpMass)⁻¹ * rawBump (r / h) ≤ (Real.sqrt bumpMass)⁻¹ := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left rawBump.le_one (by positivity : 0 ≤ (Real.sqrt bumpMass)⁻¹)
      exact mul_le_mul_of_nonneg_left hi (by positivity)
    calc
      _ ≤ c * (h ^ (4 : ℕ) * Real.sqrt h) * ((Real.sqrt h)⁻¹ * (Real.sqrt bumpMass)⁻¹) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = Real.sqrt 495 * h ^ (4 : ℕ) * (1 / 8) := by
        unfold c
        field_simp [(Real.sqrt_pos.2 hh).ne', (Real.sqrt_pos.2 bump_mass_pos).ne']
      _ ≤ resonanceIncoming r := by
        unfold resonanceIncoming
        refine mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh.le hrh 4) (by positivity))
          (by linarith) (by norm_num) (by positivity)
  · rw [resonance_bump_zero hh hs, mul_zero]
    unfold resonanceIncoming
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hr.2)

private theorem resonance_bump_compact {h : ℝ} (hh : 0 < h) :
    HasCompactSupport (resonanceBump h) :=
  HasCompactSupport.intro isCompact_Icc fun _ hr =>
    resonance_bump_zero_off_support hh (fun hs => hr (Ioo_subset_Icc_self hs))

private theorem resonance_bump_derivative (h r : ℝ) :
    deriv (resonanceBump h) r =
      ((Real.sqrt h)⁻¹ / h) * deriv resonanceReference (r / h) := by
  have href := (resonance_reference_smooth.differentiable (by simp) (r / h)).hasDerivAt
  have hdiv := (hasDerivAt_id r).div_const h
  have hb := (href.comp r hdiv).const_mul ((Real.sqrt h)⁻¹)
  convert hb.deriv using 1
  simp only [div_eq_mul_inv, mul_assoc, mul_comm, one_mul]

private theorem resonance_bump_kinetic_integral {h : ℝ} (hh : 0 < h) :
    (∫ r : ℝ, deriv (resonanceBump h) r ^ (2 : ℕ)) =
      (h ^ (2 : ℕ))⁻¹ * ∫ s : ℝ, deriv resonanceReference s ^ (2 : ℕ) := by
  simp_rw [resonance_bump_derivative, mul_pow, integral_const_mul]
  have h := Measure.integral_comp_div (fun s : ℝ => deriv resonanceReference s ^ (2 : ℕ)) h
  rw [h, abs_of_pos hh, smul_eq_mul]
  have hs := Real.sq_sqrt hh.le
  rw [div_pow, inv_pow, hs]
  field_simp [hh.ne']

/-- The source's smooth unit test has the three form-energy costs of
the resonant radial expression, with one fixed coefficient. -/
theorem resonance_bump_energy_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ν h, 0 ≤ ν → 0 < h → 2 * h ≤ 1 →
      IntegrableOn (fun r => deriv (resonanceBump h) r ^ (2 : ℕ) +
        resonancePotential ν r * resonanceBump h r ^ (2 : ℕ)) (Ioc 0 1) ∧
      resonanceEnergy ν (resonanceBump h) ≤
        B * ((h ^ (2 : ℕ))⁻¹ + ν ^ (2 : ℕ) / h ^ (8 : ℕ) + ν / h ^ (5 : ℕ)) := by
  let D := ∫ s : ℝ, deriv resonanceReference s ^ (2 : ℕ)
  let B := max 4 D
  have hB : 0 ≤ B := (by norm_num : (0 : ℝ) ≤ 4).trans (le_max_left _ _)
  refine ⟨B, hB, fun ν h hν hh h2 => ?_⟩
  let P := ν ^ (2 : ℕ) / h ^ (8 : ℕ) + 4 * ν / h ^ (5 : ℕ)
  have hP : 0 ≤ P := by positivity
  have hz (r : ℝ) : 0 ≤ resonancePotential ν r * resonanceBump h r ^ (2 : ℕ) := by
    by_cases hr : r ∈ Ioo h (2 * h)
    · have hr0 := hh.trans hr.1
      unfold resonancePotential
      positivity
    · simp [resonance_bump_zero_off_support hh hr]
  have hp (r : ℝ) : resonancePotential ν r * resonanceBump h r ^ (2 : ℕ) ≤
      P * resonanceBump h r ^ (2 : ℕ) := by
    by_cases hr : r ∈ Ioo h (2 * h)
    · have hr0 := hh.trans hr.1
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      unfold resonancePotential P
      have hd8 : 0 < h ^ (8 : ℕ) := pow_pos hh _
      have hd5 : 0 < h ^ (5 : ℕ) := pow_pos hh _
      exact add_le_add
        (div_le_div_of_nonneg_left (sq_nonneg _) hd8 (pow_le_pow_left₀ hh.le hr.1.le _))
        (div_le_div_of_nonneg_left (by positivity) hd5 (pow_le_pow_left₀ hh.le hr.1.le _))
    · simp [resonance_bump_zero_off_support hh hr]
  have hcb := resonance_bump_compact hh
  have hcd := resonance_bump_smooth h
  have hdcs : HasCompactSupport (fun r => deriv (resonanceBump h) r ^ (2 : ℕ)) := by
    simpa only [pow_two, Pi.mul_apply] using
      (hcb.deriv.mul_right : HasCompactSupport (deriv (resonanceBump h) * deriv (resonanceBump h)))
  have hbcs : HasCompactSupport (fun r => resonanceBump h r ^ (2 : ℕ)) := by
    simpa only [pow_two, Pi.mul_apply] using
      (hcb.mul_right : HasCompactSupport (resonanceBump h * resonanceBump h))
  have hdi := ((hcd.continuous_deriv (by simp)).pow 2).integrable_of_hasCompactSupport (μ := volume) hdcs
  have hbi := (hcd.continuous.pow 2).integrable_of_hasCompactSupport (μ := volume) hbcs
  have hq : Integrable (fun r => resonancePotential ν r * resonanceBump h r ^ (2 : ℕ)) := by
    have hpmeas : Measurable (resonancePotential ν) := by unfold resonancePotential; fun_prop
    have hbmeas := (hcd.continuous.pow 2).measurable
    apply (hbi.const_mul P).mono' (hpmeas.mul hbmeas).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun r => by simpa [Real.norm_of_nonneg (hz r)] using hp r
  refine ⟨(hdi.add hq).integrableOn, ?_⟩
  have hnorm : (∫ r in Ioc (0 : ℝ) 1, resonanceBump h r ^ (2 : ℕ)) = 1 := by
    calc
      _ = ∫ r : ℝ, resonanceBump h r ^ (2 : ℕ) :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun r hr => by
          have hre : r ∉ Ioo h (2 * h) := fun hs => hr ⟨hh.trans hs.1, hs.2.le.trans h2⟩
          simp [resonance_bump_zero_off_support hh hre]
      _ = _ := by
        rw [← resonance_bump_norm hh]
        exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun r hr => by
          simp [resonance_bump_zero_off_support hh (fun hs => hr (Ioo_subset_Icc_self hs))])).symm
  have hdi_bound : (∫ r in Ioc (0 : ℝ) 1, deriv (resonanceBump h) r ^ (2 : ℕ)) ≤
      (h ^ (2 : ℕ))⁻¹ * D := by
    rw [← resonance_bump_kinetic_integral hh]
    exact setIntegral_le_integral hdi (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  have hpi_bound : (∫ r in Ioc (0 : ℝ) 1,
      resonancePotential ν r * resonanceBump h r ^ (2 : ℕ)) ≤ P := by
    calc
      _ ≤ ∫ r in Ioc (0 : ℝ) 1, P * resonanceBump h r ^ (2 : ℕ) :=
        setIntegral_mono_on hq.integrableOn (hbi.const_mul P).integrableOn measurableSet_Ioc
          (fun r _ => hp r)
      _ = _ := by rw [integral_const_mul, hnorm, mul_one]
  unfold resonanceEnergy
  rw [integral_add hdi.integrableOn hq.integrableOn]
  calc
    _ ≤ (h ^ (2 : ℕ))⁻¹ * D + P := add_le_add hdi_bound hpi_bound
    _ ≤ (h ^ (2 : ℕ))⁻¹ * B + B * (ν ^ (2 : ℕ) / h ^ (8 : ℕ)) +
        B * (ν / h ^ (5 : ℕ)) := by
      have hd := mul_le_mul_of_nonneg_left (show D ≤ B from le_max_right 4 D)
        (by positivity : 0 ≤ (h ^ (2 : ℕ))⁻¹)
      have h8 := mul_le_mul_of_nonneg_right (by linarith [le_max_left 4 D] : 1 ≤ B)
        (by positivity : 0 ≤ ν ^ (2 : ℕ) / h ^ (8 : ℕ))
      have h5 : 4 * ν / h ^ (5 : ℕ) ≤ B * (ν / h ^ (5 : ℕ)) := by
        rw [show 4 * ν / h ^ (5 : ℕ) = 4 * (ν / h ^ (5 : ℕ)) by ring]
        exact mul_le_mul_of_nonneg_right (show 4 ≤ B from le_max_left 4 D) (by positivity)
      unfold P
      linarith
    _ = _ := by ring

/-- At a fixed nonzero resonance distance the selected chirality
dominates the quartic spinless barrier up to a finite scalar shift. -/
theorem resonant_potential_compares_quartic {ν : ℝ} (hν : 0 < ν) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioc (0 : ℝ) 1,
      2 / r ^ (2 : ℕ) + ν ^ (2 : ℕ) / r ^ (8 : ℕ) - C ≤ resonancePotential ν r := by
  let a := min 1 ν
  have ha := lt_min zero_lt_one hν
  refine ⟨2 / a ^ (2 : ℕ), by positivity, fun r hr => ?_⟩
  unfold resonancePotential
  by_cases hra : r ≤ a
  · have hpow : r ^ (3 : ℕ) ≤ r := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_self_of_le_one hr.1.le hr.2 (by norm_num)
    have hrc : r ^ (3 : ℕ) ≤ ν := hpow.trans (hra.trans (min_le_right _ _))
    have hpot : 2 / r ^ (2 : ℕ) ≤ 4 * ν / r ^ (5 : ℕ) := by
      apply (div_le_div_iff₀ (pow_pos hr.1 _) (pow_pos hr.1 _)).mpr
      calc
        _ = (2 * r ^ (3 : ℕ)) * r ^ (2 : ℕ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    linarith [show 0 ≤ 2 / a ^ (2 : ℕ) by positivity]
  · have h2 : 2 / r ^ (2 : ℕ) ≤ 2 / a ^ (2 : ℕ) :=
      div_le_div_of_nonneg_left (by norm_num) (pow_pos ha _) (pow_le_pow_left₀ ha.le (le_of_not_ge hra) _)
    linarith [div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hν.le) (pow_nonneg hr.1.le 5)]

end UV.AdvanceCollarResonanceBump
