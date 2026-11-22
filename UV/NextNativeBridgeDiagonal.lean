import UV.NextNativeBridgeResponse
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-! The same-profile two-insertion response has two-sided logarithmic
growth in the actual four-dimensional carrier radial measure. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace UV.NextNativeBridge

variable {E : Type} [NormedAddCommGroup E]

def sameProfilePair (B : NormalBridge E) (i : Bool) (q k : UV.ScalarMomentum) : ℝ :=
  bridgeCoefficient B i i k * bridgeCoefficient B i i (k + q)

private theorem diagonalCoefficient_band (f : NormalProfile) :
    ∃ S : ℝ, ∀ ω ≥ S, 1 / 2 ≤ ω ^ 2 * normalCovariance f f ω ∧
      ω ^ 2 * normalCovariance f f ω ≤ 2 := by
  have hev := (normalCovariance_diagonal_tendsto f).eventually
    (Ioo_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1) (by norm_num : (1 : ℝ) < 2))
  obtain ⟨S, hS⟩ := eventually_atTop.mp hev
  exact ⟨S, fun ω hω => ⟨(hS ω hω).1.le, (hS ω hω).2.le⟩⟩

/-- Bounds of the exact inverse-fourth-power order on every sufficiently
large shell, for an arbitrary fixed shifted momentum. -/
theorem same_profile_pair_tail_bounds (B : NormalBridge E) (i : Bool) (q : UV.ScalarMomentum) :
    ∃ R > 0, ∀ k : UV.ScalarMomentum, R < ‖k‖ →
      1 / (64 * ‖k‖ ^ 4) ≤ sameProfilePair B i q k ∧
      sameProfilePair B i q k ≤ 64 / ‖k‖ ^ 4 := by
  obtain ⟨S, hS⟩ := diagonalCoefficient_band (B.profiles i)
  let R := 2 * (‖q‖ + B.mass + max S 1)
  have hR : 0 < R := by
    dsimp [R]
    linarith [B.mass_pos, norm_nonneg q, le_max_right S (1 : ℝ)]
  refine ⟨R, hR, fun k hk => ?_⟩
  have hk₀ := hR.trans hk
  have hscaled (q' : UV.ScalarMomentum) (hq' : ‖q'‖ ≤ ‖q‖) :
      1 / (8 * ‖k‖ ^ 2) ≤ bridgeCoefficient B i i (k + q') ∧
      bridgeCoefficient B i i (k + q') ≤ 8 / ‖k‖ ^ 2 := by
    have htri := norm_sub_le (k + q') q'
    rw [add_sub_cancel_right] at htri
    let ω := euclideanOmega B (k + q')
    have hω₀ : 0 < ω := B.mass_pos.trans_le (mass_le_euclideanOmega _ _)
    have hωlo : ‖k‖ / 2 ≤ ω := by
      have hb := norm_le_euclideanOmega B (k + q')
      dsimp [R] at hk
      dsimp [ω]
      linarith [le_max_right S (1 : ℝ), B.mass_pos]
    have hωhi : ω ≤ 2 * ‖k‖ := by
      have hb := euclideanOmega_le B (k + q')
      have hnorm := norm_add_le k q'
      dsimp [R] at hk
      dsimp [ω]
      linarith [le_max_right S (1 : ℝ), B.mass_pos, norm_nonneg q]
    have hωS : S ≤ ω := by
      dsimp [R] at hk
      linarith [le_max_left S (1 : ℝ), norm_nonneg q, B.mass_pos]
    obtain ⟨hl, hh⟩ := hS ω hωS
    have hsqlo := (sq_le_sq₀ (by positivity : 0 ≤ ‖k‖ / 2) hω₀.le).2 hωlo
    have hsqhi := (sq_le_sq₀ hω₀.le (by positivity : 0 ≤ 2 * ‖k‖)).2 hωhi
    have hw : 0 < ω ^ 2 := by positivity
    change 1 / (8 * ‖k‖ ^ 2) ≤ normalCovariance _ _ ω ∧
      normalCovariance _ _ ω ≤ 8 / ‖k‖ ^ 2
    constructor
    · calc
        _ = (1 / 2 : ℝ) / (4 * ‖k‖ ^ 2) := by ring
        _ ≤ (1 / 2 : ℝ) / ω ^ 2 :=
          div_le_div_of_nonneg_left (by norm_num) hw (by nlinarith)
        _ ≤ _ := (div_le_iff₀ hw).mpr (by linarith)
    · calc
        _ ≤ 2 / ω ^ 2 := (le_div_iff₀ hw).mpr (by linarith)
        _ ≤ 2 / (‖k‖ / 2) ^ 2 :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hsqlo
        _ = _ := by ring
  obtain ⟨h0a, h0b⟩ := hscaled 0 (by simp)
  rw [add_zero] at h0a h0b
  obtain ⟨hqa, hqb⟩ := hscaled q le_rfl
  have hp : 0 ≤ 1 / (8 * ‖k‖ ^ 2) := by positivity
  unfold sameProfilePair
  constructor
  · calc
      _ = (1 / (8 * ‖k‖ ^ 2)) * (1 / (8 * ‖k‖ ^ 2)) := by ring
      _ ≤ _ := mul_le_mul h0a hqa hp (hp.trans h0a)
  · calc
      _ ≤ (8 / ‖k‖ ^ 2) * (8 / ‖k‖ ^ 2) :=
        mul_le_mul h0b hqb (hp.trans hqa) (by positivity)
      _ = _ := by ring

def carrierShell (R T : ℝ) : Set UV.ScalarMomentum := {k | ‖k‖ ∈ Ioc R T}

private theorem carrierShell_measurable (R T : ℝ) : MeasurableSet (carrierShell R T) :=
  measurable_norm measurableSet_Ioc

private theorem carrierShell_lt_top (R T : ℝ) :
    (volume : Measure UV.ScalarMomentum) (carrierShell R T) < ⊤ := by
  apply lt_of_le_of_lt (measure_mono (t := Metric.closedBall 0 T) ?_)
    measure_closedBall_lt_top
  intro k hk
  simpa only [Metric.mem_closedBall, dist_zero_right] using (mem_Ioc.mp hk).2

def carrierRadialFactor : ℝ :=
  4 * (volume : Measure UV.ScalarMomentum).real (Metric.ball 0 1)

theorem carrier_radial_factor_pos : 0 < carrierRadialFactor := by
  have hp := Metric.measure_ball_pos (volume : Measure UV.ScalarMomentum) 0 zero_lt_one
  unfold carrierRadialFactor
  exact mul_pos (by norm_num) (ENNReal.toReal_pos (ne_of_gt hp) measure_ball_lt_top.ne)

private theorem inverse_fourth_shell_integrable {R T : ℝ} (hR : 0 < R) :
    IntegrableOn (fun k : UV.ScalarMomentum => (‖k‖ ^ 4)⁻¹) (carrierShell R T) := by
  apply (integrableOn_const (C := (R ^ 4)⁻¹) (carrierShell_lt_top R T).ne).mono'
  · exact (measurable_norm.pow_const _).inv.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (carrierShell_measurable R T)] with k hk
    rw [Real.norm_of_nonneg (by positivity)]
    apply inv_anti₀ (by positivity : 0 < R ^ 4)
    exact pow_le_pow_left₀ hR.le (mem_Ioc.mp hk).1.le 4

private theorem inverse_fourth_shell_integral {R T : ℝ} (hR : 0 < R) (hT : R ≤ T) :
    (∫ k in carrierShell R T, (‖k‖ ^ 4)⁻¹) =
      carrierRadialFactor * (Real.log T - Real.log R) := by
  rw [← integral_indicator (carrierShell_measurable R T)]
  change (∫ k : UV.ScalarMomentum, (Ioc R T).indicator (fun r : ℝ => (r ^ 4)⁻¹) ‖k‖) = _
  rw [integral_fun_norm_addHaar]
  norm_num only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat]
  have hrad :
      (∫ r : ℝ in Ioi 0, r ^ 3 * (Ioc R T).indicator (fun r => (r ^ 4)⁻¹) r) =
        Real.log T - Real.log R := by
    calc
      _ = ∫ r in Ioc R T, r⁻¹ := by
        rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioc]
        apply integral_congr_ae
        refine Eventually.of_forall fun r => ?_
        by_cases hr : r ∈ Ioc R T
        · have hr₀ := hR.trans (mem_Ioc.mp hr).1
          rw [indicator_of_mem (mem_Ioi.mpr hr₀), indicator_of_mem hr, indicator_of_mem hr]
          field_simp [hr₀.ne']
        · by_cases hr₀ : r ∈ Ioi (0 : ℝ)
          · rw [indicator_of_mem hr₀, indicator_of_notMem hr, indicator_of_notMem hr, mul_zero]
          · rw [indicator_of_notMem hr₀, indicator_of_notMem hr]
      _ = _ := by
        rw [← intervalIntegral.integral_of_le hT, integral_inv_of_pos hR (hR.trans_le hT),
          Real.log_div (hR.trans_le hT).ne' hR.ne']
  rw [hrad, carrierRadialFactor, mul_assoc]

/-- The absolute same-profile shell integral is bounded above and below
by strictly positive multiples of the logarithmic shell ratio. -/
theorem same_profile_pair_logarithmic (B : NormalBridge E) (i : Bool) (q : UV.ScalarMomentum) :
    ∃ R > 0, ∀ T ≥ R, IntegrableOn (sameProfilePair B i q) (carrierShell R T) ∧
      carrierRadialFactor / 64 * (Real.log T - Real.log R) ≤
        ∫ k in carrierShell R T, ‖sameProfilePair B i q k‖ ∧
      (∫ k in carrierShell R T, ‖sameProfilePair B i q k‖) ≤
        64 * carrierRadialFactor * (Real.log T - Real.log R) := by
  obtain ⟨R, hR, hpair⟩ := same_profile_pair_tail_bounds B i q
  refine ⟨R, hR, fun T hT => ?_⟩
  have hi := inverse_fourth_shell_integrable (T := T) hR
  have hmeas : StronglyMeasurable (sameProfilePair B i q) :=
    (bridgeCoefficient_stronglyMeasurable B i i).mul
      ((bridgeCoefficient_stronglyMeasurable B i i).comp_measurable (by fun_prop))
  have hnorm (k : UV.ScalarMomentum) (hk : k ∈ carrierShell R T) :
      ‖sameProfilePair B i q k‖ = sameProfilePair B i q k := by
    exact Real.norm_of_nonneg ((by positivity : 0 ≤ 1 / (64 * ‖k‖ ^ 4)).trans
      (hpair k (mem_Ioc.mp hk).1).1)
  have hI : IntegrableOn (sameProfilePair B i q) (carrierShell R T) := by
    apply (hi.const_mul 64).mono' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (carrierShell_measurable R T)] with k hk
    rw [hnorm k hk, ← div_eq_mul_inv]
    exact (hpair k (mem_Ioc.mp hk).1).2
  refine ⟨hI, ?_, ?_⟩
  · have h := setIntegral_mono_on (hi.const_mul (1 / 64)) hI.norm
      (carrierShell_measurable R T) (fun k hk => by
        rw [hnorm k hk]
        simpa only [div_eq_mul_inv, mul_inv, one_mul] using (hpair k (mem_Ioc.mp hk).1).1)
    rw [integral_const_mul, inverse_fourth_shell_integral hR hT] at h
    convert h using 1
    ring
  · have h := setIntegral_mono_on hI.norm (hi.const_mul 64)
      (carrierShell_measurable R T) (fun k hk => by
        rw [hnorm k hk, ← div_eq_mul_inv]
        exact (hpair k (mem_Ioc.mp hk).1).2)
    rw [integral_const_mul, inverse_fourth_shell_integral hR hT] at h
    simpa only [mul_assoc] using h

/-- The positive radial factor forces absolute divergence of the actual
same-profile two-insertion product on the fixed four-plane. -/
theorem same_profile_pair_not_integrable (B : NormalBridge E) (i : Bool) (q : UV.ScalarMomentum) :
    ¬ Integrable (sameProfilePair B i q) := by
  intro h
  obtain ⟨R, hR, hh⟩ := same_profile_pair_logarithmic B i q
  have hpos : 0 < carrierRadialFactor / 64 := by linarith [carrier_radial_factor_pos]
  have hlog : Tendsto (fun T : ℝ => Real.log T - Real.log R) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [tendsto_atTop.mp Real.tendsto_log_atTop (b + Real.log R)] with T hT
    linarith
  have ht : Tendsto (fun T : ℝ =>
      carrierRadialFactor / 64 * (Real.log T - Real.log R)) atTop atTop :=
    hlog.const_mul_atTop hpos
  let I := ∫ k, ‖sameProfilePair B i q k‖
  obtain ⟨T, hT, hlarge⟩ := ((eventually_ge_atTop R).and
    (ht.eventually_gt_atTop I)).exists
  have hlow := (hh T hT).2.1
  have hu : (∫ k in carrierShell R T, ‖sameProfilePair B i q k‖) ≤ I := by
    apply setIntegral_le_integral h.norm
    exact Eventually.of_forall fun k => norm_nonneg _
  exact (hlarge.trans_le (hlow.trans hu)).false

end UV.NextNativeBridge
