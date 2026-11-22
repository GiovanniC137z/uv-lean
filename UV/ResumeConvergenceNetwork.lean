import UV.MomentRecurrence
import UV.RevisionBoundaryHeat
import Mathlib.MeasureTheory.Integral.Pi

/-! Exact duration factors in the expanded manuscript's marked normal
network, on one fixed Euclidean sector plane and in the stated reference
units. These estimates retain the five-dimensional edge normalization.
The separate network Gaussian/Fourier routing identity is not assumed. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace UV

def networkHeatFive (m z s : ℝ) : ℝ :=
  (1 / (32 * Real.pi ^ 2 * Real.sqrt Real.pi)) *
    s ^ (-(5 : ℝ) / 2) * Real.exp (-(m ^ 2 * s) - z ^ 2 / (4 * s))

def networkEdgeGreen (m z : ℝ) : ℝ :=
  ((1 + m * z) * Real.exp (-(m * z))) / (8 * Real.pi ^ 2 * z ^ 3)

theorem networkHeatFive_standard {s : ℝ} (hs : 0 < s) (m z : ℝ) :
    networkHeatFive m z s = (4 * Real.pi * s) ^ (-(5 : ℝ) / 2) *
      Real.exp (-(m ^ 2 * s) - z ^ 2 / (4 * s)) := by
  have hpow : (4 * Real.pi) ^ ((5 : ℝ) / 2) = 32 * Real.pi ^ 2 * Real.sqrt Real.pi := by
    rw [show (5 : ℝ) / 2 = 2 + 1 / 2 by ring, Real.rpow_add (by positivity),
      Real.rpow_two, ← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
    ring
  rw [Real.mul_rpow (by positivity : 0 ≤ 4 * Real.pi) hs.le,
    show -(5 : ℝ) / 2 = -((5 : ℝ) / 2) by ring,
    Real.rpow_neg (by positivity : 0 ≤ 4 * Real.pi), hpow]
  simp only [networkHeatFive, one_div, neg_div]

theorem networkHeatFive_nonneg {s : ℝ} (hs : 0 ≤ s) (m z : ℝ) :
    0 ≤ networkHeatFive m z s := by unfold networkHeatFive; positivity

theorem networkHeatFive_scale {z τ : ℝ} (hz : 0 < z) (hτ : 0 < τ) (m : ℝ) :
    z ^ 2 * networkHeatFive m z (z ^ 2 * τ) =
      (1 / (16 * Real.pi ^ 2 * z ^ 3 * Real.exp (m * z))) *
        (τ ^ (-1 : ℝ) * oqedDensity (m * z) τ) := by
  have hz0 := hz.ne'
  have hπ := Real.pi_ne_zero
  have hsqrt : Real.sqrt Real.pi ≠ 0 := by positivity
  have hp : (z ^ 2 * τ) ^ (-(5 : ℝ) / 2) = (z ^ 5)⁻¹ * τ ^ (-(5 : ℝ) / 2) := by
    rw [Real.mul_rpow (sq_nonneg z) hτ.le, ← Real.rpow_natCast z 2, ← Real.rpow_mul hz.le]
    norm_num [Real.rpow_neg hz.le]
  have hτpow : τ ^ (-1 : ℝ) * τ ^ (-(3 : ℝ) / 2) = τ ^ (-(5 : ℝ) / 2) := by
    rw [← Real.rpow_add hτ]
    congr 1
    ring
  have he : -(m ^ 2 * (z ^ 2 * τ)) - z ^ 2 / (4 * (z ^ 2 * τ)) =
      -((m * z) ^ 2 * τ) - 1 / (4 * τ) := by
    field_simp
  unfold networkHeatFive oqedDensity oqedDensityCore
  rw [hp, he]
  have hexp := ne_of_gt (Real.exp_pos (m * z))
  field_simp
  simp only [neg_div] at hτpow
  nlinarith [hτpow]

theorem networkHeatFive_integrable {m z : ℝ} (hz : 0 < z) :
    IntegrableOn (networkHeatFive m z) (Ioi 0) := by
  have hi := (oqedNatMomentReal_integrable (m * z) 1).const_mul
    (1 / (16 * Real.pi ^ 2 * z ^ 3 * Real.exp (m * z)))
  have hi' : IntegrableOn (fun τ : ℝ => z ^ 2 * networkHeatFive m z (z ^ 2 * τ)) (Ioi 0) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    simpa only [Nat.cast_one] using (networkHeatFive_scale hz hτ m).symm
  have hi'' := (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hz.ne')) _).mp hi'
  have h := (integrableOn_Ioi_comp_mul_left_iff (networkHeatFive m z) 0 (sq_pos_of_pos hz)).mp hi''
  simpa only [mul_zero] using h

theorem networkHeatFive_integral {m z : ℝ} (hm : 0 < m) (hz : 0 < z) :
    (∫ s in Ioi (0 : ℝ), networkHeatFive m z s) = networkEdgeGreen m z := by
  have hscale := integral_comp_mul_left_Ioi (networkHeatFive m z) 0 (sq_pos_of_pos hz)
  rw [mul_zero, smul_eq_mul] at hscale
  calc
    _ = ∫ τ in Ioi (0 : ℝ), z ^ 2 * networkHeatFive m z (z ^ 2 * τ) := by
      rw [integral_const_mul, hscale]
      field_simp
    _ = (1 / (16 * Real.pi ^ 2 * z ^ 3 * Real.exp (m * z))) * oqedNatMomentReal (m * z) 1 := by
      unfold oqedNatMomentReal
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro τ hτ
      simpa only [Nat.cast_one] using networkHeatFive_scale hz hτ m
    _ = _ := by
      rw [oqedNatMomentReal_one (mul_pos hm hz)]
      unfold networkEdgeGreen
      rw [Real.exp_neg]
      ring

def networkEdgeCost (m z : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (networkHeatFive m z s)

theorem networkEdgeCost_positive {m z : ℝ} (hm : 0 < m) (hz : 0 < z) :
    networkEdgeCost m z = ENNReal.ofReal (networkEdgeGreen m z) := by
  unfold networkEdgeCost
  rw [← ofReal_integral_eq_lintegral_ofReal (networkHeatFive_integrable hz)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact networkHeatFive_nonneg hs.le m z), networkHeatFive_integral hm hz]

theorem networkHeatFive_zero_not_integrable (m : ℝ) :
    ¬ IntegrableOn (networkHeatFive m 0) (Ioi 0) := by
  intro hi
  let A : ℝ := 1 / (32 * Real.pi ^ 2 * Real.sqrt Real.pi)
  let C : ℝ := A * Real.exp (-(m ^ 2))
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 0 < C := mul_pos hA (Real.exp_pos _)
  have hlo {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
      C * RevisionBoundary.returnIntegrand 0 s ≤ networkHeatFive m 0 s := by
    have hp : (s ^ 2)⁻¹ ≤ s ^ (-(5 : ℝ) / 2) := by
      have h := Real.rpow_le_rpow_of_exponent_ge hs.1 hs.2 (by norm_num : -(5 : ℝ) / 2 ≤ -2)
      simpa only [Real.rpow_neg hs.1.le, Real.rpow_two] using h
    have he : Real.exp (-(m ^ 2)) ≤ Real.exp (-(m ^ 2 * s)) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hs.2 (sq_nonneg m))
    calc
      _ = A * ((s ^ 2)⁻¹ * Real.exp (-(m ^ 2))) := by
        simp only [C, RevisionBoundary.returnIntegrand, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
          neg_zero, zero_div, Real.exp_zero, one_div]
        ring
      _ ≤ A * (s ^ (-(5 : ℝ) / 2) * Real.exp (-(m ^ 2 * s))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hp he (Real.exp_pos _).le
          (Real.rpow_nonneg hs.1.le _)) hA.le
      _ = _ := by simp only [networkHeatFive, A, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, sub_zero]; ring
  have hrestrict := hi.mono_set (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from fun _ hs => hs.1)
  have hj : IntegrableOn (RevisionBoundary.returnIntegrand 0) (Ioc (0 : ℝ) 1) := by
    apply (hrestrict.const_mul C⁻¹).mono' (by
      apply Measurable.aestronglyMeasurable
      unfold RevisionBoundary.returnIntegrand
      fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.norm_of_nonneg (by unfold RevisionBoundary.returnIntegrand; positivity)]
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ hC).mpr
    simpa only [mul_comm] using hlo hs
  exact (RevisionBoundary.return_integral_zero_diverges (by norm_num : (0 : ℝ) < 1)) hj

theorem networkEdgeCost_zero (m : ℝ) : networkEdgeCost m 0 = ⊤ := by
  by_contra h
  apply networkHeatFive_zero_not_integrable m
  apply (lintegral_ofReal_ne_top_iff_integrable
    (by unfold networkHeatFive; fun_prop : Measurable (networkHeatFive m 0)).aestronglyMeasurable
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact networkHeatFive_nonneg hs.le m 0)).mp h

def networkDurationCost {E : Type*} [Fintype E] (m z : E → ℝ) : ℝ≥0∞ :=
  ∫⁻ s : E → ℝ, ENNReal.ofReal (∏ e, networkHeatFive (m e) (z e) (s e))
    ∂Measure.pi (fun _ : E => volume.restrict (Ioi (0 : ℝ)))

theorem networkDurationCost_positive {E : Type*} [Fintype E]
    (m z : E → ℝ) (hm : ∀ e, 0 < m e) (hz : ∀ e, 0 < z e) :
    networkDurationCost m z = ENNReal.ofReal (∏ e, networkEdgeGreen (m e) (z e)) := by
  have hi := Integrable.fintype_prod (fun e : E => networkHeatFive_integrable (m := m e) (hz e))
  have ha : ∀ᵐ s : E → ℝ ∂Measure.pi (fun _ : E => volume.restrict (Ioi (0 : ℝ))), ∀ e, 0 < s e := by
    apply ae_all_iff.mpr
    intro e
    exact (Measure.quasiMeasurePreserving_eval _ e).ae (ae_restrict_mem measurableSet_Ioi)
  unfold networkDurationCost
  rw [← ofReal_integral_eq_lintegral_ofReal hi (by
    filter_upwards [ha] with s hs
    exact Finset.prod_nonneg (fun e _ => networkHeatFive_nonneg (hs e).le _ _)),
    integral_fintype_prod_eq_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro e _
  exact networkHeatFive_integral (hm e) (hz e)

theorem networkDurationCost_common_law {E X : Type*} [Fintype E] [MeasurableSpace X]
    (μ : Measure X) (m : E → ℝ) (z : X → E → ℝ)
    (hm : ∀ e, 0 < m e) (hz : ∀ᵐ x ∂μ, ∀ e, 0 < z x e) :
    (∫⁻ x, networkDurationCost m (z x) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (∏ e, networkEdgeGreen (m e) (z x e)) ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [hz] with x hx
  exact networkDurationCost_positive m (z x) hm hx

def networkLowerConstant {E : Type*} [Fintype E] (m : E → ℝ) : ℝ :=
  ∏ e, Real.exp (-(m e)) / (8 * Real.pi ^ 2)

def networkUpperConstant {E : Type*} [Fintype E] (m : E → ℝ) : ℝ :=
  ∏ e, (1 + m e) / (8 * Real.pi ^ 2)

theorem networkEdgeGreen_bounds {m r : ℝ} (hm : 0 < m) (hr : r ∈ Ioc (0 : ℝ) 1) :
    (Real.exp (-m) / (8 * Real.pi ^ 2)) / r ^ 3 ≤ networkEdgeGreen m r ∧
      networkEdgeGreen m r ≤ ((1 + m) / (8 * Real.pi ^ 2)) / r ^ 3 := by
  have hr0 := hr.1
  have heLo : Real.exp (-m) ≤ Real.exp (-(m * r)) :=
    Real.exp_le_exp.mpr (by nlinarith [hr.2])
  have heHi : Real.exp (-(m * r)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hr.1])
  have hfactor : 1 ≤ 1 + m * r := by linarith [mul_pos hm hr0]
  have hfactorHi : 1 + m * r ≤ 1 + m := by nlinarith [hr.2]
  unfold networkEdgeGreen
  constructor
  · have hh : Real.exp (-m) ≤ (1 + m * r) * Real.exp (-(m * r)) :=
      heLo.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le)
    calc
      _ = Real.exp (-m) / (8 * Real.pi ^ 2 * r ^ 3) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hh (by positivity)
  · have hh : (1 + m * r) * Real.exp (-(m * r)) ≤ 1 + m := by
      simpa only [mul_one] using mul_le_mul hfactorHi heHi (Real.exp_pos _).le (by positivity)
    calc
      _ ≤ (1 + m) / (8 * Real.pi ^ 2 * r ^ 3) :=
        div_le_div_of_nonneg_right hh (by positivity)
      _ = _ := by ring

theorem networkGreen_product_bounds {E : Type*} [Fintype E]
    (m : E → ℝ) (hm : ∀ e, 0 < m e) {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) :
    networkLowerConstant m / r ^ (3 * Fintype.card E) ≤ ∏ e, networkEdgeGreen (m e) r ∧
      (∏ e, networkEdgeGreen (m e) r) ≤ networkUpperConstant m / r ^ (3 * Fintype.card E) := by
  have hr0 := hr.1
  have hm0 (e : E) := (hm e).le
  have hLo := Finset.prod_le_prod
    (fun e (_ : e ∈ Finset.univ) => by positivity :
      ∀ e ∈ Finset.univ, 0 ≤ (Real.exp (-(m e)) / (8 * Real.pi ^ 2)) / r ^ 3)
    (fun e (_ : e ∈ Finset.univ) => (networkEdgeGreen_bounds (hm e) hr).1)
  have hHi := Finset.prod_le_prod
    (fun e (_ : e ∈ Finset.univ) => by
      have hme := hm e
      unfold networkEdgeGreen
      positivity :
      ∀ e ∈ Finset.univ, 0 ≤ networkEdgeGreen (m e) r)
    (fun e (_ : e ∈ Finset.univ) => (networkEdgeGreen_bounds (hm e) hr).2)
  constructor
  · simpa only [networkLowerConstant, Finset.prod_div_distrib, Finset.prod_const,
      Finset.card_univ, ← pow_mul] using hLo
  · simpa only [networkUpperConstant, Finset.prod_div_distrib, Finset.prod_const,
      Finset.card_univ, ← pow_mul] using hHi

/-- The exact finite-edge proper-time cost has precisely the source's
inverse third moment per edge on a common collapsing positive width. -/
theorem networkDurationCost_inverse_moment_iff {E : Type*} [Fintype E]
    (μ : Measure ℝ) (m : E → ℝ) (hm : ∀ e, 0 < m e)
    (hr : ∀ᵐ r ∂μ, r ∈ Ioc (0 : ℝ) 1) :
    (∫⁻ r, networkDurationCost m (fun _ => r) ∂μ) < ⊤ ↔
      inverseMoment μ ((3 * Fintype.card E : ℕ) : ℝ) < ⊤ := by
  have hL : 0 < networkLowerConstant m := Finset.prod_pos (fun _ _ => by positivity)
  have hU : 0 < networkUpperConstant m := Finset.prod_pos (fun e _ => by exact div_pos (by linarith [hm e]) (by positivity))
  let R : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal ((r ^ (3 * Fintype.card E))⁻¹)
  have hRm : Measurable R := by dsimp [R]; fun_prop
  have hmoment : inverseMoment μ ((3 * Fintype.card E : ℕ) : ℝ) = ∫⁻ r, R r ∂μ := by
    unfold inverseMoment
    have hpos : ∀ᵐ r ∂μ, r ∈ Ioi (0 : ℝ) := hr.mono fun r hh => hh.1
    have hrestrict : μ.restrict (Ioi (0 : ℝ)) = μ := Measure.restrict_eq_self_of_ae_mem hpos
    rw [hrestrict]
    apply lintegral_congr_ae
    filter_upwards [hr] with r hh
    rw [Real.rpow_neg hh.1.le, Real.rpow_natCast]
  have hLo : ENNReal.ofReal (networkLowerConstant m) * (∫⁻ r, R r ∂μ) ≤
      ∫⁻ r, networkDurationCost m (fun _ => r) ∂μ := by
    rw [← lintegral_const_mul _ hRm]
    apply lintegral_mono_ae
    filter_upwards [hr] with r hh
    rw [networkDurationCost_positive _ _ hm (fun _ => hh.1),
      ← ENNReal.ofReal_mul hL.le]
    exact ENNReal.ofReal_le_ofReal (by simpa only [R, div_eq_mul_inv] using (networkGreen_product_bounds m hm hh).1)
  have hHi : (∫⁻ r, networkDurationCost m (fun _ => r) ∂μ) ≤
      ENNReal.ofReal (networkUpperConstant m) * (∫⁻ r, R r ∂μ) := by
    rw [← lintegral_const_mul _ hRm]
    apply lintegral_mono_ae
    filter_upwards [hr] with r hh
    rw [networkDurationCost_positive _ _ hm (fun _ => hh.1),
      ← ENNReal.ofReal_mul hU.le]
    exact ENNReal.ofReal_le_ofReal (by simpa only [R, div_eq_mul_inv] using (networkGreen_product_bounds m hm hh).2)
  rw [hmoment]
  constructor
  · intro h
    exact ENNReal.lt_top_of_mul_ne_top_right (hLo.trans_lt h).ne
      (ne_of_gt (ENNReal.ofReal_pos.mpr hL))
  · intro h
    exact hHi.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h)

def alternatingNetworkHeight (r : ℝ) {N : ℕ} (v : Fin (N + 1) × Bool) : ℝ :=
  if v.2 then r else 0

def alternatingNetworkNext {N : ℕ} (v : Fin (N + 1) × Bool) : Fin (N + 1) × Bool :=
  if v.2 then (v.1 + 1, false) else (v.1, true)

def alternatingNetworkDisplacement (r : ℝ) {N : ℕ} (v : Fin (N + 1) × Bool) : ℝ :=
  alternatingNetworkHeight r (alternatingNetworkNext v) - alternatingNetworkHeight r v

theorem alternatingNetwork_mark {N : ℕ} {r : ℝ} (hr : 0 ≤ r) (v : Fin (N + 1) × Bool) :
    |alternatingNetworkDisplacement r v| = r := by
  obtain ⟨v, b⟩ := v
  cases b <;> simp [alternatingNetworkDisplacement, alternatingNetworkNext, alternatingNetworkHeight,
    abs_of_nonneg hr]

theorem alternatingNetwork_total_displacement (N : ℕ) (r : ℝ) :
    (∑ v : Fin (N + 1) × Bool, alternatingNetworkDisplacement r v) = 0 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro v _
  simp [alternatingNetworkDisplacement, alternatingNetworkNext, alternatingNetworkHeight]

/-- There are 2(N+1) genuinely alternating edges. The returned position
has zero total displacement, while its proper-time cost tests the inverse
6(N+1)-st moment, i.e. the inverse third moment per edge. -/
theorem alternatingNetwork_inverse_moment_iff (N : ℕ) (μ : Measure ℝ)
    (m : (Fin (N + 1) × Bool) → ℝ) (hm : ∀ e, 0 < m e)
    (hr : ∀ᵐ r ∂μ, r ∈ Ioc (0 : ℝ) 1) :
    (∫⁻ r, networkDurationCost m (fun v => |alternatingNetworkDisplacement r v|) ∂μ) < ⊤ ↔
      inverseMoment μ ((6 * (N + 1) : ℕ) : ℝ) < ⊤ := by
  have he : (∫⁻ r, networkDurationCost m (fun v => |alternatingNetworkDisplacement r v|) ∂μ) =
      ∫⁻ r, networkDurationCost m (fun _ => r) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hr] with r hh
    congr 1
    funext v
    exact alternatingNetwork_mark hh.1.le v
  rw [he]
  have hcard : 3 * Fintype.card (Fin (N + 1) × Bool) = 6 * (N + 1) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    ring
  have h := networkDurationCost_inverse_moment_iff μ m hm hr
  rwa [hcard] at h

end UV
