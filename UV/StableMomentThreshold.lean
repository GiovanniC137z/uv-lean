import UV.PoissonTail
import UV.DepthAsymptotics
import Mathlib.Analysis.MeanInequalities

/-! The sixth moment threshold follows from a radial lower bound alone.
Coordinate permutation invariance of the comparison tail replaces an angular
sector construction. -/

noncomputable section
open MeasureTheory Real Filter Set
open scoped Topology ENNReal

namespace UV

def stableTailDensity (R : ℝ) (x : ScalarMomentum) : ℝ :=
  if R ≤ ‖x‖ then ‖x‖ ^ (-10 : ℤ) else 0

theorem stableTailDensity_nonneg (R : ℝ) (x : ScalarMomentum) :
    0 ≤ stableTailDensity R x := by
  unfold stableTailDensity
  split_ifs <;> positivity

theorem stableTailDensity_measurable (R : ℝ) : Measurable (stableTailDensity R) := by
  unfold stableTailDensity
  apply Measurable.ite (measurableSet_le measurable_const measurable_norm)
  · fun_prop
  · exact measurable_const

theorem scalar_norm_six_le_sum (x : ScalarMomentum) :
    ‖x‖^6 ≤ 16 * ∑ j : Fin 4, (x j)^6 := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (s := (Finset.univ : Finset (Fin 4))) (f := fun j => (x j)^2)
    (p := (3:ℝ)) (by norm_num) (fun j _ => sq_nonneg (x j))
  have hn : ‖x‖^2 = ∑ j : Fin 4, (x j)^2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using PiLp.norm_sq_eq_of_L2 (fun _ : Fin 4 => ℝ) x
  rw [show ‖x‖^6 = (‖x‖^2)^3 by ring, hn]
  norm_num [Real.rpow_natCast, ← pow_mul] at h
  exact h

theorem stableTailDensity_radial_six_not_integrable {R : ℝ} (hR : 0 < R) :
    ¬ Integrable (fun x : ScalarMomentum => ‖x‖^6 * stableTailDensity R x) := by
  intro hi
  have hr : IntegrableOn (fun r : ℝ => r^3 * (r^6 *
      (if R ≤ r then r^(-10:ℤ) else 0))) (Ioi 0) := by
    have hh := (integrable_fun_norm_addHaar (E := ScalarMomentum) volume
      (f := fun r : ℝ => r^6 * (if R ≤ r then r^(-10:ℤ) else 0))).mp hi
    simpa only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul] using hh
  have htail := hr.mono_set (Ioi_subset_Ioi hR.le)
  have hinv : IntegrableOn (fun r : ℝ => r^(-(1:ℝ))) (Ioi R) := by
    apply htail.congr_fun _ measurableSet_Ioi
    intro r hr
    change R < r at hr
    have hr0 : 0 < r := hR.trans hr
    dsimp only
    rw [if_pos hr.le, Real.rpow_neg_one, zpow_neg, zpow_ofNat]
    field_simp
  have h := (integrableOn_Ioi_rpow_iff hR).mp hinv
  norm_num at h

theorem stableTailDensity_coordinate_six_integrable_all (R : ℝ)
    (h0 : Integrable (fun x : ScalarMomentum => (x 0)^6 * stableTailDensity R x))
    (j : Fin 4) :
    Integrable (fun x : ScalarMomentum => (x j)^6 * stableTailDensity R x) := by
  let A : ScalarMomentum ≃ₗᵢ[ℝ] ScalarMomentum :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 j)
  have ha := A.measurePreserving.integrable_comp_of_integrable h0
  convert ha using 1
  funext x
  change (x j)^6 * stableTailDensity R x = (A x 0)^6 * stableTailDensity R (A x)
  have hn : stableTailDensity R (A x) = stableTailDensity R x := by
    simp only [stableTailDensity, A.norm_map]
  rw [hn]
  congr 2

theorem stableTailDensity_coordinate_six_not_integrable {R : ℝ} (hR : 0 < R) :
    ¬ Integrable (fun x : ScalarMomentum => (x 0)^6 * stableTailDensity R x) := by
  intro h0
  have hs := integrable_finset_sum (Finset.univ : Finset (Fin 4))
    (fun j _ => stableTailDensity_coordinate_six_integrable_all R h0 j)
  apply stableTailDensity_radial_six_not_integrable hR
  apply (hs.const_mul 16).mono'
  · exact (continuous_norm.pow 6).aestronglyMeasurable.mul
      (stableTailDensity_measurable R).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity)
      (stableTailDensity_nonneg R x)), ← Finset.sum_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (scalar_norm_six_le_sum x)
      (stableTailDensity_nonneg R x)

 theorem polynomial_tail_coordinate_six_not_integrable {C : ScalarMomentum → ℝ}
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hlower : ∀ x, R ≤ ‖x‖ → c ≤ ‖x‖^5 * C x) :
    ¬ Integrable (fun x : ScalarMomentum => (x 0)^6 * (C x)^2) := by
  intro hi
  apply stableTailDensity_coordinate_six_not_integrable hR
  apply (hi.const_mul ((c^2)⁻¹)).mono'
  · exact ((PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0).pow 6).aestronglyMeasurable.mul
      (stableTailDensity_measurable R).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity)
      (stableTailDensity_nonneg R x))]
    by_cases hx : R ≤ ‖x‖
    · have hr : 0 < ‖x‖ := hR.trans_le hx
      have hcx : c/‖x‖^5 ≤ C x := (div_le_iff₀ (pow_pos hr 5)).mpr (by
        simpa only [mul_comm] using hlower x hx)
      have hc0 : 0 ≤ C x := (by positivity : 0 ≤ c/‖x‖^5).trans hcx
      have hs := (sq_le_sq₀ (by positivity : 0 ≤ c/‖x‖^5) hc0).mpr hcx
      have htail : stableTailDensity R x ≤ (c^2)⁻¹ * (C x)^2 := by
        rw [stableTailDensity, if_pos hx]
        calc
          _ = (c^2)⁻¹ * (c/‖x‖^5)^2 := by
            rw [zpow_neg, zpow_ofNat]
            field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
      simpa only [mul_assoc, mul_left_comm (c^2)⁻¹] using
        mul_le_mul_of_nonneg_left htail (by positivity : 0 ≤ (x 0)^6)
    · rw [stableTailDensity, if_neg hx, mul_zero]
      positivity

 theorem polynomial_tail_coordinate_six_infinite {C : ScalarMomentum → ℝ}
    (hC : AEStronglyMeasurable C) {c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hlower : ∀ x, R ≤ ‖x‖ → c ≤ ‖x‖^5 * C x) :
    (∫⁻ x : ScalarMomentum, ENNReal.ofReal ((x 0)^6 * (C x)^2)) = ∞ := by
  by_contra hfinite
  apply polynomial_tail_coordinate_six_not_integrable hc hR hlower
  apply (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable _ _).mp hfinite
  · exact ((PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0).pow 6).aestronglyMeasurable.mul (hC.pow 2)
  · exact Eventually.of_forall fun _ => by positivity

 theorem positive_norm_tail_lower_bound {C : ScalarMomentum → ℝ} {c : ℝ}
    (hc : 0 < c)
    (htail : Tendsto (fun x => ‖x‖^5 * C x)
      (Filter.comap (fun x : ScalarMomentum => ‖x‖) atTop) (𝓝 c)) :
    ∃ R : ℝ, 0 < R ∧ ∀ x, R ≤ ‖x‖ → c/2 ≤ ‖x‖^5 * C x := by
  have hev := htail.eventually (eventually_gt_nhds (by linarith : c/2 < c))
  rw [eventually_comap] at hev
  obtain ⟨R,hR⟩ := eventually_atTop.mp hev
  refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x hx => ?_⟩
  exact (hR ‖x‖ ((le_max_left R 1).trans hx) x rfl).le

end UV
