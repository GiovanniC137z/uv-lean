import UV.ContinueNetworkBlind
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Necessary sign, drift, and visibility conditions for the literal
absolute directional model before the subspace power counts. -/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace

namespace UV

private theorem directionalMassiveFactor_ray_lower {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (ν : ℝ) (hν : 0 ≤ ν)
    (x u : V) {t : ℝ} (ht : 1 ≤ t) :
    (1 + (‖x‖ + ‖u‖) ^ 2) ^ (-ν) * t ^ (-(2 * ν)) ≤
      directionalMassiveFactor ν (x + t • u) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hn : ‖x + t • u‖ ≤ (‖x‖ + ‖u‖) * t := by
    have hh := norm_add_le x (t • u)
    rw [norm_smul, Real.norm_of_nonneg ht0.le] at hh
    rw [add_mul, mul_comm ‖u‖]
    exact hh.trans (add_le_add_right (le_mul_of_one_le_right (norm_nonneg _) ht) _)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have ht2 := one_le_pow₀ ht (n := 2)
  have hb : 1 + ‖x + t • u‖ ^ 2 ≤ (1 + (‖x‖ + ‖u‖) ^ 2) * t ^ 2 := by
    rw [mul_pow] at hs
    rw [add_mul, one_mul]
    exact add_le_add ht2 hs
  have hpow : t ^ (-(2 * ν)) = (t ^ (2 : ℕ)) ^ (-ν) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    push_cast
    ring_nf
  rw [hpow, ← Real.mul_rpow (by positivity) (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) hb (neg_nonpos.mpr hν)

variable {E : Type*} [Fintype E] {d : ℕ}
variable {V : E → Type*} [∀ e, NormedAddCommGroup (V e)] [∀ e, NormedSpace ℝ (V e)]

private theorem directionalAbsoluteModel_ray_not_integrable
    (Q : DirectionalMomentum (d + 1) →L[ℝ] DirectionalMomentum (d + 1))
    (h : DirectionalMomentum (d + 1))
    (C : ∀ e, DirectionalMomentum (d + 1) →L[ℝ] V e) (p : ∀ e, V e)
    (ν : E → ℝ) (hν : ∀ e, 0 ≤ ν e) (P : MvPolynomial (Fin (d + 1)) ℂ)
    (x u : DirectionalMomentum (d + 1)) {t₀ : ℝ}
    (hP : directionalNumerator P (x + t₀ • u) ≠ 0)
    {b : ℝ} (hb : 0 < b)
    (hg : ∀ᶠ t : ℝ in atTop, b * t ≤
      -inner ℝ (x + t • u) (Q (x + t • u)) + inner ℝ h (x + t • u)) :
    ¬ Integrable (fun t : ℝ => directionalAbsoluteModel Q h C p ν P (x + t • u)) := by
  obtain ⟨c, hc, hpoly⟩ := directionalNumerator_ray_eventually_lower P x u hP
  let a (e : E) : ℝ := (1 + (‖C e x + p e‖ + ‖C e u‖) ^ 2) ^ (-ν e)
  let A := ∏ e, a e
  let N := ∑ e, 2 * ν e
  have hA : 0 < A := Finset.prod_pos fun e _ => by dsimp [a]; positivity
  have hexp := (tendsto_atTop.1 (tendsto_exp_mul_div_rpow_atTop N b hb)) 1
  apply directional_not_integrable_of_eventually_pos (mul_pos hc hA)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hpoly, hg, hexp] with t ht hP' hg' hexp'
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hlower :
      A * t ^ (-N) ≤ ∏ e, directionalMassiveFactor (ν e) (C e (x + t • u) + p e) := by
    have hN : -N = ∑ e, -(2 * ν e) := by simp [N]
    rw [hN, Real.rpow_sum_of_pos ht0, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod (fun e _ => by dsimp [a]; positivity)
    intro e _
    have hline := directionalMassiveFactor_ray_lower (ν e) (hν e) (C e x + p e) (C e u) ht
    have hre : C e (x + t • u) + p e = (C e x + p e) + t • C e u := by
      simp only [map_add, map_smul, add_right_comm]
    rwa [hre]
  unfold directionalAbsoluteModel
  calc
    c * A ≤ (c * A) * (Real.exp (b * t) / t ^ N) :=
      le_mul_of_one_le_right (by positivity) hexp'
    _ = c * Real.exp (b * t) * (A * t ^ (-N)) := by
      rw [Real.rpow_neg ht0.le, div_eq_mul_inv]
      ring
    _ ≤ _ := mul_le_mul (mul_le_mul hP' (Real.exp_le_exp.mpr hg')
      (Real.exp_nonneg _) (norm_nonneg _)) hlower (by positivity) (by positivity)

private theorem directionalExponent_on_ray
    (Q : DirectionalMomentum (d + 1) →L[ℝ] DirectionalMomentum (d + 1))
    (h : DirectionalMomentum (d + 1))
    (hSym : ∀ k k', inner ℝ k (Q k') = inner ℝ k' (Q k))
    (x u : DirectionalMomentum (d + 1)) (t : ℝ) :
    -inner ℝ (x + t • u) (Q (x + t • u)) + inner ℝ h (x + t • u) =
      (-inner ℝ u (Q u)) * t ^ 2 +
      (inner ℝ h u - 2 * inner ℝ u (Q x)) * t +
        (-inner ℝ x (Q x) + inner ℝ h x) := by
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hSym x u]
  ring

/-- A negative direction of the actual symmetric Gaussian form makes
the absolute coefficient with any nonzero polynomial divergent. -/
theorem directionalAbsoluteModel_not_integrable_of_negative_form
    (Q : DirectionalMomentum (d + 1) →L[ℝ] DirectionalMomentum (d + 1))
    (h : DirectionalMomentum (d + 1))
    (C : ∀ e, DirectionalMomentum (d + 1) →L[ℝ] V e) (p : ∀ e, V e)
    (ν : E → ℝ) (hν : ∀ e, 0 ≤ ν e) (P : MvPolynomial (Fin (d + 1)) ℂ)
    (hSym : ∀ k k', inner ℝ k (Q k') = inner ℝ k' (Q k)) (hP : P ≠ 0)
    (w : DirectionalMomentum (d + 1)) (hw : inner ℝ w (Q w) < 0) :
    ¬ Integrable (directionalAbsoluteModel Q h C p ν P) := by
  intro hI
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr (by intro hzero; simp [hzero] at hw)
  let u := ‖w‖⁻¹ • w
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hwn.le), hwn.ne']
  have huQ : inner ℝ u (Q u) < 0 := by
    simp only [u, map_smul, real_inner_smul_left, real_inner_smul_right]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hwn) (mul_neg_of_pos_of_neg (inv_pos.mpr hwn) hw)
  obtain ⟨x, t₀, hpy, hiy⟩ := directionalFiber_choose_integrable hI hP hu
  apply directionalAbsoluteModel_ray_not_integrable Q h C p ν hν P x u hpy zero_lt_one ?_ hiy
  let a := -inner ℝ u (Q u)
  let b := inner ℝ h u - 2 * inner ℝ u (Q x)
  let c := -inner ℝ x (Q x) + inner ℝ h x
  have ha : 0 < a := neg_pos.mpr huQ
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop ((1 + |b| + |c|) / a)]
    with t ht ht'
  rw [directionalExponent_on_ray Q h hSym, one_mul]
  change t ≤ a * t ^ 2 + b * t + c
  have h1 : 1 + |b| + |c| ≤ a * t := by
    simpa only [mul_comm t a] using (div_le_iff₀ ha).mp ht'
  have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : 0 ≤ t)
  have h3 := mul_le_mul_of_nonneg_right (neg_le_abs b) (by linarith : 0 ≤ t)
  have h4 := le_mul_of_one_le_right (abs_nonneg c) ht
  nlinarith only [h2, h3, h4, neg_le_abs c]

/-- A nonzero drift on the kernel makes the absolute coefficient
divergent even when the routed massive factors see that direction. -/
theorem directionalAbsoluteModel_not_integrable_of_kernel_drift
    (Q : DirectionalMomentum (d + 1) →L[ℝ] DirectionalMomentum (d + 1))
    (h : DirectionalMomentum (d + 1))
    (C : ∀ e, DirectionalMomentum (d + 1) →L[ℝ] V e) (p : ∀ e, V e)
    (ν : E → ℝ) (hν : ∀ e, 0 ≤ ν e) (P : MvPolynomial (Fin (d + 1)) ℂ)
    (hSym : ∀ k k', inner ℝ k (Q k') = inner ℝ k' (Q k)) (hP : P ≠ 0)
    (w : DirectionalMomentum (d + 1)) (hw : Q w = 0) (hh : inner ℝ h w ≠ 0) :
    ¬ Integrable (directionalAbsoluteModel Q h C p ν P) := by
  intro hI
  have hv : ∃ v : DirectionalMomentum (d + 1), Q v = 0 ∧ 0 < inner ℝ h v := by
    rcases lt_or_gt_of_ne hh with hneg | hpos
    · exact ⟨-w, by simp [hw], by simpa using neg_pos.mpr hneg⟩
    · exact ⟨w, hw, hpos⟩
  obtain ⟨v, hvQ, hvh⟩ := hv
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr (by intro hzero; simp [hzero] at hvh)
  let u := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hvn.le), hvn.ne']
  have huQ : Q u = 0 := by simp [u, hvQ]
  have huh : 0 < inner ℝ h u := by
    rw [show u = ‖v‖⁻¹ • v from rfl, real_inner_smul_right]
    exact mul_pos (inv_pos.mpr hvn) hvh
  obtain ⟨x, t₀, hpy, hiy⟩ := directionalFiber_choose_integrable hI hP hu
  have hhalf : 0 < inner ℝ h u / 2 := by positivity
  apply directionalAbsoluteModel_ray_not_integrable Q h C p ν hν P x u hpy hhalf ?_ hiy
  let c := -inner ℝ x (Q x) + inner ℝ h x
  filter_upwards [eventually_ge_atTop (-c / (inner ℝ h u / 2))] with t ht
  have hcross : inner ℝ u (Q x) = 0 := by rw [hSym, huQ, inner_zero_right]
  rw [directionalExponent_on_ray Q h hSym]
  simp only [huQ, hcross, inner_zero_right, neg_zero, zero_mul, mul_zero, sub_zero, zero_add]
  have ht' := (div_le_iff₀ hhalf).mp ht
  dsimp [c] at ht'
  linarith

/-- The sign, kernel-drift, and combined-route conditions in the
directional test are all necessary for its actual polynomial integral. -/
theorem directionalAbsoluteModel_sign_drift_visibility
    (Q : DirectionalMomentum (d + 1) →L[ℝ] DirectionalMomentum (d + 1))
    (h : DirectionalMomentum (d + 1))
    (C : ∀ e, DirectionalMomentum (d + 1) →L[ℝ] V e) (p : ∀ e, V e)
    (ν : E → ℝ) (hν : ∀ e, 0 ≤ ν e) (P : MvPolynomial (Fin (d + 1)) ℂ)
    (hSym : ∀ k k', inner ℝ k (Q k') = inner ℝ k' (Q k)) (hP : P ≠ 0)
    (hI : Integrable (directionalAbsoluteModel Q h C p ν P)) :
    (∀ w, 0 ≤ inner ℝ w (Q w)) ∧ (∀ w, Q w = 0 → inner ℝ h w = 0) ∧
      (∀ w, Q w = 0 → (∀ e, C e w = 0) → w = 0) := by
  have hd (w : DirectionalMomentum (d + 1)) (hw : Q w = 0) : inner ℝ h w = 0 := by
    by_contra hne
    exact directionalAbsoluteModel_not_integrable_of_kernel_drift Q h C p ν hν P
      hSym hP w hw hne hI
  refine ⟨fun w => le_of_not_gt (fun hw => ?_), hd, fun w hw hC => ?_⟩
  · exact directionalAbsoluteModel_not_integrable_of_negative_form Q h C p ν hν P
      hSym hP w hw hI
  · by_contra hne
    exact directionalAbsoluteModel_not_integrable_of_common_blind Q h C p ν P
      hSym hP w hne hw (hd w hw) hC hI

end UV
