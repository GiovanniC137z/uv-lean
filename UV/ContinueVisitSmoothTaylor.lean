import UV.ContinueVisitTaylorDensity
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Identification of the homogeneous profile with the first nonzero
Fréchet Taylor jet of the actual smooth normal state. -/

noncomputable section

open MeasureTheory Set Filter Metric Asymptotics
open scoped ENNReal Topology Nat

namespace UV.ContinueVisitSmoothTaylor

open UV.VerifyVisitCodimension UV.ContinueVisitNormalPolar UV.ContinueVisitTaylorDensity

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def normalTaylorJet (n j : ℕ) (ψ : NormalCoordinates n → F) (x : NormalCoordinates n) : F :=
  ((j ! : ℝ)⁻¹) • (iteratedFDeriv ℝ j ψ 0) (fun _ => x)

theorem normal_taylor_jet_continuous (n j : ℕ) (ψ : NormalCoordinates n → F) :
    Continuous (normalTaylorJet n j ψ) := by
  unfold normalTaylorJet
  exact continuous_const.smul ((iteratedFDeriv ℝ j ψ 0).cont.comp (continuous_pi fun _ =>
    continuous_id))

theorem normal_taylor_jet_homogeneous (n j : ℕ) (ψ : NormalCoordinates n → F)
    (t : ℝ) (x : NormalCoordinates n) :
    normalTaylorJet n j ψ (t • x) = t ^ j • normalTaylorJet n j ψ x := by
  unfold normalTaylorJet
  rw [show (fun _ : Fin j => t • x) = (fun i : Fin j => (fun _ : Fin j => t) i •
    (fun _ : Fin j => x) i) by rfl, ContinuousMultilinearMap.map_smul_univ,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_comm]

private theorem normal_line_iterated_derivative {n k N : ℕ}
    {ψ : NormalCoordinates n → F} (hψ : ContDiff ℝ N ψ) (hk : k ≤ N)
    (x : NormalCoordinates n) (t : ℝ) :
    iteratedDeriv k (fun s : ℝ => ψ (s • x)) t =
      (iteratedFDeriv ℝ k ψ (t • x)) (fun _ => x) := by
  let L : ℝ →L[ℝ] NormalCoordinates n := (ContinuousLinearMap.id ℝ ℝ).smulRight x
  change iteratedDeriv k (ψ ∘ L) t = _
  have hk' : (k : WithTop ℕ∞) ≤ (N : WithTop ℕ∞) := by exact_mod_cast hk
  rw [iteratedDeriv_eq_iteratedFDeriv, L.iteratedFDeriv_comp_right hψ t hk']
  simp [L]

private theorem normal_line_taylor_value {n j : ℕ} {ψ : NormalCoordinates n → F}
    (hψ : ContDiff ℝ (j + 1 : ℕ) ψ)
    (hzero : ∀ k < j, iteratedFDeriv ℝ k ψ 0 = 0) (x : NormalCoordinates n) :
    taylorWithinEval (fun s : ℝ => ψ (s • x)) j (Icc 0 1) 0 1 = normalTaylorJet n j ψ x := by
  have hline : ContDiff ℝ (j + 1 : ℕ) (fun s : ℝ => ψ (s • x)) :=
    hψ.comp (by fun_prop)
  rw [taylor_within_apply, Finset.sum_range_succ]
  have he (k : ℕ) (hk : k ≤ j + 1) :
      iteratedDerivWithin k (fun s : ℝ => ψ (s • x)) (Icc 0 1) 0 =
        (iteratedFDeriv ℝ k ψ 0) (fun _ => x) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
      ((hline.of_le (by exact_mod_cast hk)).contDiffAt) (by simp),
      normal_line_iterated_derivative hψ hk, zero_smul]
  rw [Finset.sum_eq_zero, zero_add, he j (Nat.le_succ _)]
  · simp [normalTaylorJet]
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [he k (hk.le.trans (Nat.le_succ _)), hzero k hk]
    simp

/-- The smooth state has the homogeneous degree-j diagonal Fréchet
jet plus a uniform little-o remainder when its lower jets vanish. -/
theorem normal_taylor_jet_remainder (n j : ℕ) {ψ : NormalCoordinates n → F}
    (hψ : ContDiff ℝ (j + 1 : ℕ) ψ)
    (hzero : ∀ k < j, iteratedFDeriv ℝ k ψ 0 = 0) :
    (fun x => ψ x - normalTaylorJet n j ψ x) =o[𝓝 0] (fun x => ‖x‖ ^ j) := by
  let D := fun x => iteratedFDeriv ℝ (j + 1) ψ x
  let C := ‖D 0‖ + 1
  have hC : 0 < C := add_pos_of_nonneg_of_pos (norm_nonneg _) one_pos
  have hc : Continuous D := hψ.continuous_iteratedFDeriv'
  have hev : ∀ᶠ x in 𝓝 (0 : NormalCoordinates n), ‖D x‖ < C :=
    hc.norm.continuousAt.eventually (Iio_mem_nhds (lt_add_one ‖D 0‖))
  obtain ⟨R, hR, hRbound⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hestimate (x : NormalCoordinates n) (hx : ‖x‖ < R) :
      ‖ψ x - normalTaylorJet n j ψ x‖ ≤ C * ‖x‖ ^ (j + 1) / (j ! : ℝ) := by
    have hline : ContDiff ℝ (j + 1 : ℕ) (fun s : ℝ => ψ (s • x)) :=
      hψ.comp (by fun_prop)
    have hder (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        ‖iteratedDerivWithin (j + 1) (fun s : ℝ => ψ (s • x)) (Icc 0 1) t‖ ≤
          C * ‖x‖ ^ (j + 1) := by
      rw [iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) hline.contDiffAt ht,
        normal_line_iterated_derivative hψ le_rfl]
      have hb : t • x ∈ ball (0 : NormalCoordinates n) R := by
        rw [mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1]
        exact (mul_le_of_le_one_left (norm_nonneg x) ht.2).trans_lt hx
      have hnorm : ‖D (t • x)‖ ≤ C := (hRbound _ hb).le
      have hD := (D (t • x)).le_opNorm (fun _ => x)
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hD
      exact hD.trans (mul_le_mul_of_nonneg_right hnorm (pow_nonneg (norm_nonneg x) _))
    have hT := taylor_mean_remainder_bound (n := j) (a := (0 : ℝ)) (b := 1) (x := 1)
      zero_le_one hline.contDiffOn (right_mem_Icc.mpr zero_le_one) hder
    rw [normal_line_taylor_value hψ hzero] at hT
    simpa only [one_smul, sub_zero, one_pow, mul_one] using hT
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  let K := C / (j ! : ℝ)
  have hj : 0 < (j ! : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hK : 0 < K := div_pos hC hj
  have hball : Metric.ball (0 : NormalCoordinates n) (min R (ε / K)) ∈ 𝓝 0 :=
    Metric.ball_mem_nhds _ (lt_min hR (div_pos hε hK))
  filter_upwards [hball] with x hx
  rw [mem_ball, dist_zero_right, lt_min_iff] at hx
  rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) _)]
  have hsmall : K * ‖x‖ ≤ ε := by
    rw [mul_comm]
    exact (le_div_iff₀ hK).mp hx.2.le
  calc
    _ ≤ C * ‖x‖ ^ (j + 1) / (j ! : ℝ) := hestimate x hx.1
    _ = (K * ‖x‖) * ‖x‖ ^ j := by unfold K; rw [pow_succ]; ring
    _ ≤ ε * ‖x‖ ^ j := mul_le_mul_of_nonneg_right hsmall (pow_nonneg (norm_nonneg x) _)

/-- Smooth-state specialization at its first nonzero normal Taylor
jet. Its leading coefficient is read on the actual unit sphere. -/
theorem smooth_normal_taylor_inverse_moment_iff (n j : ℕ) {ψ : NormalCoordinates n → F}
    (hψ : ContDiff ℝ (j + 1 : ℕ) ψ)
    (hzero : ∀ k < j, iteratedFDeriv ℝ k ψ 0 = 0)
    (hnz : ∃ u : NormalUnit n, normalTaylorJet n j ψ u ≠ 0) :
    (0 < ∫ u : NormalUnit n, ‖normalTaylorJet n j ψ u‖ ^ (2 : ℕ) ∂normalSphereMeasure n) ∧
      ∃ R > 0, ∀ ρ, 0 < ρ → ρ ≤ R →
        (IntegrableOn (normalTaylorWeight n ψ) (ball 0 ρ) ↔ n + 1 < 2 * j) := by
  have hcont := normal_taylor_jet_continuous n j ψ
  exact ⟨normal_taylor_angular_coefficient_pos n hcont hnz,
    normal_taylor_inverse_moment_iff n j hψ.continuous hcont
      (fun t _ x => normal_taylor_jet_homogeneous n j ψ t x) hnz
      (normal_taylor_jet_remainder n j hψ hzero)⟩

end UV.ContinueVisitSmoothTaylor
