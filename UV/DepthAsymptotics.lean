import UV.DepthMonotonicity
import UV.GlobalConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! Fourier-normalized one-line depth asymptotics from
`prop:OQED-depth-stability`. -/

noncomputable section
open MeasureTheory Filter Set Real
open scoped Topology

namespace UV

def oneLineIntegrand (d a M m : ℝ) (q : ScalarMomentum) : ℝ :=
  ‖q‖ ^ d * kernel a M (‖q‖ ^ 2) / (‖q‖ ^ 2 + m ^ 2)

def oneLineComparison (d a M m : ℝ) : ℝ :=
  (2 * Real.pi) ^ (-4 : ℤ) * ∫ q, oneLineIntegrand d a M m q

def oneLineRadial (d a M m r : ℝ) : ℝ :=
  r ^ (d + 3) * kernel a M (r ^ 2) / (r ^ 2 + m ^ 2)

theorem oneLineRadial_nonneg (d a M m : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ oneLineRadial d a M m r := by
  unfold oneLineRadial
  exact div_nonneg (mul_nonneg (Real.rpow_nonneg hr _) (kernel_pos _ _ _).le) (by positivity)

theorem oneLineRadial_bound {a : ℝ} (ha : 0 ≤ a) (d M m : ℝ) {r : ℝ} (hr : 0 < r) :
    oneLineRadial d a M m r ≤ Real.exp (a * M) * (r ^ (d + 1) * Real.exp (-a * r)) := by
  have hk := kernel_upper (M := M) ha (sq_nonneg r)
  rw [Real.sqrt_sq hr.le] at hk
  have hp : r ^ (d + 3) / r ^ 2 = r ^ (d + 1) := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_sub hr]
    congr 1
    norm_num
    ring
  unfold oneLineRadial
  calc
    _ ≤ r ^ (d + 3) * kernel a M (r ^ 2) / r ^ 2 := by
      apply div_le_div_of_nonneg_left
        (mul_nonneg (Real.rpow_nonneg hr.le _) (kernel_pos _ _ _).le) (sq_pos_of_pos hr)
      nlinarith [sq_nonneg m]
    _ = (r ^ (d + 3) / r ^ 2) * kernel a M (r ^ 2) := by ring
    _ = r ^ (d + 1) * kernel a M (r ^ 2) := by rw [hp]
    _ ≤ r ^ (d + 1) * (Real.exp (a * M) * Real.exp (-a * r)) := by gcongr
    _ = _ := by ring

theorem oneLineRadial_integrable {d a : ℝ} (hd : 0 ≤ d) (ha : 0 < a) (M m : ℝ) :
    IntegrableOn (oneLineRadial d a M m) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := 1) (s := d + 1) (b := a) (by linarith) (by norm_num) ha
  simp only [Real.rpow_one] at h
  apply (h.const_mul (Real.exp (a * M))).mono'
  · apply Measurable.aestronglyMeasurable
    unfold oneLineRadial kernel depthProfile
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_of_nonneg (oneLineRadial_nonneg d a M m hr.le)]
    exact oneLineRadial_bound ha.le d M m hr

theorem oneLine_radial_density (d a M m : ℝ) {r : ℝ} (hr : 0 < r) :
    r ^ (Module.finrank ℝ ScalarMomentum - 1) •
      (r ^ d * kernel a M (r ^ 2) / (r ^ 2 + m ^ 2)) = oneLineRadial d a M m r := by
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
  unfold oneLineRadial
  rw [← mul_div_assoc, ← mul_assoc, ← Real.rpow_natCast r 3, ← Real.rpow_add hr]
  congr 3
  ring

theorem oneLineIntegrand_integrable {d a : ℝ} (hd : 0 ≤ d) (ha : 0 < a) (M m : ℝ) :
    Integrable (oneLineIntegrand d a M m) := by
  apply (integrable_fun_norm_addHaar (E := ScalarMomentum) volume
    (f := fun r : ℝ => r ^ d * kernel a M (r ^ 2) / (r ^ 2 + m ^ 2))).mpr
  exact (oneLineRadial_integrable hd ha M m).congr_fun
    (fun r hr => (oneLine_radial_density d a M m hr).symm) measurableSet_Ioi

theorem fourDimensional_unitBall_volume :
    volume.real (Metric.ball (0 : ScalarMomentum) 1) = Real.pi ^ 2 / 2 := by
  rw [measureReal_def, EuclideanSpace.volume_ball]
  norm_num [Real.Gamma_nat_eq_factorial, Real.sq_sqrt Real.pi_nonneg]
  rw [ENNReal.toReal_ofReal (by positivity)]
  congr 1
  nlinarith [Real.sq_sqrt Real.pi_nonneg]

theorem oneLineComparison_radial (d a M m : ℝ) :
    oneLineComparison d a M m =
      (8 * Real.pi ^ 2)⁻¹ * ∫ r in Ioi 0, oneLineRadial d a M m r := by
  unfold oneLineComparison oneLineIntegrand
  rw [integral_fun_norm_addHaar (E := ScalarMomentum) volume
    (fun r : ℝ => r ^ d * kernel a M (r ^ 2) / (r ^ 2 + m ^ 2))]
  have hrad : (∫ r in Ioi 0, r ^ (Module.finrank ℝ ScalarMomentum - 1) •
      (r ^ d * kernel a M (r ^ 2) / (r ^ 2 + m ^ 2))) =
      ∫ r in Ioi 0, oneLineRadial d a M m r :=
    setIntegral_congr_fun measurableSet_Ioi (fun r hr => oneLine_radial_density d a M m hr)
  rw [hrad, fourDimensional_unitBall_volume]
  simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
  rw [zpow_neg, zpow_ofNat]
  field_simp
  ring

theorem radial_integral_scale (d : ℝ) {s : ℝ} (hs : 0 < s) (f : ℝ → ℝ) :
    s ^ (d + 4) * (∫ r in Ioi 0, r ^ (d + 3) * f r) =
      ∫ v in Ioi 0, v ^ (d + 3) * f (s⁻¹ * v) := by
  have hc := integral_comp_mul_left_Ioi (fun r : ℝ => r ^ (d + 3) * f r) 0 (inv_pos.mpr hs)
  simp only [mul_zero, inv_inv, smul_eq_mul] at hc
  have hp {v : ℝ} (hv : 0 < v) :
      s ^ (d + 3) * (s⁻¹ * v) ^ (d + 3) = v ^ (d + 3) := by
    rw [← Real.mul_rpow hs.le (by positivity), mul_inv_cancel_left₀ hs.ne']
  have he : s ^ (d + 3) * s = s ^ (d + 4) := by
    calc
      _ = s ^ (d + 3) * s ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = s ^ (d + 3 + 1) := (Real.rpow_add hs _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ = s ^ (d + 3) * (s * ∫ r in Ioi 0, r ^ (d + 3) * f r) := by rw [← mul_assoc, he]
    _ = s ^ (d + 3) * ∫ v in Ioi 0, (s⁻¹ * v) ^ (d + 3) * f (s⁻¹ * v) := by rw [hc]
    _ = ∫ v in Ioi 0, s ^ (d + 3) * ((s⁻¹ * v) ^ (d + 3) * f (s⁻¹ * v)) := by
      rw [integral_const_mul]
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      rw [← mul_assoc, hp hv]

theorem oneLineComparison_scaled_radial (d a M m : ℝ) {s : ℝ} (hs : 0 < s) :
    s ^ (d + 4) * oneLineComparison d a M m = (8 * Real.pi ^ 2)⁻¹ *
      ∫ v in Ioi 0, v ^ (d + 3) * kernel a M ((s⁻¹ * v) ^ 2) /
        ((s⁻¹ * v) ^ 2 + m ^ 2) := by
  rw [oneLineComparison_radial]
  simp only [oneLineRadial, mul_div_assoc]
  rw [← mul_assoc, mul_comm (s ^ (d + 4)), mul_assoc, radial_integral_scale d hs]

theorem kernel_scale_input {s : ℝ} (hs : 0 < s) (a M v : ℝ) :
    kernel a M ((s⁻¹ * v) ^ 2) = kernel (a / s) (s * M) (v ^ 2) := by
  have he : v ^ 2 + (s * M) ^ 2 = s ^ 2 * ((s⁻¹ * v) ^ 2 + M ^ 2) := by
    field_simp
  unfold kernel depthProfile
  rw [he, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le]
  congr 1
  field_simp

theorem oneLineComparison_depth_scaling (d : ℝ) {a : ℝ} (ha : 0 < a) (M m : ℝ) :
    a ^ (d + 2) * oneLineComparison d a M m = oneLineComparison d 1 (a * M) (a * m) := by
  have hs := oneLineComparison_scaled_radial d a M m ha
  have he : ∀ v : ℝ,
      v ^ (d + 3) * kernel a M ((a⁻¹ * v) ^ 2) / ((a⁻¹ * v) ^ 2 + m ^ 2) =
        a ^ 2 * oneLineRadial d 1 (a * M) (a * m) v := by
    intro v
    rw [kernel_scale_input ha, div_self ha.ne']
    have hden : (a⁻¹ * v) ^ 2 + m ^ 2 = (v ^ 2 + (a * m) ^ 2) / a ^ 2 := by
      field_simp
    rw [hden, div_div_eq_mul_div]
    unfold oneLineRadial
    ring
  simp_rw [he] at hs
  rw [integral_const_mul] at hs
  have hs' : a ^ (d + 4) * oneLineComparison d a M m =
      a ^ 2 * oneLineComparison d 1 (a * M) (a * m) := by
    rw [oneLineComparison_radial d 1 (a * M) (a * m)]
    calc
      _ = (8 * Real.pi ^ 2)⁻¹ * (a ^ 2 * ∫ r in Ioi 0, oneLineRadial d 1 (a * M) (a * m) r) := hs
      _ = _ := by ring
  have hp : a ^ (d + 4) = a ^ 2 * a ^ (d + 2) := by
    rw [← Real.rpow_natCast a 2, ← Real.rpow_add ha]
    congr 1
    norm_num
    ring
  apply (mul_left_cancel₀ (sq_pos_of_pos ha).ne')
  calc
    a ^ 2 * (a ^ (d + 2) * oneLineComparison d a M m) =
        a ^ (d + 4) * oneLineComparison d a M m := by rw [hp]; ring
    _ = a ^ 2 * oneLineComparison d 1 (a * M) (a * m) := hs'

theorem oneLineRadial_massless_unit (d : ℝ) {r : ℝ} (hr : 0 < r) :
    oneLineRadial d 1 0 0 r = r ^ (d + 1) * Real.exp (-r) := by
  unfold oneLineRadial kernel depthProfile
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, sub_zero,
    Real.sqrt_sq hr.le, neg_one_mul]
  rw [← div_mul_eq_mul_div, ← Real.rpow_natCast r 2, ← Real.rpow_sub hr]
  congr 2
  norm_num
  ring

theorem radial_exponential_integral {d : ℝ} (hd : 0 ≤ d) :
    (∫ r in Ioi 0, r ^ (d + 1) * Real.exp (-r)) = Real.Gamma (d + 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := d + 1) (b := 1)
    (by norm_num) (by linarith) (by norm_num)
  simpa only [Real.rpow_one, Real.one_rpow, one_mul, neg_one_mul, div_one, one_div_one,
    mul_one, show d + 1 + 1 = d + 2 by ring] using h

theorem oneLineComparison_zero_depth {d M m : ℝ} (hd : 0 ≤ d) (hM : 0 ≤ M) :
    Tendsto (fun a : ℝ => a ^ (d + 2) * oneLineComparison d a M m) (𝓝[>] 0)
      (𝓝 (Real.Gamma (d + 2) / (8 * Real.pi ^ 2))) := by
  have hgi := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := 1) (s := d + 1) (b := 1) (by linarith) (by norm_num) (by norm_num)
  simp only [Real.rpow_one, neg_one_mul] at hgi
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun a r => oneLineRadial d 1 (a * M) (a * m) r)
    (f := fun r => r ^ (d + 1) * Real.exp (-r))
    (l := 𝓝[>] (0 : ℝ)) (fun r => Real.exp M * (r ^ (d + 1) * Real.exp (-r)))
    (Eventually.of_forall (fun a => by
      apply Measurable.aestronglyMeasurable
      unfold oneLineRadial kernel depthProfile
      fun_prop))
    (by
      filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
        with a ha
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      rw [Real.norm_of_nonneg (oneLineRadial_nonneg _ _ _ _ hr.le)]
      calc
        _ ≤ Real.exp (a * M) * (r ^ (d + 1) * Real.exp (-r)) := by
          simpa only [one_mul, neg_one_mul] using oneLineRadial_bound (by norm_num : (0 : ℝ) ≤ 1) d (a * M) (a * m) hr
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (by nlinarith))
          (mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_pos _).le))
    (hgi.const_mul (Real.exp M))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : 0 < r := hr
      have hc : ContinuousAt (fun a : ℝ => oneLineRadial d 1 (a * M) (a * m) r) 0 := by
        unfold oneLineRadial kernel depthProfile
        fun_prop (disch := positivity)
      simpa only [zero_mul, oneLineRadial_massless_unit d hr] using
        hc.tendsto.mono_left nhdsWithin_le_nhds)
  rw [radial_exponential_integral hd] at ht
  have hT : Tendsto (fun a : ℝ => oneLineComparison d 1 (a * M) (a * m)) (𝓝[>] 0)
      (𝓝 (Real.Gamma (d + 2) / (8 * Real.pi ^ 2))) := by
    have he : Real.Gamma (d + 2) / (8 * Real.pi ^ 2) =
        (8 * Real.pi ^ 2)⁻¹ * Real.Gamma (d + 2) := by ring
    rw [he]
    simpa only [oneLineComparison_radial] using
      ht.const_mul ((8 * Real.pi ^ 2)⁻¹)
  apply hT.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (oneLineComparison_depth_scaling d ha M m).symm

theorem oneLineComparison_monotone_auxMass {d a M N m : ℝ} (hd : 0 ≤ d) (ha : 0 < a)
    (hM : 0 ≤ M) (hMN : M ≤ N) : oneLineComparison d a M m ≤ oneLineComparison d a N m := by
  rw [oneLineComparison_radial, oneLineComparison_radial]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono_ae (oneLineRadial_integrable hd ha M m) (oneLineRadial_integrable hd ha N m)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  unfold oneLineRadial
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (kernel_monotone_mass ha.le hM hMN (sq_nonneg r))
    (Real.rpow_nonneg hr.le _)

theorem oneLineComparison_antitone_mass {d a M m n : ℝ} (hd : 0 ≤ d) (ha : 0 < a)
    (hm : 0 ≤ m) (hmn : m ≤ n) : oneLineComparison d a M n ≤ oneLineComparison d a M m := by
  rw [oneLineComparison_radial, oneLineComparison_radial]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono_ae (oneLineRadial_integrable hd ha M n) (oneLineRadial_integrable hd ha M m)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  unfold oneLineRadial
  apply div_le_div_of_nonneg_left
    (mul_nonneg (Real.rpow_nonneg hr.le _) (kernel_pos _ _ _).le)
    (by have hr0 : 0 < r := hr; positivity)
  have hn : 0 ≤ n := hm.trans hmn
  nlinarith

/-- Uniform zero-depth convergence on every bounded nonnegative mass square. -/
theorem oneLineComparison_zero_depth_uniform_bounded {d K : ℝ} (hd : 0 ≤ d) (hK : 0 ≤ K) :
    ∀ ε > 0, ∃ δ > 0, ∀ a, 0 < a → a < δ → ∀ M m,
      0 ≤ M → M ≤ K → 0 ≤ m → m ≤ K →
      |a ^ (d + 2) * oneLineComparison d a M m - Real.Gamma (d + 2) / (8 * Real.pi ^ 2)| < ε := by
  intro ε hε
  let C := Real.Gamma (d + 2) / (8 * Real.pi ^ 2)
  have hl := oneLineComparison_zero_depth (M := 0) (m := K) hd (by norm_num)
  have hu := oneLineComparison_zero_depth (M := K) (m := 0) hd hK
  have hle : ∀ᶠ a : ℝ in 𝓝[>] 0, |a ^ (d + 2) * oneLineComparison d a 0 K - C| < ε := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hl.eventually (Metric.ball_mem_nhds C hε)
  have hue : ∀ᶠ a : ℝ in 𝓝[>] 0, |a ^ (d + 2) * oneLineComparison d a K 0 - C| < ε := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hu.eventually (Metric.ball_mem_nhds C hε)
  obtain ⟨δ, hδ, hh⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hle.and hue)
  refine ⟨δ, hδ, fun a ha haδ M m hM hMK hm hmK => ?_⟩
  have hbounds := hh ⟨ha, haδ⟩
  change |a ^ (d + 2) * oneLineComparison d a 0 K - C| < ε ∧
    |a ^ (d + 2) * oneLineComparison d a K 0 - C| < ε at hbounds
  have hlo : oneLineComparison d a 0 K ≤ oneLineComparison d a M m :=
    (oneLineComparison_monotone_auxMass hd ha (by norm_num) hM).trans
      (oneLineComparison_antitone_mass hd ha hm hmK)
  have hup : oneLineComparison d a M m ≤ oneLineComparison d a K 0 :=
    (oneLineComparison_monotone_auxMass hd ha hM hMK).trans
      (oneLineComparison_antitone_mass hd ha (by norm_num) hm)
  have hpow : 0 ≤ a ^ (d + 2) := Real.rpow_nonneg ha.le _
  have hlo' := mul_le_mul_of_nonneg_left hlo hpow
  have hup' := mul_le_mul_of_nonneg_left hup hpow
  have hl' := (abs_lt.mp hbounds.1).1
  have hu' := (abs_lt.mp hbounds.2).2
  apply abs_lt.mpr
  dsimp [C] at *
  constructor <;> linarith

theorem kernel_zero_mass_rescaled {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    kernel a 0 ((a⁻¹ * r) ^ 2) = Real.exp (-r) := by
  rw [kernel_scale_input ha, div_self ha.ne', mul_zero]
  simp [kernel, depthProfile, Real.sqrt_sq hr.le]

theorem radial_exponential_integral_add_two {d : ℝ} (hd : 0 ≤ d) :
    (∫ r in Ioi 0, r ^ (d + 3) * Real.exp (-r)) = Real.Gamma (d + 4) := by
  simpa only [show d + 2 + 1 = d + 3 by ring, show d + 2 + 2 = d + 4 by ring] using
    radial_exponential_integral (d := d + 2) (by linarith)

theorem oneLineComparison_strong_depth_zero_auxMass {d m : ℝ} (hd : 0 ≤ d) (hm : 0 < m) :
    Tendsto (fun a : ℝ => a ^ (d + 4) * oneLineComparison d a 0 m) atTop
      (𝓝 (Real.Gamma (d + 4) / (8 * Real.pi ^ 2 * m ^ 2))) := by
  have hgi := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := 1) (s := d + 3) (b := 1) (by linarith) (by norm_num) (by norm_num)
  simp only [Real.rpow_one, neg_one_mul] at hgi
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun a r => r ^ (d + 3) * Real.exp (-r) / ((a⁻¹ * r) ^ 2 + m ^ 2))
    (f := fun r => r ^ (d + 3) * Real.exp (-r) / m ^ 2)
    (l := atTop) (fun r => (r ^ (d + 3) * Real.exp (-r)) / m ^ 2)
    (Eventually.of_forall (fun a => by apply Measurable.aestronglyMeasurable; fun_prop))
    (Eventually.of_forall (fun a => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : 0 < r := hr
      rw [Real.norm_of_nonneg (by positivity)]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [sq_nonneg (a⁻¹ * r)]))
    (hgi.div_const (m ^ 2))
    (Eventually.of_forall (fun r => by
      have hc : ContinuousAt (fun c : ℝ => r ^ (d + 3) * Real.exp (-r) /
          ((c * r) ^ 2 + m ^ 2)) 0 := by fun_prop (disch := positivity)
      simpa using hc.tendsto.comp tendsto_inv_atTop_zero))
  rw [integral_div, radial_exponential_integral_add_two hd] at ht
  have hval : Real.Gamma (d + 4) / (8 * Real.pi ^ 2 * m ^ 2) =
      (8 * Real.pi ^ 2)⁻¹ * (Real.Gamma (d + 4) / m ^ 2) := by ring
  rw [hval]
  apply (ht.const_mul ((8 * Real.pi ^ 2)⁻¹)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  rw [oneLineComparison_scaled_radial d a 0 m ha]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [kernel_zero_mass_rescaled ha hr]

theorem kernel_rationalized_rescale {a M r : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (hr : 0 < r) :
    kernel a M (a⁻¹ * r ^ 2) =
      Real.exp (-(r ^ 2 / (Real.sqrt (a⁻¹ * r ^ 2 + M ^ 2) + M))) := by
  unfold kernel
  rw [depthProfile_eq_div hM (mul_pos (inv_pos.mpr ha) (sq_pos_of_pos hr))]
  congr 1
  field_simp

theorem oneLineComparison_sqrt_scaled {d a M m : ℝ} (ha : 0 < a) (hM : 0 ≤ M) :
    a ^ ((d + 4) / 2) * oneLineComparison d a M m = (8 * Real.pi ^ 2)⁻¹ *
      ∫ r in Ioi 0, r ^ (d + 3) *
        Real.exp (-(r ^ 2 / (Real.sqrt (a⁻¹ * r ^ 2 + M ^ 2) + M))) /
          (a⁻¹ * r ^ 2 + m ^ 2) := by
  have hp : (Real.sqrt a) ^ (d + 4) = a ^ ((d + 4) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ha.le]
    congr 1
    ring
  rw [← hp, oneLineComparison_scaled_radial d a M m (Real.sqrt_pos.mpr ha)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [mul_pow, inv_pow, Real.sq_sqrt ha.le, kernel_rationalized_rescale ha hM hr]

theorem radial_gaussian_integral_add_two {d M : ℝ} (hd : 0 ≤ d) (hM : 0 < M) :
    (∫ r in Ioi 0, r ^ (d + 3) * Real.exp (-(r ^ 2 / (2 * M)))) =
      (2 * M) ^ ((d + 4) / 2) / 2 * Real.Gamma ((d + 4) / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := d + 3) (b := (2 * M)⁻¹)
    (by norm_num) (by linarith) (by positivity)
  simp only [Real.rpow_two, show d + 3 + 1 = d + 4 by ring,
    show -(d + 4) / 2 = -((d + 4) / 2) by ring] at h
  have hp : ((2 * M)⁻¹) ^ (-((d + 4) / 2)) = (2 * M) ^ ((d + 4) / 2) := by
    rw [Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv]
  rw [hp] at h
  calc
    _ = ∫ r in Ioi 0, r ^ (d + 3) * Real.exp (-(2 * M)⁻¹ * r ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r _
      dsimp only
      congr 2
      ring
    _ = _ := by rw [h]; ring

theorem oneLineComparison_strong_depth_pos_auxMass {d M m : ℝ}
    (hd : 0 ≤ d) (hM : 0 < M) (hm : 0 < m) :
    Tendsto (fun a : ℝ => a ^ ((d + 4) / 2) * oneLineComparison d a M m) atTop
      (𝓝 ((2 * M) ^ ((d + 4) / 2) * Real.Gamma ((d + 4) / 2) /
        (16 * Real.pi ^ 2 * m ^ 2))) := by
  have hgi := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := 1) (s := d + 3) (b := 1) (by linarith) (by norm_num) (by norm_num)
  simp only [Real.rpow_one, neg_one_mul] at hgi
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun a r => r ^ (d + 3) *
      Real.exp (-(r ^ 2 / (Real.sqrt (a⁻¹ * r ^ 2 + M ^ 2) + M))) / (a⁻¹ * r ^ 2 + m ^ 2))
    (f := fun r => r ^ (d + 3) * Real.exp (-(r ^ 2 / (2 * M))) / m ^ 2)
    (l := atTop) (fun r => Real.exp M / m ^ 2 * (r ^ (d + 3) * Real.exp (-r)))
    (Eventually.of_forall (fun a => by apply Measurable.aestronglyMeasurable; fun_prop))
    (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
      have ha0 : 0 < a := by linarith
      have hc0 : 0 ≤ a⁻¹ := (inv_pos.mpr ha0).le
      have hc1 : a⁻¹ ≤ 1 := by rw [inv_eq_one_div]; exact (div_le_iff₀ ha0).mpr (by linarith)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : 0 < r := hr
      have hratio : depthProfile M (r ^ 2) ≤
          r ^ 2 / (Real.sqrt (a⁻¹ * r ^ 2 + M ^ 2) + M) := by
        rw [depthProfile_eq_div hM.le (sq_pos_of_pos hr0)]
        apply div_le_div_of_nonneg_left (sq_nonneg r) (by positivity)
        gcongr
        nlinarith [mul_le_mul_of_nonneg_right hc1 (sq_nonneg r)]
      have he : Real.exp (-(r ^ 2 / (Real.sqrt (a⁻¹ * r ^ 2 + M ^ 2) + M))) ≤
          Real.exp M * Real.exp (-r) := by
        calc
          _ ≤ kernel 1 M (r ^ 2) := by
            unfold kernel
            simp only [neg_one_mul]
            exact Real.exp_le_exp.mpr (neg_le_neg hratio)
          _ ≤ _ := by simpa only [one_mul, neg_one_mul, Real.sqrt_sq hr0.le] using
            kernel_upper (M := M) (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg r)
      rw [Real.norm_of_nonneg (by positivity)]
      calc
        _ ≤ (r ^ (d + 3) * Real.exp (-(r ^ 2 / (Real.sqrt (a⁻¹ * r ^ 2 + M ^ 2) + M)))) / m ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          nlinarith [mul_nonneg hc0 (sq_nonneg r)]
        _ ≤ (r ^ (d + 3) * (Real.exp M * Real.exp (-r))) / m ^ 2 := by gcongr
        _ = _ := by ring)
    (hgi.const_mul (Real.exp M / m ^ 2))
    (Eventually.of_forall (fun r => by
      have hc : ContinuousAt (fun c : ℝ => r ^ (d + 3) *
          Real.exp (-(r ^ 2 / (Real.sqrt (c * r ^ 2 + M ^ 2) + M))) / (c * r ^ 2 + m ^ 2)) 0 := by
        fun_prop (disch := positivity)
      simpa only [zero_mul, zero_add, Real.sqrt_sq hM.le, show M + M = 2 * M by ring] using
        hc.tendsto.comp tendsto_inv_atTop_zero))
  rw [integral_div, radial_gaussian_integral_add_two hd hM] at ht
  have hval : (2 * M) ^ ((d + 4) / 2) * Real.Gamma ((d + 4) / 2) /
      (16 * Real.pi ^ 2 * m ^ 2) = (8 * Real.pi ^ 2)⁻¹ *
        ((2 * M) ^ ((d + 4) / 2) / 2 * Real.Gamma ((d + 4) / 2) / m ^ 2) := by ring
  rw [hval]
  apply (ht.const_mul ((8 * Real.pi ^ 2)⁻¹)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  exact (oneLineComparison_sqrt_scaled (d := d) (m := m) ha hM.le).symm

theorem kernel_hasDerivAt_auxMass (a M : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun N => kernel a N u)
      (a * (1 - M / Real.sqrt (u + M ^ 2)) * kernel a M u) M := by
  have hinner := ((hasDerivAt_id M).pow 2).const_add u
  have hs := hinner.sqrt (show u + (id M) ^ 2 ≠ 0 by positivity)
  have he := ((hs.sub (hasDerivAt_id M)).const_mul (-a)).exp
  convert he using 1
  simp only [id_eq, Pi.pow_apply, Pi.sub_apply, kernel, depthProfile]
  field_simp
  ring

theorem kernel_deriv_auxMass_pos {a M u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    0 < deriv (fun N => kernel a N u) M := by
  rw [(kernel_hasDerivAt_auxMass a M hu).deriv]
  have hs : 0 < Real.sqrt (u + M ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hlt : M < Real.sqrt (u + M ^ 2) := Real.lt_sqrt_of_sq_lt (by linarith)
  have hf : M / Real.sqrt (u + M ^ 2) < 1 := (div_lt_one hs).mpr hlt
  exact mul_pos (mul_pos ha (sub_pos.mpr hf)) (kernel_pos _ _ _)

/-- The complete one-line asymptotic content of `prop:OQED-depth-stability`,
with its exact Fourier constants and its separate strong-depth regimes. -/
theorem oqed_oneLine_depth_asymptotics {d : ℝ} (hd : 0 ≤ d) :
    (∀ M m a, 0 < a → Integrable (oneLineIntegrand d a M m)) ∧
    (∀ M m, 0 ≤ M → 0 ≤ m →
      Tendsto (fun a : ℝ => a ^ (d + 2) * oneLineComparison d a M m) (𝓝[>] 0)
        (𝓝 (Real.Gamma (d + 2) / (8 * Real.pi ^ 2)))) ∧
    (∀ K, 0 ≤ K → ∀ ε > 0, ∃ δ > 0, ∀ a, 0 < a → a < δ → ∀ M m,
      0 ≤ M → M ≤ K → 0 ≤ m → m ≤ K →
      |a ^ (d + 2) * oneLineComparison d a M m - Real.Gamma (d + 2) / (8 * Real.pi ^ 2)| < ε) ∧
    (∀ m, 0 < m →
      Tendsto (fun a : ℝ => a ^ (d + 4) * oneLineComparison d a 0 m) atTop
        (𝓝 (Real.Gamma (d + 4) / (8 * Real.pi ^ 2 * m ^ 2)))) ∧
    (∀ M m, 0 < M → 0 < m →
      Tendsto (fun a : ℝ => a ^ ((d + 4) / 2) * oneLineComparison d a M m) atTop
        (𝓝 ((2 * M) ^ ((d + 4) / 2) * Real.Gamma ((d + 4) / 2) /
          (16 * Real.pi ^ 2 * m ^ 2)))) := by
  exact ⟨(fun M m a ha => oneLineIntegrand_integrable hd ha M m),
    (fun M _ hM _ => oneLineComparison_zero_depth hd hM),
    (fun _ hK => oneLineComparison_zero_depth_uniform_bounded hd hK),
    (fun _ hm => oneLineComparison_strong_depth_zero_auxMass hd hm),
    (fun _ _ hM hm => oneLineComparison_strong_depth_pos_auxMass hd hM hm)⟩

def crossoverH (d μ : ℝ) : ℝ :=
  ∫ r in Ioi 0, r ^ (d + 3) * kernel 1 μ (r ^ 2)

theorem crossoverH_integrable {d : ℝ} (hd : 0 ≤ d) (μ : ℝ) :
    IntegrableOn (fun r => r ^ (d + 3) * kernel 1 μ (r ^ 2)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := 1) (s := d + 3) (b := 1) (by linarith) (by norm_num) (by norm_num)
  simp only [Real.rpow_one, neg_one_mul] at h
  apply (h.const_mul (Real.exp μ)).mono'
  · apply Measurable.aestronglyMeasurable
    unfold kernel depthProfile
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hr.le _) (kernel_pos _ _ _).le)]
    have hk := kernel_upper (M := μ) (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg r)
    simp only [one_mul, neg_one_mul, Real.sqrt_sq hr.le] at hk
    calc
      _ ≤ r ^ (d + 3) * (Real.exp μ * Real.exp (-r)) := by gcongr
      _ = _ := by ring

theorem crossoverH_zero {d : ℝ} (hd : 0 ≤ d) : crossoverH d 0 = Real.Gamma (d + 4) := by
  unfold crossoverH
  rw [← radial_exponential_integral_add_two hd]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  simp [kernel, depthProfile, Real.sqrt_sq hr.le]

def crossoverLineIntegrand (d μ m a r : ℝ) : ℝ :=
  r ^ (d + 3) * kernel 1 μ (r ^ 2) / ((a⁻¹ * r) ^ 2 + m ^ 2)

theorem crossoverLineIntegrand_integrable {d m : ℝ} (hd : 0 ≤ d) (hm : 0 < m) (μ a : ℝ) :
    IntegrableOn (crossoverLineIntegrand d μ m a) (Ioi 0) := by
  apply ((crossoverH_integrable hd μ).div_const (m ^ 2)).mono'
  · apply Measurable.aestronglyMeasurable
    unfold crossoverLineIntegrand kernel depthProfile
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    unfold crossoverLineIntegrand
    rw [Real.norm_of_nonneg (div_nonneg
      (mul_nonneg (Real.rpow_nonneg hr.le _) (kernel_pos _ _ _).le) (by positivity))]
    apply div_le_div_of_nonneg_left
      (mul_nonneg (Real.rpow_nonneg hr.le _) (kernel_pos _ _ _).le) (by positivity)
    nlinarith [sq_nonneg (a⁻¹ * r)]

theorem oneLineComparison_crossover_scaled {d a μ m : ℝ} (ha : 0 < a) :
    a ^ (d + 4) * oneLineComparison d a (μ / a) m =
      (8 * Real.pi ^ 2)⁻¹ * ∫ r in Ioi 0, crossoverLineIntegrand d μ m a r := by
  rw [oneLineComparison_scaled_radial d a (μ / a) m ha]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  dsimp only
  rw [kernel_scale_input ha, div_self ha.ne']
  have he : a * (μ / a) = μ := by field_simp
  rw [he]
  rfl

theorem oneLineComparison_controlled_crossover {d m : ℝ} (hd : 0 ≤ d) (hm : 0 < m) (μ : ℝ) :
    Tendsto (fun a : ℝ => a ^ (d + 4) * oneLineComparison d a (μ / a) m) atTop
      (𝓝 (crossoverH d μ / (8 * Real.pi ^ 2 * m ^ 2))) := by
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun a r => crossoverLineIntegrand d μ m a r)
    (f := fun r => r ^ (d + 3) * kernel 1 μ (r ^ 2) / m ^ 2)
    (l := atTop) (fun r => (r ^ (d + 3) * kernel 1 μ (r ^ 2)) / m ^ 2)
    (Eventually.of_forall (fun a => (crossoverLineIntegrand_integrable hd hm μ a).aestronglyMeasurable))
    (Eventually.of_forall (fun a => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      unfold crossoverLineIntegrand
      rw [Real.norm_of_nonneg (div_nonneg
        (mul_nonneg (Real.rpow_nonneg hr.le _) (kernel_pos _ _ _).le) (by positivity))]
      apply div_le_div_of_nonneg_left
        (mul_nonneg (Real.rpow_nonneg hr.le _) (kernel_pos _ _ _).le) (by positivity)
      nlinarith [sq_nonneg (a⁻¹ * r)]))
    ((crossoverH_integrable hd μ).div_const (m ^ 2))
    (Eventually.of_forall (fun r => by
      have hc : ContinuousAt (fun c : ℝ => r ^ (d + 3) * kernel 1 μ (r ^ 2) /
          ((c * r) ^ 2 + m ^ 2)) 0 := by fun_prop (disch := positivity)
      simpa [crossoverLineIntegrand] using hc.tendsto.comp tendsto_inv_atTop_zero))
  rw [integral_div] at ht
  change Tendsto _ _ (𝓝 (crossoverH d μ / m ^ 2)) at ht
  have hval : crossoverH d μ / (8 * Real.pi ^ 2 * m ^ 2) =
      (8 * Real.pi ^ 2)⁻¹ * (crossoverH d μ / m ^ 2) := by ring
  rw [hval]
  apply (ht.const_mul ((8 * Real.pi ^ 2)⁻¹)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  exact (oneLineComparison_crossover_scaled ha).symm

theorem reciprocal_mass_difference_bound {x m : ℝ} (hx : 0 ≤ x) (hm : 0 < m) :
    0 ≤ 1 / m ^ 2 - 1 / (x + m ^ 2) ∧
      1 / m ^ 2 - 1 / (x + m ^ 2) ≤ x / m ^ 4 := by
  have he : 1 / m ^ 2 - 1 / (x + m ^ 2) = x / (m ^ 2 * (x + m ^ 2)) := by
    field_simp
    ring
  rw [he]
  constructor
  · positivity
  · apply div_le_div_of_nonneg_left hx (by positivity)
    nlinarith [mul_nonneg (sq_nonneg m) hx]

/-- A quantitative estimate supplies uniform crossover on every compact
nonnegative auxiliary-mass interval. -/
theorem oneLineComparison_crossover_error {d a μ K m : ℝ}
    (hd : 0 ≤ d) (ha : 0 < a) (hμ : 0 ≤ μ) (hμK : μ ≤ K) (hm : 0 < m) :
    0 ≤ crossoverH d μ / (8 * Real.pi ^ 2 * m ^ 2) -
        a ^ (d + 4) * oneLineComparison d a (μ / a) m ∧
    crossoverH d μ / (8 * Real.pi ^ 2 * m ^ 2) -
        a ^ (d + 4) * oneLineComparison d a (μ / a) m ≤
      (a⁻¹) ^ 2 * Real.exp K * Real.Gamma (d + 6) / (8 * Real.pi ^ 2 * m ^ 4) := by
  let f := fun r => r ^ (d + 3) * kernel 1 μ (r ^ 2) / m ^ 2 - crossoverLineIntegrand d μ m a r
  have hf : IntegrableOn f (Ioi 0) :=
    ((crossoverH_integrable hd μ).div_const (m ^ 2)).sub (crossoverLineIntegrand_integrable hd hm μ a)
  have hnonneg : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ f r := by
    intro r hr
    have hN : 0 ≤ r ^ (d + 3) * kernel 1 μ (r ^ 2) :=
      mul_nonneg (Real.rpow_nonneg hr.le _) (kernel_pos _ _ _).le
    dsimp [f, crossoverLineIntegrand]
    apply sub_nonneg.mpr
    apply div_le_div_of_nonneg_left hN (by positivity)
    nlinarith [sq_nonneg (a⁻¹ * r)]
  have hpoint : ∀ r ∈ Ioi (0 : ℝ), f r ≤
      ((a⁻¹) ^ 2 * Real.exp K / m ^ 4) * (r ^ (d + 5) * Real.exp (-r)) := by
    intro r hr
    have hr0 : 0 < r := hr
    have hN : 0 ≤ r ^ (d + 3) * kernel 1 μ (r ^ 2) :=
      mul_nonneg (Real.rpow_nonneg hr.le _) (kernel_pos _ _ _).le
    have hb := (reciprocal_mass_difference_bound (sq_nonneg (a⁻¹ * r)) hm).2
    have hk : kernel 1 μ (r ^ 2) ≤ Real.exp K * Real.exp (-r) := by
      have hk := kernel_upper (M := K) (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg r)
      simp only [one_mul, neg_one_mul, Real.sqrt_sq hr.le] at hk
      exact (kernel_monotone_mass (by norm_num) hμ hμK (sq_nonneg r)).trans hk
    have hp : r ^ (d + 3) * r ^ 2 = r ^ (d + 5) := by
      rw [← Real.rpow_natCast r 2, ← Real.rpow_add hr0]
      congr 1
      norm_num
      ring
    calc
      f r = (r ^ (d + 3) * kernel 1 μ (r ^ 2)) *
          (1 / m ^ 2 - 1 / ((a⁻¹ * r) ^ 2 + m ^ 2)) := by dsimp [f, crossoverLineIntegrand]; ring
      _ ≤ (r ^ (d + 3) * kernel 1 μ (r ^ 2)) * ((a⁻¹ * r) ^ 2 / m ^ 4) :=
        mul_le_mul_of_nonneg_left hb hN
      _ ≤ (r ^ (d + 3) * (Real.exp K * Real.exp (-r))) * ((a⁻¹ * r) ^ 2 / m ^ 4) := by gcongr
      _ = ((a⁻¹) ^ 2 * Real.exp K / m ^ 4) * ((r ^ (d + 3) * r ^ 2) * Real.exp (-r)) := by ring
      _ = _ := by rw [hp]
  have hi : crossoverH d μ / (8 * Real.pi ^ 2 * m ^ 2) -
      a ^ (d + 4) * oneLineComparison d a (μ / a) m = (8 * Real.pi ^ 2)⁻¹ * ∫ r in Ioi 0, f r := by
    rw [oneLineComparison_crossover_scaled ha,
      integral_sub ((crossoverH_integrable hd μ).div_const (m ^ 2)) (crossoverLineIntegrand_integrable hd hm μ a),
      integral_div]
    dsimp [crossoverH]
    ring
  rw [hi]
  constructor
  · exact mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi hnonneg)
  · have hgi := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := d + 5) (b := 1) (by linarith) (by norm_num) (by norm_num)
    simp only [Real.rpow_one, neg_one_mul] at hgi
    have hib := integral_mono_ae hf (hgi.const_mul ((a⁻¹) ^ 2 * Real.exp K / m ^ 4))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hpoint))
    rw [integral_const_mul] at hib
    have hgval : (∫ r in Ioi 0, r ^ (d + 5) * Real.exp (-r)) = Real.Gamma (d + 6) := by
      simpa only [show d + 2 + 3 = d + 5 by ring, show d + 2 + 4 = d + 6 by ring] using
        radial_exponential_integral_add_two (d := d + 2) (by linarith)
    rw [hgval] at hib
    calc
      _ ≤ (8 * Real.pi ^ 2)⁻¹ * (((a⁻¹) ^ 2 * Real.exp K / m ^ 4) * Real.Gamma (d + 6)) :=
        mul_le_mul_of_nonneg_left hib (by positivity)
      _ = _ := by ring

theorem oneLineComparison_controlled_crossover_uniform {d K m : ℝ}
    (hd : 0 ≤ d) (hm : 0 < m) :
    ∀ ε > 0, ∃ A > 0, ∀ a, A < a → ∀ μ, 0 ≤ μ → μ ≤ K →
      |a ^ (d + 4) * oneLineComparison d a (μ / a) m -
        crossoverH d μ / (8 * Real.pi ^ 2 * m ^ 2)| < ε := by
  intro ε hε
  have ht : Tendsto (fun a : ℝ => (a⁻¹) ^ 2 * Real.exp K * Real.Gamma (d + 6) /
      (8 * Real.pi ^ 2 * m ^ 4)) atTop (𝓝 0) := by
    have hi : Tendsto (fun a : ℝ => a⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa using ((((hi.pow 2).mul_const (Real.exp K)).mul_const (Real.Gamma (d + 6))).div_const
      (8 * Real.pi ^ 2 * m ^ 4))
  obtain ⟨A, hA⟩ := eventually_atTop.mp (ht.eventually (eventually_lt_nhds hε))
  refine ⟨max A 1, lt_of_lt_of_le zero_lt_one (le_max_right A 1), fun a ha μ hμ hμK => ?_⟩
  have ha0 : 0 < a := lt_trans (lt_of_lt_of_le zero_lt_one (le_max_right A 1)) ha
  have hb := hA a ((le_max_left A 1).trans ha.le)
  have he := oneLineComparison_crossover_error hd ha0 hμ hμK hm
  rw [abs_sub_comm, abs_of_nonneg he.1]
  exact he.2.trans_lt hb

theorem fourier_radial_integral (f : ℝ → ℝ) :
    (2 * Real.pi) ^ (-4 : ℤ) * (∫ q : ScalarMomentum, f ‖q‖) =
      (8 * Real.pi ^ 2)⁻¹ * ∫ r in Ioi 0, r ^ 3 * f r := by
  rw [integral_fun_norm_addHaar (E := ScalarMomentum) volume f]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, nsmul_eq_mul, smul_eq_mul]
  rw [fourDimensional_unitBall_volume, zpow_neg, zpow_ofNat]
  field_simp
  ring

theorem scalarBubble_zero_transfer_radial (a M m : ℝ) :
    scalarBubble a M m 0 = (8 * Real.pi ^ 2)⁻¹ *
      ∫ r in Ioi 0, r ^ 3 * kernel a M (r ^ 2) ^ 2 / (r ^ 2 + m ^ 2) ^ 2 := by
  unfold scalarBubble scalarBubbleIntegrand scalarCovariance
  simp only [add_zero]
  simp_rw [← pow_two]
  rw [fourier_radial_integral (fun r => (kernel a M (r ^ 2) / (r ^ 2 + m ^ 2)) ^ 2)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  dsimp only
  rw [div_pow]
  ring

def crossoverBubbleH (μ : ℝ) : ℝ :=
  ∫ r in Ioi 0, r ^ 3 * kernel 1 μ (r ^ 2) ^ 2

theorem crossoverBubbleH_integrable {μ : ℝ} (hμ : 0 ≤ μ) :
    IntegrableOn (fun r => r ^ 3 * kernel 1 μ (r ^ 2) ^ 2) (Ioi 0) := by
  have h : IntegrableOn (fun r => r ^ 3 * kernel 1 μ (r ^ 2)) (Ioi 0) := by
    simpa only [zero_add, Real.rpow_ofNat] using crossoverH_integrable (d := 0) (by norm_num) μ
  apply h.mono'
  · apply Measurable.aestronglyMeasurable
    unfold kernel depthProfile
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hr.le _) (sq_nonneg _))]
    have hk := kernel_le_one (by norm_num : (0 : ℝ) ≤ 1) hμ (sq_nonneg r)
    have hk0 := kernel_pos 1 μ (r ^ 2)
    exact mul_le_mul_of_nonneg_left (by nlinarith : kernel 1 μ (r ^ 2) ^ 2 ≤ kernel 1 μ (r ^ 2))
      (pow_nonneg hr.le _)

def crossoverBubbleIntegrand (μ m a r : ℝ) : ℝ :=
  r ^ 3 * kernel 1 μ (r ^ 2) ^ 2 / ((a⁻¹ * r) ^ 2 + m ^ 2) ^ 2

theorem crossoverBubbleIntegrand_integrable {μ m : ℝ} (hμ : 0 ≤ μ) (hm : 0 < m) (a : ℝ) :
    IntegrableOn (crossoverBubbleIntegrand μ m a) (Ioi 0) := by
  apply ((crossoverBubbleH_integrable hμ).div_const (m ^ 4)).mono'
  · apply Measurable.aestronglyMeasurable
    unfold crossoverBubbleIntegrand kernel depthProfile
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    unfold crossoverBubbleIntegrand
    rw [Real.norm_of_nonneg (div_nonneg
      (mul_nonneg (pow_nonneg hr.le _) (sq_nonneg _)) (sq_nonneg _))]
    apply div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg hr.le _) (sq_nonneg _)) (by positivity)
    nlinarith [sq_nonneg ((a⁻¹ * r) ^ 2), mul_nonneg (sq_nonneg (a⁻¹ * r)) (sq_nonneg m)]

theorem scalarBubble_crossover_scaled {a μ m : ℝ} (ha : 0 < a) :
    a ^ 4 * scalarBubble a (μ / a) m 0 =
      (8 * Real.pi ^ 2)⁻¹ * ∫ r in Ioi 0, crossoverBubbleIntegrand μ m a r := by
  rw [scalarBubble_zero_transfer_radial]
  have hs := radial_integral_scale 0 ha
    (fun r => kernel a (μ / a) (r ^ 2) ^ 2 / (r ^ 2 + m ^ 2) ^ 2)
  simp only [zero_add, Real.rpow_ofNat, ← mul_div_assoc] at hs
  calc
    _ = (8 * Real.pi ^ 2)⁻¹ *
        (a ^ 4 * ∫ r in Ioi 0, r ^ 3 * kernel a (μ / a) (r ^ 2) ^ 2 / (r ^ 2 + m ^ 2) ^ 2) := by ring
    _ = (8 * Real.pi ^ 2)⁻¹ * ∫ r in Ioi 0,
        r ^ 3 * kernel a (μ / a) ((a⁻¹ * r) ^ 2) ^ 2 / ((a⁻¹ * r) ^ 2 + m ^ 2) ^ 2 := by rw [hs]
    _ = _ := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r _
      dsimp only [crossoverBubbleIntegrand]
      rw [kernel_scale_input ha, div_self ha.ne']
      have he : a * (μ / a) = μ := by field_simp
      rw [he]

theorem scalarBubble_controlled_crossover_raw {μ m : ℝ} (hμ : 0 ≤ μ) (hm : 0 < m) :
    Tendsto (fun a : ℝ => a ^ 4 * scalarBubble a (μ / a) m 0) atTop
      (𝓝 (crossoverBubbleH μ / (8 * Real.pi ^ 2 * m ^ 4))) := by
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun a r => crossoverBubbleIntegrand μ m a r)
    (f := fun r => r ^ 3 * kernel 1 μ (r ^ 2) ^ 2 / m ^ 4)
    (l := atTop) (fun r => (r ^ 3 * kernel 1 μ (r ^ 2) ^ 2) / m ^ 4)
    (Eventually.of_forall (fun a => (crossoverBubbleIntegrand_integrable hμ hm a).aestronglyMeasurable))
    (Eventually.of_forall (fun a => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      unfold crossoverBubbleIntegrand
      rw [Real.norm_of_nonneg (div_nonneg
        (mul_nonneg (pow_nonneg hr.le _) (sq_nonneg _)) (sq_nonneg _))]
      apply div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg hr.le _) (sq_nonneg _)) (by positivity)
      nlinarith [sq_nonneg ((a⁻¹ * r) ^ 2), mul_nonneg (sq_nonneg (a⁻¹ * r)) (sq_nonneg m)]))
    ((crossoverBubbleH_integrable hμ).div_const (m ^ 4))
    (Eventually.of_forall (fun r => by
      have hc : ContinuousAt (fun c : ℝ => r ^ 3 * kernel 1 μ (r ^ 2) ^ 2 /
          ((c * r) ^ 2 + m ^ 2) ^ 2) 0 := by fun_prop (disch := positivity)
      simpa [crossoverBubbleIntegrand, ← pow_mul] using hc.tendsto.comp tendsto_inv_atTop_zero))
  rw [integral_div] at ht
  change Tendsto _ _ (𝓝 (crossoverBubbleH μ / m ^ 4)) at ht
  have hval : crossoverBubbleH μ / (8 * Real.pi ^ 2 * m ^ 4) =
      (8 * Real.pi ^ 2)⁻¹ * (crossoverBubbleH μ / m ^ 4) := by ring
  rw [hval]
  apply (ht.const_mul ((8 * Real.pi ^ 2)⁻¹)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  exact (scalarBubble_crossover_scaled ha).symm

theorem crossoverBubbleH_eq_scaled_H0 (μ : ℝ) : crossoverBubbleH μ = crossoverH 0 (2 * μ) / 16 := by
  have hs := radial_integral_scale 0 (by norm_num : (0 : ℝ) < 2)
    (fun r => kernel 1 μ (r ^ 2) ^ 2)
  simp only [zero_add, Real.rpow_ofNat] at hs
  have hk : ∀ r : ℝ, kernel 1 μ (((2 : ℝ)⁻¹ * r) ^ 2) ^ 2 = kernel 1 (2 * μ) (r ^ 2) := by
    intro r
    rw [kernel_scale_input (by norm_num : (0 : ℝ) < 2)]
    unfold kernel
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hi : (∫ v in Ioi 0, v ^ 3 * kernel 1 μ (((2 : ℝ)⁻¹ * v) ^ 2) ^ 2) = crossoverH 0 (2 * μ) := by
    simp only [hk, crossoverH, zero_add, Real.rpow_ofNat]
  rw [hi] at hs
  change (2 : ℝ) ^ 4 * crossoverBubbleH μ = crossoverH 0 (2 * μ) at hs
  norm_num at hs
  apply (eq_div_iff (by norm_num : (16 : ℝ) ≠ 0)).mpr
  linarith


def crossoverQuadraticShift (μ t : ℝ) : ℝ := t ^ 2 + 2 * μ * t

theorem crossoverQuadraticShift_strictMono {μ : ℝ} (hμ : 0 ≤ μ) : StrictMonoOn (crossoverQuadraticShift μ) (Ioi 0) := by
  intro x hx y hy hxy
  have hh := mul_pos (sub_pos.mpr hxy) (add_pos hy hx)
  have hm := mul_nonneg hμ (sub_pos.mpr hxy).le
  unfold crossoverQuadraticShift
  nlinarith

theorem crossoverQuadraticShift_image {μ : ℝ} (hμ : 0 ≤ μ) : crossoverQuadraticShift μ '' Ioi 0 = Ioi 0 := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    change 0 < t ^ 2 + 2 * μ * t
    have ht0 : 0 < t := ht
    have hm := mul_nonneg hμ ht0.le
    have ht2 := sq_pos_of_pos ht0
    nlinarith
  · intro hu
    have hu0 : 0 < u := hu
    have hs := Real.sq_sqrt (show 0 ≤ u + μ ^ 2 by positivity)
    have hp : μ < Real.sqrt (u + μ ^ 2) := (Real.lt_sqrt hμ).mpr (by linarith)
    refine ⟨Real.sqrt (u + μ ^ 2) - μ, sub_pos.mpr hp, ?_⟩
    unfold crossoverQuadraticShift
    nlinarith

theorem crossoverQuadraticShift_hasDerivAt (μ t : ℝ) : HasDerivAt (crossoverQuadraticShift μ) (2 * (t + μ)) t := by
  convert ((hasDerivAt_id t).pow 2).add ((hasDerivAt_id t).const_mul (2 * μ)) using 1
  simp only [id_eq]
  ring

theorem kernel_crossoverQuadraticShift {μ t : ℝ} (hμ : 0 ≤ μ) (ht : 0 < t) :
    kernel 1 μ (crossoverQuadraticShift μ t) = Real.exp (-t) := by
  unfold kernel depthProfile crossoverQuadraticShift
  rw [show t ^ 2 + 2 * μ * t + μ ^ 2 = (t + μ) ^ 2 by ring,
    Real.sqrt_sq (by linarith : 0 ≤ t + μ)]
  congr 1
  ring

theorem crossoverNatExpIntegrable (n : ℕ) : IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-t)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n : ℝ)) (b := 1)
    (by have hh := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) (by norm_num)
  simpa only [Real.rpow_one, Real.rpow_natCast, neg_one_mul] using h

theorem crossoverNatExpIntegral (n : ℕ) : (∫ t : ℝ in Ioi 0, t ^ n * Real.exp (-t)) = (n.factorial : ℝ) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := (n : ℝ)) (b := 1)
    (by norm_num) (by have hh := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num)
  simpa [Real.Gamma_nat_eq_factorial, Real.rpow_natCast] using h

theorem crossoverPolynomialExpIntegral (μ : ℝ) :
    (∫ t : ℝ in Ioi 0, (t ^ 3 * Real.exp (-t) + (3 * μ) * (t ^ 2 * Real.exp (-t))) +
      (2 * μ ^ 2) * (t * Real.exp (-t))) = 6 + 6 * μ + 2 * μ ^ 2 := by
  have h1 : IntegrableOn (fun t : ℝ => t * Real.exp (-t)) (Ioi 0) := by
    simpa only [pow_one] using crossoverNatExpIntegrable 1
  have hi1 : (∫ t : ℝ in Ioi 0, t * Real.exp (-t)) = 1 := by
    simpa using crossoverNatExpIntegral 1
  have hs1 : (∫ t : ℝ in Ioi 0, (t ^ 3 * Real.exp (-t) + (3 * μ) * (t ^ 2 * Real.exp (-t))) +
      (2 * μ ^ 2) * (t * Real.exp (-t))) =
      (∫ t : ℝ in Ioi 0, t ^ 3 * Real.exp (-t) + (3 * μ) * (t ^ 2 * Real.exp (-t))) +
      (∫ t : ℝ in Ioi 0, (2 * μ ^ 2) * (t * Real.exp (-t))) :=
    integral_add ((crossoverNatExpIntegrable 3).add ((crossoverNatExpIntegrable 2).const_mul (3 * μ)))
      (h1.const_mul (2 * μ ^ 2))
  have hs2 : (∫ t : ℝ in Ioi 0, t ^ 3 * Real.exp (-t) + (3 * μ) * (t ^ 2 * Real.exp (-t))) =
      (∫ t : ℝ in Ioi 0, t ^ 3 * Real.exp (-t)) +
      (∫ t : ℝ in Ioi 0, (3 * μ) * (t ^ 2 * Real.exp (-t))) :=
    integral_add (crossoverNatExpIntegrable 3) ((crossoverNatExpIntegrable 2).const_mul (3 * μ))
  have hc2 : (∫ t : ℝ in Ioi 0, (3 * μ) * (t ^ 2 * Real.exp (-t))) =
      (3 * μ) * (∫ t : ℝ in Ioi 0, t ^ 2 * Real.exp (-t)) := integral_const_mul _ _
  have hc1 : (∫ t : ℝ in Ioi 0, (2 * μ ^ 2) * (t * Real.exp (-t))) =
      (2 * μ ^ 2) * (∫ t : ℝ in Ioi 0, t * Real.exp (-t)) := integral_const_mul _ _
  rw [hs1, hs2, hc1, hc2, crossoverNatExpIntegral 3, crossoverNatExpIntegral 2, hi1]
  norm_num
  ring

theorem crossoverH0_exact {μ : ℝ} (hμ : 0 ≤ μ) :
    (∫ r : ℝ in Ioi 0, r ^ 3 * kernel 1 μ (r ^ 2)) = 6 + 6 * μ + 2 * μ ^ 2 := by
  let G := fun u : ℝ => u / 2 * kernel 1 μ u
  have hsq : (∫ r : ℝ in Ioi 0, r ^ 3 * kernel 1 μ (r ^ 2)) = ∫ u in Ioi 0, G u := by
    have hh := integral_comp_rpow_Ioi G (p := 2) (by norm_num)
    calc
      _ = ∫ r in Ioi 0, (|(2 : ℝ)| * r ^ ((2 : ℝ) - 1)) • G (r ^ (2 : ℝ)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r _
        dsimp [G]
        norm_num
        ring
      _ = _ := hh
  have hj := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t _ => (crossoverQuadraticShift_hasDerivAt μ t).hasDerivWithinAt) (crossoverQuadraticShift_strictMono hμ).injOn G
  rw [crossoverQuadraticShift_image hμ] at hj
  calc
    _ = ∫ u in Ioi 0, G u := hsq
    _ = ∫ t in Ioi 0, |2 * (t + μ)| • G (crossoverQuadraticShift μ t) := hj
    _ = ∫ t in Ioi 0, (t ^ 3 * Real.exp (-t) + (3 * μ) * (t ^ 2 * Real.exp (-t))) +
        (2 * μ ^ 2) * (t * Real.exp (-t)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only [G]
      rw [abs_of_pos (by have ht0 : 0 < t := ht; positivity), kernel_crossoverQuadraticShift hμ ht]
      unfold crossoverQuadraticShift
      simp only [smul_eq_mul]
      ring
    _ = _ := crossoverPolynomialExpIntegral μ

theorem crossoverH_zero_degree {μ : ℝ} (hμ : 0 ≤ μ) :
    crossoverH 0 μ = 6 + 6 * μ + 2 * μ ^ 2 := by
  simpa only [crossoverH, zero_add, Real.rpow_ofNat] using crossoverH0_exact hμ

theorem crossoverBubbleH_exact {μ : ℝ} (hμ : 0 ≤ μ) :
    crossoverBubbleH μ = (3 + 6 * μ + 4 * μ ^ 2) / 8 := by
  rw [crossoverBubbleH_eq_scaled_H0, crossoverH_zero_degree (by positivity : 0 ≤ 2 * μ)]
  ring

theorem scalarBubble_controlled_crossover {μ m : ℝ} (hμ : 0 ≤ μ) (hm : 0 < m) :
    Tendsto (fun a : ℝ => a ^ 4 * scalarBubble a (μ / a) m 0) atTop
      (𝓝 ((3 + 6 * μ + 4 * μ ^ 2) / (64 * Real.pi ^ 2 * m ^ 4))) := by
  have he : crossoverBubbleH μ / (8 * Real.pi ^ 2 * m ^ 4) =
      (3 + 6 * μ + 4 * μ ^ 2) / (64 * Real.pi ^ 2 * m ^ 4) := by
    rw [crossoverBubbleH_exact hμ]
    ring
  simpa only [he] using scalarBubble_controlled_crossover_raw hμ hm

theorem reciprocal_squared_mass_difference_bound {x m : ℝ} (hx : 0 ≤ x) (hm : 0 < m) :
    0 ≤ 1 / m ^ 4 - 1 / (x + m ^ 2) ^ 2 ∧
      1 / m ^ 4 - 1 / (x + m ^ 2) ^ 2 ≤ 2 * x / m ^ 6 := by
  have hd := reciprocal_mass_difference_bound hx hm
  have he : 1 / m ^ 4 - 1 / (x + m ^ 2) ^ 2 =
      (1 / m ^ 2 - 1 / (x + m ^ 2)) * (1 / m ^ 2 + 1 / (x + m ^ 2)) := by
    field_simp
    ring
  have hs0 : 0 ≤ 1 / m ^ 2 + 1 / (x + m ^ 2) := by positivity
  have hs : 1 / m ^ 2 + 1 / (x + m ^ 2) ≤ 2 / m ^ 2 := by
    calc
      _ ≤ 1 / m ^ 2 + 1 / m ^ 2 := add_le_add_left (sub_nonneg.mp hd.1) _
      _ = _ := by ring
  rw [he]
  constructor
  · exact mul_nonneg hd.1 hs0
  · calc
      _ ≤ (x / m ^ 4) * (1 / m ^ 2 + 1 / (x + m ^ 2)) := mul_le_mul_of_nonneg_right hd.2 hs0
      _ ≤ (x / m ^ 4) * (2 / m ^ 2) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by field_simp

theorem scalarBubble_crossover_error {a μ K m : ℝ}
    (ha : 0 < a) (hμ : 0 ≤ μ) (hμK : μ ≤ K) (hm : 0 < m) :
    0 ≤ crossoverBubbleH μ / (8 * Real.pi ^ 2 * m ^ 4) -
        a ^ 4 * scalarBubble a (μ / a) m 0 ∧
    crossoverBubbleH μ / (8 * Real.pi ^ 2 * m ^ 4) -
        a ^ 4 * scalarBubble a (μ / a) m 0 ≤
      (30 * Real.exp K / (Real.pi ^ 2 * m ^ 6)) * (a⁻¹) ^ 2 := by
  let f := fun r => r ^ 3 * kernel 1 μ (r ^ 2) ^ 2 / m ^ 4 - crossoverBubbleIntegrand μ m a r
  have hf : IntegrableOn f (Ioi 0) :=
    ((crossoverBubbleH_integrable hμ).div_const (m ^ 4)).sub (crossoverBubbleIntegrand_integrable hμ hm a)
  have hnonneg : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ f r := by
    intro r hr
    dsimp [f, crossoverBubbleIntegrand]
    apply sub_nonneg.mpr
    apply div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg hr.le _) (sq_nonneg _)) (by positivity)
    nlinarith [sq_nonneg ((a⁻¹ * r) ^ 2), mul_nonneg (sq_nonneg (a⁻¹ * r)) (sq_nonneg m)]
  have hpoint : ∀ r ∈ Ioi (0 : ℝ), f r ≤
      ((a⁻¹) ^ 2 * 2 * Real.exp K / m ^ 6) * (r ^ 5 * Real.exp (-r)) := by
    intro r hr
    have hN : 0 ≤ r ^ 3 * kernel 1 μ (r ^ 2) ^ 2 := mul_nonneg (pow_nonneg hr.le _) (sq_nonneg _)
    have hb := (reciprocal_squared_mass_difference_bound (sq_nonneg (a⁻¹ * r)) hm).2
    have hk : kernel 1 μ (r ^ 2) ^ 2 ≤ Real.exp K * Real.exp (-r) := by
      have hk0 := kernel_pos 1 μ (r ^ 2)
      have hk1 := kernel_le_one (by norm_num : (0 : ℝ) ≤ 1) hμ (sq_nonneg r)
      have hsq : kernel 1 μ (r ^ 2) ^ 2 ≤ kernel 1 μ (r ^ 2) := by nlinarith
      have hk := kernel_upper (M := K) (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg r)
      simp only [one_mul, neg_one_mul, Real.sqrt_sq hr.le] at hk
      exact hsq.trans ((kernel_monotone_mass (by norm_num) hμ hμK (sq_nonneg r)).trans hk)
    calc
      f r = (r ^ 3 * kernel 1 μ (r ^ 2) ^ 2) *
          (1 / m ^ 4 - 1 / ((a⁻¹ * r) ^ 2 + m ^ 2) ^ 2) := by dsimp [f, crossoverBubbleIntegrand]; ring
      _ ≤ (r ^ 3 * kernel 1 μ (r ^ 2) ^ 2) * (2 * (a⁻¹ * r) ^ 2 / m ^ 6) :=
        mul_le_mul_of_nonneg_left hb hN
      _ ≤ (r ^ 3 * (Real.exp K * Real.exp (-r))) * (2 * (a⁻¹ * r) ^ 2 / m ^ 6) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (pow_nonneg hr.le _)) (by positivity)
      _ = _ := by ring
  have hi : crossoverBubbleH μ / (8 * Real.pi ^ 2 * m ^ 4) - a ^ 4 * scalarBubble a (μ / a) m 0 =
      (8 * Real.pi ^ 2)⁻¹ * ∫ r in Ioi 0, f r := by
    rw [scalarBubble_crossover_scaled ha,
      integral_sub ((crossoverBubbleH_integrable hμ).div_const (m ^ 4)) (crossoverBubbleIntegrand_integrable hμ hm a),
      integral_div]
    dsimp [crossoverBubbleH]
    ring
  rw [hi]
  constructor
  · exact mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi hnonneg)
  · have hib := integral_mono_ae hf
      ((crossoverNatExpIntegrable 5).const_mul ((a⁻¹) ^ 2 * 2 * Real.exp K / m ^ 6))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hpoint))
    rw [integral_const_mul, crossoverNatExpIntegral 5] at hib
    norm_num only [Nat.factorial] at hib
    calc
      _ ≤ (8 * Real.pi ^ 2)⁻¹ * (((a⁻¹) ^ 2 * 2 * Real.exp K / m ^ 6) * 120) :=
        mul_le_mul_of_nonneg_left hib (by positivity)
      _ = _ := by ring

theorem scalarBubble_controlled_crossover_uniform {K m : ℝ} (hm : 0 < m) :
    ∀ ε > 0, ∃ A > 0, ∀ a, A < a → ∀ μ, 0 ≤ μ → μ ≤ K →
      |a ^ 4 * scalarBubble a (μ / a) m 0 -
        (3 + 6 * μ + 4 * μ ^ 2) / (64 * Real.pi ^ 2 * m ^ 4)| < ε := by
  intro ε hε
  have ht : Tendsto (fun a : ℝ => (30 * Real.exp K / (Real.pi ^ 2 * m ^ 6)) * (a⁻¹) ^ 2)
      atTop (𝓝 0) := by
    have hi : Tendsto (fun a : ℝ => a⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa using (hi.pow 2).const_mul (30 * Real.exp K / (Real.pi ^ 2 * m ^ 6))
  obtain ⟨A, hA⟩ := eventually_atTop.mp (ht.eventually (eventually_lt_nhds hε))
  refine ⟨max A 1, lt_of_lt_of_le zero_lt_one (le_max_right A 1), fun a ha μ hμ hμK => ?_⟩
  have ha0 : 0 < a := lt_trans (lt_of_lt_of_le zero_lt_one (le_max_right A 1)) ha
  have hb := hA a ((le_max_left A 1).trans ha.le)
  have he := scalarBubble_crossover_error ha0 hμ hμK hm
  have hv : crossoverBubbleH μ / (8 * Real.pi ^ 2 * m ^ 4) =
      (3 + 6 * μ + 4 * μ ^ 2) / (64 * Real.pi ^ 2 * m ^ 4) := by rw [crossoverBubbleH_exact hμ]; ring
  rw [hv] at he
  rw [abs_sub_comm, abs_of_nonneg he.1]
  exact he.2.trans_lt hb


theorem largeMass_kernel_rescaled {μ r : ℝ} (hμ : 0 < μ) (hr : 0 < r) :
    kernel 1 μ ((Real.sqrt (2 * μ) * r) ^ 2) =
      Real.exp (-(2 * r ^ 2 / (Real.sqrt (1 + 2 * r ^ 2 * μ⁻¹) + 1))) := by
  have hinput : (Real.sqrt (2 * μ) * r) ^ 2 = 2 * μ * r ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hroot : Real.sqrt (2 * μ * r ^ 2 + μ ^ 2) =
      μ * Real.sqrt (1 + 2 * r ^ 2 * μ⁻¹) := by
    rw [show 2 * μ * r ^ 2 + μ ^ 2 = μ ^ 2 * (1 + 2 * r ^ 2 * μ⁻¹) by field_simp; ring,
      Real.sqrt_mul (sq_nonneg μ), Real.sqrt_sq hμ.le]
  rw [hinput]
  unfold kernel
  rw [depthProfile_eq_div hμ.le (by positivity : 0 < 2 * μ * r ^ 2), hroot]
  congr 1
  field_simp

theorem largeMass_scaled_radial (d : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    (2 * μ) ^ (-((d + 4) / 2)) * (∫ r in Ioi 0, r ^ (d + 3) * kernel 1 μ (r ^ 2)) =
      ∫ r in Ioi 0, r ^ (d + 3) *
        Real.exp (-(2 * r ^ 2 / (Real.sqrt (1 + 2 * r ^ 2 * μ⁻¹) + 1))) := by
  have hs : 0 < (Real.sqrt (2 * μ))⁻¹ := by positivity
  have h := radial_integral_scale d hs (fun r => kernel 1 μ (r ^ 2))
  have hp : (Real.sqrt (2 * μ))⁻¹ ^ (d + 4) = (2 * μ) ^ (-((d + 4) / 2)) := by
    rw [← Real.rpow_neg_eq_inv_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : 0 ≤ 2 * μ)]
    congr 1
    ring
  rw [hp] at h
  simp only [inv_inv] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [largeMass_kernel_rescaled hμ hr]

theorem largeMass_crossover_limit {d : ℝ} (hd : 0 ≤ d) :
    Tendsto (fun μ : ℝ => (2 * μ) ^ (-((d + 4) / 2)) *
      ∫ r in Ioi 0, r ^ (d + 3) * kernel 1 μ (r ^ 2)) atTop
      (𝓝 (Real.Gamma ((d + 4) / 2) / 2)) := by
  have hgi := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := 1) (s := d + 3) (b := 1) (by linarith) (by norm_num) (by norm_num)
  simp only [Real.rpow_one, neg_one_mul] at hgi
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun μ r => r ^ (d + 3) *
      Real.exp (-(2 * r ^ 2 / (Real.sqrt (1 + 2 * r ^ 2 * μ⁻¹) + 1))))
    (f := fun r => r ^ (d + 3) * Real.exp (-r ^ 2))
    (l := atTop) (fun r => Real.exp 1 * (r ^ (d + 3) * Real.exp (-r)))
    (Eventually.of_forall (fun μ => by apply Measurable.aestronglyMeasurable; fun_prop))
    (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with μ hμ
      have hμ0 : 0 < μ := by linarith
      have hc0 : 0 ≤ μ⁻¹ := (inv_pos.mpr hμ0).le
      have hc1 : μ⁻¹ ≤ 1 := by rw [inv_eq_one_div]; exact (div_le_iff₀ hμ0).mpr (by linarith)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : 0 < r := hr
      have hp : depthProfile 1 (r ^ 2) ≤ depthProfile 1 (2 * r ^ 2) := by
        unfold depthProfile
        gcongr
        nlinarith [sq_nonneg r]
      have hratio : depthProfile 1 (2 * r ^ 2) ≤
          2 * r ^ 2 / (Real.sqrt (1 + 2 * r ^ 2 * μ⁻¹) + 1) := by
        rw [depthProfile_eq_div (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 < 2 * r ^ 2)]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        apply add_le_add_right
        apply Real.sqrt_le_sqrt
        have hh := mul_le_mul_of_nonneg_left hc1 (by positivity : 0 ≤ 2 * r ^ 2)
        nlinarith
      have he : Real.exp (-(2 * r ^ 2 / (Real.sqrt (1 + 2 * r ^ 2 * μ⁻¹) + 1))) ≤
          Real.exp 1 * Real.exp (-r) := by
        calc
          _ ≤ kernel 1 1 (r ^ 2) := by
            unfold kernel
            simp only [neg_one_mul]
            exact Real.exp_le_exp.mpr (neg_le_neg (hp.trans hratio))
          _ ≤ _ := by simpa only [one_mul, neg_one_mul, Real.sqrt_sq hr0.le] using
            kernel_upper (M := 1) (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg r)
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_pos _).le)]
      calc
        _ ≤ r ^ (d + 3) * (Real.exp 1 * Real.exp (-r)) := by gcongr
        _ = _ := by ring)
    (hgi.const_mul (Real.exp 1))
    (Eventually.of_forall (fun r => by
      have hc : ContinuousAt (fun c : ℝ => r ^ (d + 3) *
          Real.exp (-(2 * r ^ 2 / (Real.sqrt (1 + 2 * r ^ 2 * c) + 1)))) 0 := by
        fun_prop (disch := positivity)
      have he : -(2 * r ^ 2 / ((1 : ℝ) + 1)) = -r ^ 2 := by ring
      simpa only [Function.comp_def, mul_zero, add_zero, Real.sqrt_one, he] using
        hc.tendsto.comp tendsto_inv_atTop_zero))
  have hg : (∫ r in Ioi 0, r ^ (d + 3) * Real.exp (-r ^ 2)) =
      Real.Gamma ((d + 4) / 2) / 2 := by
    have hh := radial_gaussian_integral_add_two (M := (1 / 2 : ℝ)) hd (by norm_num)
    norm_num at hh
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hh
  rw [hg] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with μ hμ
  exact (largeMass_scaled_radial d hμ).symm

theorem largeMass_crossover_ratio_limit {d : ℝ} (hd : 0 ≤ d) :
    Tendsto (fun μ : ℝ => (∫ r in Ioi 0, r ^ (d + 3) * kernel 1 μ (r ^ 2)) /
      ((1 / 2 : ℝ) * (2 * μ) ^ ((d + 4) / 2) * Real.Gamma ((d + 4) / 2))) atTop (𝓝 1) := by
  have hG : 0 < Real.Gamma ((d + 4) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hG0 : Real.Gamma ((d + 4) / 2) / 2 ≠ 0 := by positivity
  have ht := (largeMass_crossover_limit hd).div_const (Real.Gamma ((d + 4) / 2) / 2)
  rw [div_self hG0] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with μ hμ
  rw [Real.rpow_neg (by positivity : 0 ≤ 2 * μ)]
  have hp : (2 * μ) ^ ((d + 4) / 2) ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
  field_simp [hG.ne', hp]

/-- The full controlled-crossover theorem, with both limits uniform for µ in
bounded nonnegative sets and the large-µ statement expressed as a ratio limit.
Every coefficient is an actual radial Lebesgue integral. -/
theorem oqed_strong_depth_crossover {d m : ℝ} (hd : 0 ≤ d) (hm : 0 < m) :
    (∀ μ, 0 ≤ μ →
      Tendsto (fun a : ℝ => a ^ (d + 4) * oneLineComparison d a (μ / a) m) atTop
        (𝓝 (crossoverH d μ / (8 * Real.pi ^ 2 * m ^ 2))) ∧
      Tendsto (fun a : ℝ => a ^ 4 * scalarBubble a (μ / a) m 0) atTop
        (𝓝 ((3 + 6 * μ + 4 * μ ^ 2) / (64 * Real.pi ^ 2 * m ^ 4)))) ∧
    (∀ K, 0 ≤ K →
      (∀ ε > 0, ∃ A > 0, ∀ a, A < a → ∀ μ, 0 ≤ μ → μ ≤ K →
        |a ^ (d + 4) * oneLineComparison d a (μ / a) m -
          crossoverH d μ / (8 * Real.pi ^ 2 * m ^ 2)| < ε) ∧
      (∀ ε > 0, ∃ A > 0, ∀ a, A < a → ∀ μ, 0 ≤ μ → μ ≤ K →
        |a ^ 4 * scalarBubble a (μ / a) m 0 -
          (3 + 6 * μ + 4 * μ ^ 2) / (64 * Real.pi ^ 2 * m ^ 4)| < ε)) ∧
    (∀ μ, 0 ≤ μ → crossoverH 0 μ = 6 + 6 * μ + 2 * μ ^ 2) ∧
    crossoverH d 0 = Real.Gamma (d + 4) ∧
    Tendsto (fun μ : ℝ => crossoverH d μ /
      ((1 / 2 : ℝ) * (2 * μ) ^ ((d + 4) / 2) * Real.Gamma ((d + 4) / 2))) atTop (𝓝 1) := by
  refine ⟨?_, ?_, (fun _ hμ => crossoverH_zero_degree hμ), crossoverH_zero hd, ?_⟩
  · intro μ hμ
    exact ⟨oneLineComparison_controlled_crossover hd hm μ, scalarBubble_controlled_crossover hμ hm⟩
  · intro K _
    exact ⟨oneLineComparison_controlled_crossover_uniform (K := K) hd hm,
      scalarBubble_controlled_crossover_uniform (K := K) hm⟩
  · simpa only [crossoverH] using largeMass_crossover_ratio_limit hd

end UV
