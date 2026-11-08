import UV.HeatFourier
import UV.PoissonTail
import UV.HeatMeasure
import UV.ScalarLaplace

/-! The literal four-dimensional Poisson kernel is the inverse Fourier
transform of the normalized stable-half multiplier. The proof uses genuine
heat subordination, reciprocal-variable Gamma integrals, and Fubini. -/

noncomputable section
open MeasureTheory Set Real Filter
open scoped Topology ENNReal RealInnerProductSpace Complex

namespace UV

lemma stableInverseHeatCore_change (b t : ℝ) (ht : 0 < t) :
    (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) •
      ((t ^ (-1 : ℝ)) ^ ((3 : ℝ) / 2) * Real.exp (-b * t ^ (-1 : ℝ))) =
        t ^ (-(7 : ℝ) / 2) * Real.exp (-b / t) := by
  norm_num only [abs_neg, abs_one, one_mul, smul_eq_mul]
  rw [← Real.rpow_mul ht.le, ← mul_assoc, ← Real.rpow_add ht]
  congr 1
  · congr 1
    ring
  · rw [Real.rpow_neg_one]
    congr 1

theorem stableInverseHeatCore_integrable {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ (-(7 : ℝ) / 2) * Real.exp (-b / t)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := 1) (s := (3 : ℝ) / 2) (b := b) (by norm_num) (by norm_num) hb
  simp only [Real.rpow_one] at h
  have hi := (integrableOn_Ioi_comp_rpow_iff
    (fun u : ℝ => u ^ ((3 : ℝ) / 2) * Real.exp (-b * u))
    (p := -1) (by norm_num)).mpr h
  exact hi.congr_fun (fun t ht => stableInverseHeatCore_change b t ht) measurableSet_Ioi

theorem stableInverseHeatCore_integral {b : ℝ} (hb : 0 < b) :
    (∫ t : ℝ in Ioi 0, t ^ (-(7 : ℝ) / 2) * Real.exp (-b / t)) =
      b ^ (-(5 : ℝ) / 2) * Real.Gamma (5 / 2) := by
  calc
    _ = ∫ t : ℝ in Ioi 0, (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) •
        ((t ^ (-1 : ℝ)) ^ ((3 : ℝ) / 2) * Real.exp (-b * t ^ (-1 : ℝ))) := by
      exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => (stableInverseHeatCore_change b t ht).symm)
    _ = ∫ u : ℝ in Ioi 0, u ^ ((3 : ℝ) / 2) * Real.exp (-b * u) :=
      integral_comp_rpow_Ioi (fun u : ℝ => u ^ ((3 : ℝ) / 2) * Real.exp (-b * u))
        (p := -1) (by norm_num)
    _ = _ := by
      have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := (3 : ℝ) / 2)
        (b := b) (by norm_num) (by norm_num) hb
      norm_num [Real.rpow_one] at h ⊢
      exact h

/-- The reciprocal Gamma integral is finite at every spatial point because
a>0 provides its strictly positive short-time scale. -/
theorem stableHeatKernel_mixture {a : ℝ} (ha : 0 < a) (x : ScalarMomentum) :
    (∫ t, stableHeatKernel t x ∂oqedHeatMeasure a 0) = stablePoissonKernel a x := by
  let R := stablePoissonRadius a x
  let b := R ^ 2 / (4 * a ^ 2)
  have hr : 0 < R := stablePoissonRadius_pos ha x
  have hb : 0 < b := by dsimp [b]; positivity
  have ha0 : a ≠ 0 := ha.ne'
  have hr0 : R ≠ 0 := hr.ne'
  have hsqrt : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hpoint {t : ℝ} (ht : 0 < t) :
      oqedDensity 0 t * stableHeatKernel (a ^ 2 * t) x =
        (1 / (32 * Real.pi ^ 2 * Real.sqrt Real.pi * a ^ 4)) *
          (t ^ (-(7 : ℝ) / 2) * Real.exp (-b / t)) := by
    have ht0 := ht.ne'
    have hp : t ^ (-(7 : ℝ) / 2) = t ^ (-(3 : ℝ) / 2) * (t ^ 2)⁻¹ := by
      rw [← Real.rpow_two, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
      congr 1
      norm_num
    have he : -(1 / (4 * t)) + (-‖x‖ ^ 2 / (4 * (a ^ 2 * t))) = -b / t := by
      dsimp [b, R]
      rw [stablePoissonRadius_sq]
      field_simp
      ring
    unfold oqedDensity oqedDensityCore stableHeatKernel
    simp only [Real.exp_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul,
      neg_zero, zero_sub]
    rw [hp, ← he, Real.exp_add]
    field_simp
    ring
  have hpow : b ^ (-(5 : ℝ) / 2) = (2 * a / R) ^ 5 := by
    have heq : b = (R / (2 * a)) ^ 2 := by dsimp [b]; ring
    rw [heq, ← Real.rpow_natCast (R / (2 * a)) 2, ← Real.rpow_mul (by positivity)]
    norm_num
    field_simp
  have hg : Real.Gamma (5 / 2) = 3 * Real.sqrt Real.pi / 4 := by
    have h := Real.Gamma_nat_add_half 2
    norm_num at h
    convert h using 1
  calc
    _ = ∫ t : ℝ in Ioi 0, oqedDensity 0 t * stableHeatKernel (a ^ 2 * t) x := by
      unfold oqedHeatMeasure
      have hm : Measurable (fun t : ℝ => stableHeatKernel t x) := by unfold stableHeatKernel; fun_prop
      rw [mul_zero, integral_map (by fun_prop) hm.aestronglyMeasurable,
        oqedMeasure, integral_withDensity_eq_integral_toReal_smul
          (oqedDensity_measurable 0).ennreal_ofReal
          (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [ENNReal.toReal_ofReal (oqedDensity_nonneg 0 t ht.le), smul_eq_mul]
    _ = (1 / (32 * Real.pi ^ 2 * Real.sqrt Real.pi * a ^ 4)) *
        ∫ t : ℝ in Ioi 0, t ^ (-(7 : ℝ) / 2) * Real.exp (-b / t) := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => hpoint ht)
    _ = _ := by
      rw [stableInverseHeatCore_integral hb, hpow, hg]
      unfold stablePoissonKernel
      change _ = (3 * a / (4 * Real.pi ^ 2)) / R ^ 5
      field_simp
      ring

lemma stableFourierPhase_comm (q x : ScalarMomentum) : stableFourierPhase q x = stableFourierPhase x q := by
  unfold stableFourierPhase
  rw [real_inner_comm]

lemma stableHeatKernel_wave_eq (t : ℝ) (q x : ScalarMomentum) :
    stableFourierPhase q x * (stableHeatKernel t x : ℂ) =
      ((16 * Real.pi ^ 2 * t ^ 2)⁻¹ : ℂ) * stableGaussianWave (1 / (4 * t)) q x := by
  simp only [stableHeatKernel, stableGaussianWave]
  rw [show -‖x‖ ^ 2 / (4 * t) = -(1 / (4 * t)) * ‖x‖ ^ 2 by ring]
  push_cast
  ring

theorem stableHeatKernel_characteristic_integrable {t : ℝ} (ht : 0 < t) (q : ScalarMomentum) :
    Integrable (fun x : ScalarMomentum => stableFourierPhase q x * (stableHeatKernel t x : ℂ)) := by
  simp_rw [stableHeatKernel_wave_eq]
  exact (stable_gaussian_characteristic_integrable (by positivity) q).const_mul _

theorem stableHeatKernel_characteristic {t : ℝ} (ht : 0 < t) (q : ScalarMomentum) :
    (∫ x : ScalarMomentum, stableFourierPhase q x * (stableHeatKernel t x : ℂ)) =
      (Real.exp (-t * ‖q‖ ^ 2) : ℂ) := by
  simp_rw [stableHeatKernel_wave_eq]
  rw [integral_const_mul, stable_gaussian_characteristic_integral (by positivity)]
  have he : -‖q‖ ^ 2 / (4 * (1 / (4 * t))) = -t * ‖q‖ ^ 2 := by field_simp
  rw [he]
  push_cast
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  field_simp [htc]
  norm_num

theorem stableHeatMeasure_positive {a : ℝ} (ha : 0 < a) :
    ∀ᵐ t ∂oqedHeatMeasure a 0, 0 < t := by
  exact ae_positive_of_support_no_atom (oqedHeatMeasure a 0)
    (measure_mono_null Iio_subset_Iic_self (oqedHeatMeasure_nonnegative_support ha 0))
    (oqedHeatMeasure_no_atom_zero ha 0)

/-- The Gaussian probability kernels have an integrable joint density under
any finite positive proper-time measure. -/
theorem stableHeatKernel_joint_integrable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ t ∂ρ, 0 < t) :
    Integrable (fun p : ℝ × ScalarMomentum => stableHeatKernel p.1 p.2) (ρ.prod volume) := by
  have hm : Measurable (fun p : ℝ × ScalarMomentum => stableHeatKernel p.1 p.2) := by
    unfold stableHeatKernel
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨hp.mono (fun t ht => stableHeatKernel_integrable ht), ?_⟩
  apply (integrable_const (μ := ρ) (1 : ℝ)).congr
  filter_upwards [hp] with t ht
  simp only [Real.norm_of_nonneg (stableHeatKernel_nonneg t _)]
  exact (stableHeatKernel_integral ht).symm

theorem stablePoissonKernel_integrable {a : ℝ} (ha : 0 < a) : Integrable (stablePoissonKernel a) := by
  have hj := stableHeatKernel_joint_integrable (oqedHeatMeasure a 0) (stableHeatMeasure_positive ha)
  simpa only [stableHeatKernel_mixture ha] using hj.integral_prod_right

theorem stablePoissonKernel_integral {a : ℝ} (ha : 0 < a) :
    (∫ x : ScalarMomentum, stablePoissonKernel a x) = 1 := by
  haveI := oqedHeatMeasure_probability ha.le (by norm_num : (0 : ℝ) ≤ 0)
  have hj := stableHeatKernel_joint_integrable (oqedHeatMeasure a 0) (stableHeatMeasure_positive ha)
  simp_rw [← stableHeatKernel_mixture ha]
  rw [← integral_integral_swap hj]
  calc
    _ = ∫ _ : ℝ, (1 : ℝ) ∂oqedHeatMeasure a 0 := by
      apply integral_congr_ae
      filter_upwards [stableHeatMeasure_positive ha] with t ht
      exact stableHeatKernel_integral ht
    _ = 1 := by simp

lemma stableHeatKernel_joint_wave_integrable (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ t ∂ρ, 0 < t) (q : ScalarMomentum) :
    Integrable (fun p : ℝ × ScalarMomentum =>
      stableFourierPhase q p.2 * (stableHeatKernel p.1 p.2 : ℂ)) (ρ.prod volume) := by
  refine (stableHeatKernel_joint_integrable ρ hp).mono'
    ((by unfold stableFourierPhase stableHeatKernel; fun_prop : Measurable (fun p : ℝ × ScalarMomentum =>
      stableFourierPhase q p.2 * (stableHeatKernel p.1 p.2 : ℂ))).aestronglyMeasurable) ?_
  exact Eventually.of_forall fun p => by
    rw [norm_mul, stableFourierPhase_norm, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (stableHeatKernel_nonneg _ _)]

lemma stableHeatMeasure_zero_laplace {a : ℝ} (ha : 0 < a) (q : ScalarMomentum) :
    (∫ t, Real.exp (-t * ‖q‖ ^ 2) ∂oqedHeatMeasure a 0) = Real.exp (-a * ‖q‖) := by
  change laplace (oqedHeatMeasure a 0) (‖q‖ ^ 2) = _
  rw [oqedHeatMeasure_laplace ha.le (sq_nonneg _) 0]
  simp [kernel, depthProfile, Real.sqrt_sq (norm_nonneg q)]

/-- The actual Fourier transform of the literal Poisson density. -/
theorem stablePoissonKernel_characteristic {a : ℝ} (ha : 0 < a) (q : ScalarMomentum) :
    (∫ x : ScalarMomentum, stableFourierPhase q x * (stablePoissonKernel a x : ℂ)) =
      (Real.exp (-a * ‖q‖) : ℂ) := by
  have hj := stableHeatKernel_joint_wave_integrable (oqedHeatMeasure a 0)
    (stableHeatMeasure_positive ha) q
  calc
    _ = ∫ x : ScalarMomentum, ∫ t,
        stableFourierPhase q x * (stableHeatKernel t x : ℂ) ∂oqedHeatMeasure a 0 := by
      congr 1
      ext x
      rw [integral_const_mul, integral_complex_ofReal, stableHeatKernel_mixture ha]
    _ = ∫ t, ∫ x : ScalarMomentum,
        stableFourierPhase q x * (stableHeatKernel t x : ℂ) ∂volume ∂oqedHeatMeasure a 0 :=
      (integral_integral_swap hj).symm
    _ = ∫ t, (Real.exp (-t * ‖q‖ ^ 2) : ℂ) ∂oqedHeatMeasure a 0 := by
      apply integral_congr_ae
      filter_upwards [stableHeatMeasure_positive ha] with t ht
      exact stableHeatKernel_characteristic ht q
    _ = _ := by rw [integral_complex_ofReal, stableHeatMeasure_zero_laplace ha]

theorem stablePoissonMultiplier_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun q : ScalarMomentum => Real.exp (-a * ‖q‖)) := by
  apply (integrable_fun_norm_addHaar (E := ScalarMomentum) volume
    (f := fun r : ℝ => Real.exp (-a * r))).mpr
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 3) (b := a)
    (by norm_num) (by norm_num) ha
  simp only [Real.rpow_one] at h
  apply h.congr_fun _ measurableSet_Ioi
  intro r _
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
  simp only [Real.rpow_ofNat]

lemma stableFourier_prefactor : (2 * Real.pi) ^ (-4 : ℤ) = 1 / (16 * Real.pi ^ 4) := by
  norm_num [zpow_neg]
  field_simp
  ring

theorem stableHeatKernel_inverseFourier {t : ℝ} (ht : 0 < t) (x : ScalarMomentum) :
    (((2 * Real.pi) ^ (-4 : ℤ) : ℝ) : ℂ) *
      (∫ q : ScalarMomentum, stableGaussianWave t x q) = (stableHeatKernel t x : ℂ) := by
  rw [stable_gaussian_characteristic_integral ht, stableFourier_prefactor]
  unfold stableHeatKernel
  push_cast
  field_simp

/-- The inverse square moment supplies the absolute joint Gaussian integral
required for inverse Fourier exchange. -/
theorem stableGaussianWave_joint_integrable {a : ℝ} (ha : 0 < a) (x : ScalarMomentum) :
    Integrable (fun p : ℝ × ScalarMomentum => stableGaussianWave p.1 x p.2)
      ((oqedHeatMeasure a 0).prod volume) := by
  have hp := stableHeatMeasure_positive ha
  have hm : Measurable (fun p : ℝ × ScalarMomentum => stableGaussianWave p.1 x p.2) := by
    unfold stableGaussianWave stableFourierPhase
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨hp.mono (fun t ht => stable_gaussian_characteristic_integrable ht x), ?_⟩
  have hi := positive_inverse_square_integrable (oqedHeatMeasure a 0)
    (measure_mono_null Iio_subset_Iic_self (oqedHeatMeasure_nonnegative_support ha 0))
    (oqedHeatMeasure_no_atom_zero ha 0)
    (oqedHeatMeasure_inverseMoment_finite ha 0 (r := 2) (by norm_num))
  apply (hi.const_mul (Real.pi ^ 2)).congr
  filter_upwards [hp] with t ht
  simp_rw [stableGaussianWave_norm]
  rw [scalar_gaussian_integral ht]
  rfl

/-- The exact inverse Fourier transform of exp(-a‖q‖), including the source's
(2π)⁻⁴ normalization, is the literal Poisson kernel. -/
theorem stablePoissonKernel_inverseFourier {a : ℝ} (ha : 0 < a) (x : ScalarMomentum) :
    (((2 * Real.pi) ^ (-4 : ℤ) : ℝ) : ℂ) *
      (∫ q : ScalarMomentum, stableFourierPhase q x * (Real.exp (-a * ‖q‖) : ℂ)) =
        (stablePoissonKernel a x : ℂ) := by
  have hj := stableGaussianWave_joint_integrable ha x
  calc
    _ = (((2 * Real.pi) ^ (-4 : ℤ) : ℝ) : ℂ) *
        ∫ q : ScalarMomentum, ∫ t,
          stableGaussianWave t x q ∂oqedHeatMeasure a 0 := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun q => by
        dsimp only
        unfold stableGaussianWave
        rw [integral_const_mul, integral_complex_ofReal, stableHeatMeasure_zero_laplace ha,
          stableFourierPhase_comm q x]
    _ = (((2 * Real.pi) ^ (-4 : ℤ) : ℝ) : ℂ) *
        ∫ t, ∫ q : ScalarMomentum, stableGaussianWave t x q ∂volume ∂oqedHeatMeasure a 0 := by
      congr 1
      exact (integral_integral_swap (f := fun t q => stableGaussianWave t x q) hj).symm
    _ = ∫ t, (stableHeatKernel t x : ℂ) ∂oqedHeatMeasure a 0 := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [stableHeatMeasure_positive ha] with t ht
      exact stableHeatKernel_inverseFourier ht x
    _ = _ := by rw [integral_complex_ofReal, stableHeatKernel_mixture ha]

theorem stablePoissonKernel_characteristic_integrable {a : ℝ} (ha : 0 < a) (q : ScalarMomentum) :
    Integrable (fun x : ScalarMomentum => stableFourierPhase q x * (stablePoissonKernel a x : ℂ)) := by
  refine (stablePoissonKernel_integrable ha).mono'
    ((by unfold stableFourierPhase stablePoissonKernel stablePoissonRadius; fun_prop :
      Measurable (fun x : ScalarMomentum => stableFourierPhase q x * (stablePoissonKernel a x : ℂ))).aestronglyMeasurable) ?_
  exact Eventually.of_forall fun x => by
    rw [norm_mul, stableFourierPhase_norm, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (stablePoissonKernel_pos ha x).le]

theorem stablePoissonMultiplier_wave_integrable {a : ℝ} (ha : 0 < a) (x : ScalarMomentum) :
    Integrable (fun q : ScalarMomentum => stableFourierPhase q x * (Real.exp (-a * ‖q‖) : ℂ)) := by
  refine (stablePoissonMultiplier_integrable ha).mono'
    ((by unfold stableFourierPhase; fun_prop :
      Measurable (fun q : ScalarMomentum => stableFourierPhase q x * (Real.exp (-a * ‖q‖) : ℂ))).aestronglyMeasurable) ?_
  exact Eventually.of_forall fun q => by
    rw [norm_mul, stableFourierPhase_norm, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_nonneg _)]

end UV
