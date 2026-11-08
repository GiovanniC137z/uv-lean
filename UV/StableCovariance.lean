import UV.StableGreen
import UV.StableMoments
import UV.StablePoisson
import UV.CoordinateSquareFourier

/-! Literal stable-half scalar covariance as an actual positive Green–Poisson
convolution, and the coordinate-square representation of the bubble. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal InnerProductSpace

namespace UV

def stableCoordinateCovariance (a m : ℝ) : ScalarMomentum → ℝ :=
  stableCoordinateConvolution a (stableGreenMeasure m)

theorem stableCoordinateCovariance_nonneg {a : ℝ} (ha : 0 < a) (m : ℝ) (x : ScalarMomentum) :
    0 ≤ stableCoordinateCovariance a m x := stableCoordinateConvolution_nonneg ha _ x

theorem stableCoordinateCovariance_le {a m : ℝ} (ha : 0 < a) (hm : 0 < m) (x : ScalarMomentum) :
    stableCoordinateCovariance a m x ≤ stablePoissonKernel a 0 / m ^ 2 := by
  letI := stableGreenMeasure_finite hm
  have h := stableCoordinateConvolution_le ha (stableGreenMeasure m) x
  rw [stableGreenMeasure_real_mass hm] at h
  simpa only [stableCoordinateCovariance, div_eq_mul_inv, one_mul, mul_one, mul_comm] using h

theorem stableCoordinateCovariance_continuous {a m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    Continuous (stableCoordinateCovariance a m) := by
  letI := stableGreenMeasure_finite hm
  exact stableCoordinateConvolution_continuous ha _

theorem scalarCovariance_stable (a m : ℝ) (q : ScalarMomentum) :
    scalarCovariance a 0 m q = Real.exp (-a * ‖q‖) / (‖q‖ ^ 2 + m ^ 2) := by
  simp [scalarCovariance, kernel, depthProfile, Real.sqrt_sq (norm_nonneg q)]

theorem scalarCovariance_stable_integrable {a m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    Integrable (scalarCovariance a 0 m) := by
  have he : Integrable (fun q : ScalarMomentum => Real.exp (-(a * ‖q‖))) := by
    simpa only [pow_zero, one_mul] using
      (integrable_norm_pow_exp (E := ScalarMomentum) ha 0)
  apply (he.const_mul (1 / m ^ 2)).mono' (scalarCovariance_continuous hm).aestronglyMeasurable
  filter_upwards with q
  rw [Real.norm_of_nonneg (scalarCovariance_nonneg _), scalarCovariance_stable]
  calc
    _ ≤ Real.exp (-a * ‖q‖) / m ^ 2 :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (sq_pos_of_pos hm) (le_add_of_nonneg_left (sq_nonneg _))
    _ = _ := by simp only [div_eq_mul_inv, neg_mul]; ring

theorem stableFourierPhase_add_frequency (q P x : ScalarMomentum) :
    stableFourierPhase (q + P) x = stableFourierPhase q x * stableFourierPhase P x := by
  unfold stableFourierPhase
  rw [inner_add_left, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem stableFourierPhase_sub (q x y : ScalarMomentum) :
    stableFourierPhase q (x - y) = stableFourierPhase q x * stableFourierPhase (-q) y := by
  rw [sub_eq_add_neg, stableFourierPhase_add, stableFourierPhase_neg]

theorem stablePoissonKernel_translate_integrable {a : ℝ} (ha : 0 < a) (y : ScalarMomentum) :
    Integrable (fun x : ScalarMomentum => stablePoissonKernel a (x - y)) := by
  simpa only [sub_eq_add_neg] using
    (measurePreserving_add_right volume (-y)).integrable_comp_of_integrable
      (stablePoissonKernel_integrable ha)

theorem stablePoissonKernel_translate_integral {a : ℝ} (ha : 0 < a) (y : ScalarMomentum) :
    (∫ x : ScalarMomentum, stablePoissonKernel a (x - y)) = 1 := by
  simpa only [sub_eq_add_neg, stablePoissonKernel_integral ha] using
    integral_add_right_eq_self (μ := volume) (stablePoissonKernel a) (-y)

theorem stableCoordinateCovariance_joint_integrable {a m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    Integrable (fun p : ScalarMomentum × ScalarMomentum => stablePoissonKernel a (p.2 - p.1))
      ((stableGreenMeasure m).prod volume) := by
  letI := stableGreenMeasure_finite hm
  apply (integrable_prod_iff
    ((stablePoissonKernel_continuous ha).comp (continuous_snd.sub continuous_fst)).aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (stablePoissonKernel_translate_integrable ha), ?_⟩
  have he : (fun y : ScalarMomentum => ∫ x : ScalarMomentum, ‖stablePoissonKernel a (x - y)‖) =
      (fun _ => (1 : ℝ)) := by
    funext y
    simp_rw [Real.norm_of_nonneg (stablePoissonKernel_pos ha _).le]
    exact stablePoissonKernel_translate_integral ha y
  change Integrable (fun y : ScalarMomentum => ∫ x : ScalarMomentum, ‖stablePoissonKernel a (x - y)‖) _
  rw [he]
  exact integrable_const _

theorem stableCoordinateCovariance_integrable {a m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    Integrable (stableCoordinateCovariance a m) := by
  letI := stableGreenMeasure_finite hm
  exact (stableCoordinateCovariance_joint_integrable ha hm).swap.integral_prod_left

theorem stableCoordinateCovariance_integral {a m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    (∫ x, stableCoordinateCovariance a m x) = 1 / m ^ 2 := by
  letI := stableGreenMeasure_finite hm
  change (∫ x, ∫ y, stablePoissonKernel a (x - y) ∂stableGreenMeasure m) = _
  rw [integral_integral_swap (f := fun x y : ScalarMomentum => stablePoissonKernel a (x - y))
    (stableCoordinateCovariance_joint_integrable ha hm).swap]
  simp_rw [stablePoissonKernel_translate_integral ha]
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real, stableGreenMeasure_real_mass hm]

theorem stableCoordinateCovariance_square_integrable {a m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    Integrable (fun x => stableCoordinateCovariance a m x ^ 2) := by
  apply ((stableCoordinateCovariance_integrable ha hm).const_mul (stablePoissonKernel a 0 / m ^ 2)).mono'
    ((stableCoordinateCovariance_continuous ha hm).pow 2).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simpa only [pow_two] using mul_le_mul_of_nonneg_right
    (stableCoordinateCovariance_le ha hm x) (stableCoordinateCovariance_nonneg ha m x)

theorem stableCoordinateCovariance_forward_joint_integrable {a m : ℝ}
    (ha : 0 < a) (hm : 0 < m) (q : ScalarMomentum) :
    Integrable (fun p : ScalarMomentum × ScalarMomentum =>
      stableFourierPhase q p.2 * (stablePoissonKernel a (p.2 - p.1) : ℂ))
      ((stableGreenMeasure m).prod volume) := by
  have h₁ : Continuous (fun p : ScalarMomentum × ScalarMomentum => stableFourierPhase q p.2) := by
    unfold stableFourierPhase
    fun_prop
  have h₂ := Complex.continuous_ofReal.comp
    ((stablePoissonKernel_continuous ha).comp (continuous_snd.sub continuous_fst))
  apply (stableCoordinateCovariance_joint_integrable ha hm).mono' (h₁.mul h₂).aestronglyMeasurable
  filter_upwards with p
  dsimp only [Function.comp_apply]
  rw [norm_mul, stableFourierPhase_norm, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (stablePoissonKernel_pos ha _).le]

theorem stablePoissonKernel_translate_characteristic {a : ℝ} (ha : 0 < a)
    (q y : ScalarMomentum) :
    (∫ x : ScalarMomentum, stableFourierPhase q x * (stablePoissonKernel a (x - y) : ℂ)) =
      stableFourierPhase q y * (Real.exp (-a * ‖q‖) : ℂ) := by
  have he : (fun x : ScalarMomentum =>
      stableFourierPhase q (x + y) * (stablePoissonKernel a (x + y - y) : ℂ)) =
      (fun x => stableFourierPhase q y * (stableFourierPhase q x * (stablePoissonKernel a x : ℂ))) := by
    funext x
    rw [add_sub_cancel_right, stableFourierPhase_add]
    ring
  have ht := integral_add_right_eq_self (μ := volume)
    (fun x : ScalarMomentum => stableFourierPhase q x * (stablePoissonKernel a (x - y) : ℂ)) y
  rw [he, integral_const_mul, stablePoissonKernel_characteristic ha] at ht
  exact ht.symm

theorem stableCoordinateCovariance_characteristic {a m : ℝ}
    (ha : 0 < a) (hm : 0 < m) (q : ScalarMomentum) :
    (∫ x : ScalarMomentum, stableFourierPhase q x * (stableCoordinateCovariance a m x : ℂ)) =
      (scalarCovariance a 0 m q : ℂ) := by
  letI := stableGreenMeasure_finite hm
  have hc (x : ScalarMomentum) :
      (stableCoordinateCovariance a m x : ℂ) =
        ∫ y, (stablePoissonKernel a (x - y) : ℂ) ∂stableGreenMeasure m :=
    integral_complex_ofReal.symm
  simp_rw [hc, ← integral_const_mul]
  rw [integral_integral_swap (f := fun x y : ScalarMomentum =>
    stableFourierPhase q x * (stablePoissonKernel a (x - y) : ℂ))
    (stableCoordinateCovariance_forward_joint_integrable ha hm q).swap]
  simp_rw [stablePoissonKernel_translate_characteristic ha, integral_mul_const,
    stableGreenMeasure_characteristic hm, scalarCovariance_stable]
  push_cast
  ring

theorem stableCoordinateCovariance_inverse_joint_integrable {a m : ℝ}
    (ha : 0 < a) (hm : 0 < m) (x : ScalarMomentum) :
    Integrable (fun p : ScalarMomentum × ScalarMomentum =>
      stableFourierPhase p.2 (x - p.1) * (Real.exp (-a * ‖p.2‖) : ℂ))
      ((stableGreenMeasure m).prod volume) := by
  letI := stableGreenMeasure_finite hm
  have hi := (integrable_const (μ := stableGreenMeasure m) (1 : ℝ)).mul_prod
    (stablePoissonMultiplier_integrable ha)
  apply hi.mono' (by unfold stableFourierPhase; fun_prop)
  filter_upwards with p
  rw [norm_mul, stableFourierPhase_norm, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, one_mul]

theorem stableCoordinateCovariance_inverseFourier {a m : ℝ}
    (ha : 0 < a) (hm : 0 < m) (x : ScalarMomentum) :
    (((2 * Real.pi) ^ (-4 : ℤ) : ℝ) : ℂ) *
      (∫ q : ScalarMomentum, stableFourierPhase q x * (scalarCovariance a 0 m q : ℂ)) =
        (stableCoordinateCovariance a m x : ℂ) := by
  letI := stableGreenMeasure_finite hm
  symm
  change (((∫ y, stablePoissonKernel a (x - y) ∂stableGreenMeasure m) : ℝ) : ℂ) = _
  rw [← integral_complex_ofReal]
  simp_rw [← stablePoissonKernel_inverseFourier ha]
  rw [integral_const_mul,
    integral_integral_swap (f := fun y q : ScalarMomentum =>
      stableFourierPhase q (x - y) * (Real.exp (-a * ‖q‖) : ℂ))
      (stableCoordinateCovariance_inverse_joint_integrable ha hm x)]
  congr 1
  apply integral_congr_ae
  filter_upwards with q
  have he : (fun y : ScalarMomentum =>
      stableFourierPhase q (x - y) * (Real.exp (-a * ‖q‖) : ℂ)) =
      (fun y => (stableFourierPhase q x * (Real.exp (-a * ‖q‖) : ℂ)) * stableFourierPhase (-q) y) := by
    funext y
    rw [stableFourierPhase_sub]
    ring
  rw [he, integral_const_mul, stableGreenMeasure_characteristic hm, norm_neg,
    scalarCovariance_stable]
  push_cast
  ring

theorem stableBubble_coordinate_joint_integrable {a m : ℝ}
    (ha : 0 < a) (hm : 0 < m) (P : ScalarMomentum) :
    Integrable (fun p : ScalarMomentum × ScalarMomentum =>
      (scalarCovariance a 0 m p.1 : ℂ) * stableFourierPhase (p.1 + P) p.2 *
        (stableCoordinateCovariance a m p.2 : ℂ)) (volume.prod volume) := by
  have h₁ : Integrable (fun q : ScalarMomentum => (scalarCovariance a 0 m q : ℂ)) :=
    (scalarCovariance_stable_integrable ha hm).ofReal
  have h₂ : Integrable (fun x : ScalarMomentum => (stableCoordinateCovariance a m x : ℂ)) :=
    (stableCoordinateCovariance_integrable ha hm).ofReal
  have hi := h₁.mul_prod h₂
  have hphase : Continuous (fun p : ScalarMomentum × ScalarMomentum => stableFourierPhase (p.1 + P) p.2) := by
    unfold stableFourierPhase
    fun_prop
  have hj := hi.bdd_mul hphase.aestronglyMeasurable
    ⟨1, fun p => (stableFourierPhase_norm (p.1 + P) p.2).le⟩
  change Integrable (fun p : ScalarMomentum × ScalarMomentum =>
    stableFourierPhase (p.1+P) p.2 *
      ((scalarCovariance a 0 m p.1 : ℂ) * (stableCoordinateCovariance a m p.2 : ℂ)))
        (volume.prod volume) at hj
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hj

/-- The bubble identity exchanges only an L1 momentum covariance and an L1
coordinate covariance. Both integrability hypotheses have already been
derived for the literal kernel. -/
theorem scalarBubble_stable_coordinate_square {a m : ℝ}
    (ha : 0 < a) (hm : 0 < m) (P : ScalarMomentum) :
    (scalarBubble a 0 m P : ℂ) = coordinateSquareFourier (stableCoordinateCovariance a m) P := by
  let κ : ℂ := (((2 * Real.pi) ^ (-4 : ℤ) : ℝ) : ℂ)
  let C := stableCoordinateCovariance a m
  let c := scalarCovariance a 0 m
  have hforward (q : ScalarMomentum) : (c q : ℂ) =
      ∫ x : ScalarMomentum, stableFourierPhase q x * (C x : ℂ) :=
    (stableCoordinateCovariance_characteristic ha hm q).symm
  change (((2 * Real.pi) ^ (-4 : ℤ) *
    (∫ q : ScalarMomentum, c q * c (q + P)) : ℝ) : ℂ) = _
  rw [Complex.ofReal_mul, ← integral_complex_ofReal]
  simp only [Complex.ofReal_mul]
  change κ * (∫ q : ScalarMomentum, (c q : ℂ) * (c (q + P) : ℂ)) = _
  calc
    _ = κ * ∫ q : ScalarMomentum, ∫ x : ScalarMomentum,
        (c q : ℂ) * stableFourierPhase (q + P) x * (C x : ℂ) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with q
      rw [hforward (q + P), ← integral_const_mul]
      congr 1
      funext x
      ring
    _ = κ * ∫ x : ScalarMomentum, ∫ q : ScalarMomentum,
        (c q : ℂ) * stableFourierPhase (q + P) x * (C x : ℂ) := by
      rw [integral_integral_swap (stableBubble_coordinate_joint_integrable ha hm P)]
    _ = coordinateSquareFourier C P := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      have he : (fun q : ScalarMomentum =>
          (c q : ℂ) * stableFourierPhase (q + P) x * (C x : ℂ)) =
          (fun q => (stableFourierPhase P x * (C x : ℂ)) *
            (stableFourierPhase q x * (c q : ℂ))) := by
        funext q
        rw [stableFourierPhase_add_frequency]
        ring
      rw [he, integral_const_mul]
      have hinv := stableCoordinateCovariance_inverseFourier ha hm x
      change κ * (∫ q, stableFourierPhase q x * (c q : ℂ)) = (C x : ℂ) at hinv
      calc
        _ = (stableFourierPhase P x * (C x : ℂ)) *
            (κ * ∫ q, stableFourierPhase q x * (c q : ℂ)) := by ring
        _ = _ := by rw [hinv]; push_cast; ring

end UV
