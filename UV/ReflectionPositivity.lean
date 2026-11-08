import UV.AnalyticScalar
import UV.GlobalConvergence
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! The actual heat-damped time covariance and its finite positive-time
Hankel obstruction. Source: prop:OS-counterexample. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace UV

/-- A second derivative test derived from derivative limits and the mean-value theorem. -/
theorem negative_near_zero_of_negative_second_derivative {D D₁ : ℝ → ℝ} {d₂ : ℝ}
    (hD : ∀ x, HasDerivAt D (D₁ x) x) (hD0 : D 0 = 0) (hD₁0 : D₁ 0 = 0)
    (hD₁ : HasDerivAt D₁ d₂ 0) (hd₂ : d₂ < 0) :
    ∃ δ > 0, ∀ ε, 0 < ε → ε < δ → D ε < 0 := by
  have ht := (hasDerivAt_iff_tendsto_slope_left_right.mp hD₁).2
  have hn : ∀ᶠ x in 𝓝[>] (0 : ℝ), slope D₁ 0 x < 0 :=
    ht.eventually (eventually_lt_nhds hd₂)
  obtain ⟨δ, hδ, hneg⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hn
  refine ⟨δ, hδ, fun ε hε hεδ => ?_⟩
  obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope D D₁ hε
    (fun x _ => (hD x).continuousAt.continuousWithinAt) (fun x _ => hD x)
  have hs := hneg ⟨hc.1, hc.2.trans hεδ⟩
  change slope D₁ 0 c < 0 at hs
  rw [slope_def_field, hD₁0, sub_zero, sub_zero] at hs
  have hcneg : D₁ c < 0 := by simpa using (div_lt_iff₀ hc.1).mp hs
  rw [hD0, sub_zero, sub_zero] at heq
  exact lt_of_lt_of_eq ((div_lt_iff₀ hε).mp (heq ▸ hcneg)) (zero_mul ε)

def heatTimeWeight (t ω p : ℝ) : ℝ :=
  Real.exp (-t * p ^ 2) / (p ^ 2 + ω ^ 2)

theorem heatTimeWeight_pos {t ω p : ℝ} (hω : 0 < ω) : 0 < heatTimeWeight t ω p := by
  unfold heatTimeWeight
  exact div_pos (Real.exp_pos _) (by positivity)

@[fun_prop] theorem heatTimeWeight_continuous (t : ℝ) {ω : ℝ} (hω : 0 < ω) :
    Continuous (heatTimeWeight t ω) := by
  unfold heatTimeWeight
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro p; positivity

theorem heatTimeWeight_moment_integrable {t ω : ℝ} (ht : 0 < t) (hω : 0 < ω) (n : ℕ) :
    Integrable (fun p : ℝ => |p| ^ n * heatTimeWeight t ω p) := by
  have hg : Integrable (fun p : ℝ => |p| ^ n * Real.exp (-t * p ^ 2)) := by
    have h := (integrable_rpow_mul_exp_neg_mul_sq ht
      (show (-1 : ℝ) < (n : ℝ) by have := Nat.cast_nonneg (α := ℝ) n; linarith)).norm
    simpa only [Real.rpow_natCast, norm_mul, norm_pow, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] using h
  apply (hg.div_const (ω ^ 2)).mono'
  · exact (((continuous_abs.pow n).mul (heatTimeWeight_continuous t hω))).aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (heatTimeWeight_pos hω).le)]
    unfold heatTimeWeight
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [sq_nonneg p]

def heatTimeCovariance (t ω u : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ p, Real.cos (p * u) * heatTimeWeight t ω p

def heatTimeFirst (t ω u : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ p, (-p * Real.sin (p * u)) * heatTimeWeight t ω p

def heatTimeSecond (t ω u : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ p, (-p ^ 2 * Real.cos (p * u)) * heatTimeWeight t ω p

theorem heatTimeCovariance_even (t ω u : ℝ) :
    heatTimeCovariance t ω (-u) = heatTimeCovariance t ω u := by
  simp [heatTimeCovariance]

theorem heatTimeFirst_zero (t ω : ℝ) : heatTimeFirst t ω 0 = 0 := by
  simp [heatTimeFirst]

theorem heatTimeCos_integrable {t ω : ℝ} (ht : 0 < t) (hω : 0 < ω) (u : ℝ) :
    Integrable (fun p => Real.cos (p * u) * heatTimeWeight t ω p) := by
  apply (heatTimeWeight_moment_integrable ht hω 0).mono'
  · exact (by fun_prop (disch := assumption) : Continuous (fun p => Real.cos (p * u) * heatTimeWeight t ω p)).aestronglyMeasurable
  · filter_upwards with p
    simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (heatTimeWeight_pos hω), pow_zero, one_mul]
    exact mul_le_of_le_one_left (heatTimeWeight_pos hω).le (Real.abs_cos_le_one _)

theorem heatTimeSin_integrable {t ω : ℝ} (ht : 0 < t) (hω : 0 < ω) (u : ℝ) :
    Integrable (fun p => (-p * Real.sin (p * u)) * heatTimeWeight t ω p) := by
  apply (heatTimeWeight_moment_integrable ht hω 1).mono'
  · exact (by fun_prop (disch := assumption) : Continuous (fun p => (-p * Real.sin (p * u)) * heatTimeWeight t ω p)).aestronglyMeasurable
  · filter_upwards with p
    simp only [norm_mul, Real.norm_eq_abs, abs_neg, abs_of_pos (heatTimeWeight_pos hω), pow_one]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (abs_nonneg p) (Real.abs_sin_le_one _)) (heatTimeWeight_pos hω).le

theorem heatTimeCovariance_hasDerivAt {t ω : ℝ} (ht : 0 < t) (hω : 0 < ω) (u : ℝ) :
    HasDerivAt (heatTimeCovariance t ω) (heatTimeFirst t ω u) u := by
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun v p => Real.cos (p * v) * heatTimeWeight t ω p)
    (F' := fun v p => (-p * Real.sin (p * v)) * heatTimeWeight t ω p)
    (x₀ := u) (ε := 1) (μ := volume)
    (bound := fun p => |p| ^ 1 * heatTimeWeight t ω p)
    (by norm_num)
    (Eventually.of_forall (fun v =>
      (by fun_prop (disch := assumption) : Continuous (fun p => Real.cos (p * v) * heatTimeWeight t ω p)).aestronglyMeasurable))
    (heatTimeCos_integrable ht hω u)
    ((by fun_prop (disch := assumption) : Continuous (fun p => (-p * Real.sin (p * u)) * heatTimeWeight t ω p)).aestronglyMeasurable)
    (Eventually.of_forall (fun p v _ => by
      simp only [norm_mul, Real.norm_eq_abs, abs_neg, abs_of_pos (heatTimeWeight_pos hω), pow_one]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right (abs_nonneg p) (Real.abs_sin_le_one _)) (heatTimeWeight_pos hω).le))
    (heatTimeWeight_moment_integrable ht hω 1)
    (Eventually.of_forall (fun p v _ => by
      convert (((hasDerivAt_id v).const_mul p).cos.mul_const (heatTimeWeight t ω p)) using 1
      simp only [id_eq]
      ring))
  exact hd.2.const_mul ((2 * Real.pi)⁻¹)

theorem heatTimeFirst_hasDerivAt {t ω : ℝ} (ht : 0 < t) (hω : 0 < ω) (u : ℝ) :
    HasDerivAt (heatTimeFirst t ω) (heatTimeSecond t ω u) u := by
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun v p => (-p * Real.sin (p * v)) * heatTimeWeight t ω p)
    (F' := fun v p => (-p ^ 2 * Real.cos (p * v)) * heatTimeWeight t ω p)
    (x₀ := u) (ε := 1) (μ := volume)
    (bound := fun p => |p| ^ 2 * heatTimeWeight t ω p)
    (by norm_num)
    (Eventually.of_forall (fun v =>
      (by fun_prop (disch := assumption) : Continuous (fun p => (-p * Real.sin (p * v)) * heatTimeWeight t ω p)).aestronglyMeasurable))
    (heatTimeSin_integrable ht hω u)
    ((by fun_prop (disch := assumption) : Continuous (fun p => (-p ^ 2 * Real.cos (p * u)) * heatTimeWeight t ω p)).aestronglyMeasurable)
    (Eventually.of_forall (fun p v _ => by
      simp only [norm_mul, Real.norm_eq_abs, abs_neg, abs_pow,
        abs_of_pos (heatTimeWeight_pos hω)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right (sq_nonneg |p|) (Real.abs_cos_le_one _)) (heatTimeWeight_pos hω).le))
    (heatTimeWeight_moment_integrable ht hω 2)
    (Eventually.of_forall (fun p v _ => by
      convert ((((hasDerivAt_id v).const_mul p).sin.const_mul (-p)).mul_const
        (heatTimeWeight t ω p)) using 1
      simp only [id_eq]
      ring))
  exact hd.2.const_mul ((2 * Real.pi)⁻¹)

theorem heatTimeCovariance_zero_pos {t ω : ℝ} (ht : 0 < t) (hω : 0 < ω) :
    0 < heatTimeCovariance t ω 0 := by
  simp only [heatTimeCovariance, mul_zero, Real.cos_zero, one_mul]
  apply mul_pos (by positivity)
  exact integral_pos_of_integrable_nonneg_nonzero (heatTimeWeight_continuous t hω)
    (by simpa only [pow_zero, one_mul] using heatTimeWeight_moment_integrable ht hω 0)
    (fun _ => (heatTimeWeight_pos hω).le) (heatTimeWeight_pos (p := 0) hω).ne'

theorem heatTimeSecond_zero_neg {t ω : ℝ} (ht : 0 < t) (hω : 0 < ω) :
    heatTimeSecond t ω 0 < 0 := by
  have hi : Integrable (fun p => p ^ 2 * heatTimeWeight t ω p) := by
    simpa only [sq_abs] using heatTimeWeight_moment_integrable ht hω 2
  have hp : 0 < ∫ p, p ^ 2 * heatTimeWeight t ω p :=
    integral_pos_of_integrable_nonneg_nonzero (x := (1 : ℝ))
      (by fun_prop (disch := assumption)) hi
      (fun p => mul_nonneg (sq_nonneg p) (heatTimeWeight_pos hω).le)
      (by simpa only [one_pow, one_mul] using (heatTimeWeight_pos (t := t) (p := 1) hω).ne')
  unfold heatTimeSecond
  simp only [mul_zero, Real.cos_zero, mul_one, neg_mul, integral_neg, mul_neg]
  exact neg_neg_of_pos (mul_pos (by positivity) hp)

def timeHankelDeterminant (f : ℝ → ℝ) (ε : ℝ) : ℝ :=
  f (2 * ε) * f (4 * ε) - f (3 * ε) ^ 2

def timeHankelFirst (f g : ℝ → ℝ) (ε : ℝ) : ℝ :=
  (g (2 * ε) * 2) * f (4 * ε) + f (2 * ε) * (g (4 * ε) * 4) -
    2 * f (3 * ε) * (g (3 * ε) * 3)

theorem hasDerivAt_scale_zero {f : ℝ → ℝ} {v : ℝ} (hf : HasDerivAt f v 0) (c : ℝ) :
    HasDerivAt (fun x : ℝ => f (c * x)) (v * c) 0 := by
  have hc : HasDerivAt f v (c * (0 : ℝ)) := by simpa only [mul_zero] using hf
  simpa only [Function.comp_def, id_eq, mul_one] using
    hc.comp 0 ((hasDerivAt_id (0 : ℝ)).const_mul c)

theorem timeHankelDeterminant_hasDerivAt {f g : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (ε : ℝ) :
    HasDerivAt (timeHankelDeterminant f) (timeHankelFirst f g ε) ε := by
  have h2 := (hf (2 * ε)).comp ε ((hasDerivAt_id ε).const_mul 2)
  have h3 := (hf (3 * ε)).comp ε ((hasDerivAt_id ε).const_mul 3)
  have h4 := (hf (4 * ε)).comp ε ((hasDerivAt_id ε).const_mul 4)
  convert (h2.mul h4).sub (h3.pow 2) using 1
  simp only [timeHankelFirst, Function.comp_def]
  ring

theorem timeHankelFirst_hasDerivAt_zero {f g : ℝ → ℝ} {v : ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : HasDerivAt g v 0) (hg0 : g 0 = 0) :
    HasDerivAt (timeHankelFirst f g) (2 * f 0 * v) 0 := by
  have h2f : HasDerivAt (fun x : ℝ => f (2 * x)) 0 0 := by
    simpa only [hg0, zero_mul] using hasDerivAt_scale_zero (hf 0) 2
  have h3f : HasDerivAt (fun x : ℝ => f (3 * x)) 0 0 := by
    simpa only [hg0, zero_mul] using hasDerivAt_scale_zero (hf 0) 3
  have h4f : HasDerivAt (fun x : ℝ => f (4 * x)) 0 0 := by
    simpa only [hg0, zero_mul] using hasDerivAt_scale_zero (hf 0) 4
  have h2g : HasDerivAt (fun x : ℝ => g (2 * x)) (v * 2) 0 :=
    hasDerivAt_scale_zero hg 2
  have h3g : HasDerivAt (fun x : ℝ => g (3 * x)) (v * 3) 0 :=
    hasDerivAt_scale_zero hg 3
  have h4g : HasDerivAt (fun x : ℝ => g (4 * x)) (v * 4) 0 :=
    hasDerivAt_scale_zero hg 4
  convert (((h2g.mul_const 2).mul h4f).add (h2f.mul (h4g.mul_const 4))).sub
    ((h3f.const_mul 2).mul (h3g.mul_const 3)) using 1
  simp only [mul_zero, hg0, zero_mul, add_zero, zero_add]
  ring

/-- A positive covariance with vanishing first derivative and negative second
derivative at zero has an actual negative positive-time two-point determinant. -/
theorem timeHankelDeterminant_negative_near_zero {f g : ℝ → ℝ} {v : ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : HasDerivAt g v 0)
    (hf0 : 0 < f 0) (hg0 : g 0 = 0) (hv : v < 0) :
    ∃ δ > 0, ∀ ε, 0 < ε → ε < δ → timeHankelDeterminant f ε < 0 := by
  apply negative_near_zero_of_negative_second_derivative
    (timeHankelDeterminant_hasDerivAt hf)
  · simp [timeHankelDeterminant, pow_two]
  · simp [timeHankelFirst, hg0]
  · exact timeHankelFirst_hasDerivAt_zero hf hg hg0
  · exact mul_neg_of_pos_of_neg (by positivity) hv

/-- The Hankel determinant of the literal heat-damped Fourier cosine covariance
is negative for every sufficiently small positive probe spacing. -/
theorem heatTimeCovariance_negative_hankel {t ω : ℝ} (ht : 0 < t) (hω : 0 < ω) :
    ∃ δ > 0, ∀ ε, 0 < ε → ε < δ →
      heatTimeCovariance t ω (2 * ε) * heatTimeCovariance t ω (4 * ε) -
        heatTimeCovariance t ω (3 * ε) ^ 2 < 0 := by
  exact timeHankelDeterminant_negative_near_zero
    (heatTimeCovariance_hasDerivAt ht hω) (heatTimeFirst_hasDerivAt ht hω 0)
    (heatTimeCovariance_zero_pos ht hω) (heatTimeFirst_zero t ω) (heatTimeSecond_zero_neg ht hω)

def heatTimeFourierCovariance (t ω u : ℝ) : ℂ :=
  ((2 * Real.pi)⁻¹ : ℝ) * ∫ p : ℝ,
    Complex.exp ((p * u : ℝ) * Complex.I) * (heatTimeWeight t ω p : ℂ)

theorem heatTimeFourierIntegrand_integrable {t ω : ℝ}
    (ht : 0 < t) (hω : 0 < ω) (u : ℝ) :
    Integrable (fun p : ℝ => Complex.exp ((p * u : ℝ) * Complex.I) *
      (heatTimeWeight t ω p : ℂ)) := by
  apply (heatTimeWeight_moment_integrable ht hω 0).mono'
  · exact (by fun_prop (disch := assumption) : Continuous (fun p : ℝ =>
      Complex.exp ((p * u : ℝ) * Complex.I) * (heatTimeWeight t ω p : ℂ))).aestronglyMeasurable
  · filter_upwards with p
    simp [Complex.norm_exp, abs_of_pos (heatTimeWeight_pos hω)]

theorem heatTimeSineIntegral_zero (t ω u : ℝ) :
    (∫ p, Real.sin (p * u) * heatTimeWeight t ω p) = 0 := by
  have he : (∫ p, Real.sin (p * u) * heatTimeWeight t ω p) =
      -(∫ p, Real.sin (p * u) * heatTimeWeight t ω p) := by
    calc
      _ = ∫ p, Real.sin ((-p) * u) * heatTimeWeight t ω (-p) :=
        (integral_neg_eq_self (fun p => Real.sin (p * u) * heatTimeWeight t ω p) volume).symm
      _ = _ := by simp [heatTimeWeight, neg_mul, integral_neg]
  linarith

/-- The cosine representation equals the literal complex Fourier integral:
the imaginary sine term vanishes by oddness. -/
theorem heatTimeFourierCovariance_eq_real {t ω : ℝ}
    (ht : 0 < t) (hω : 0 < ω) (u : ℝ) :
    heatTimeFourierCovariance t ω u = (heatTimeCovariance t ω u : ℂ) := by
  have hi := heatTimeFourierIntegrand_integrable ht hω u
  have he : (∫ p : ℝ, Complex.exp ((p * u : ℝ) * Complex.I) *
      (heatTimeWeight t ω p : ℂ)) =
        ((∫ p, Real.cos (p * u) * heatTimeWeight t ω p) : ℝ) := by
    apply Complex.ext
    · simpa [RCLike.re_to_complex, Complex.exp_re] using (integral_re hi).symm
    · simpa [RCLike.im_to_complex, Complex.exp_im, heatTimeSineIntegral_zero] using
        (integral_im hi).symm
  unfold heatTimeFourierCovariance heatTimeCovariance
  rw [he]
  norm_cast

def heatTimeHankelMatrix (t ω ε : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![heatTimeCovariance t ω (2 * ε), heatTimeCovariance t ω (3 * ε);
    heatTimeCovariance t ω (3 * ε), heatTimeCovariance t ω (4 * ε)]

/-- The actual covariance violates positivity already on the two positive
point probes at ε and 2ε. Smooth test-function approximation is separate. -/
theorem heatTimeHankelMatrix_not_posSemidef {t ω : ℝ} (ht : 0 < t) (hω : 0 < ω) :
    ∃ δ > 0, ∀ ε, 0 < ε → ε < δ → ¬ (heatTimeHankelMatrix t ω ε).PosSemidef := by
  obtain ⟨δ, hδ, hd⟩ := heatTimeCovariance_negative_hankel ht hω
  refine ⟨δ, hδ, fun ε hε hεδ hp => ?_⟩
  have hn := hp.det_nonneg
  have hd' := hd ε hε hεδ
  simp only [heatTimeHankelMatrix, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hn
  nlinarith

def heatTimeFourierHankelMatrix (t ω ε : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![heatTimeFourierCovariance t ω (2 * ε), heatTimeFourierCovariance t ω (3 * ε);
    heatTimeFourierCovariance t ω (3 * ε), heatTimeFourierCovariance t ω (4 * ε)]

open scoped ComplexOrder in
/-- The same finite positive-time obstruction, stated directly for the source's
complex Fourier integral rather than its equivalent cosine representation. -/
theorem heatTimeFourierHankelMatrix_not_posSemidef {t ω : ℝ} (ht : 0 < t) (hω : 0 < ω) :
    ∃ δ > 0, ∀ ε, 0 < ε → ε < δ → ¬ (heatTimeFourierHankelMatrix t ω ε).PosSemidef := by
  obtain ⟨δ, hδ, hd⟩ := heatTimeCovariance_negative_hankel ht hω
  refine ⟨δ, hδ, fun ε hε hεδ hp => ?_⟩
  have hn := (Complex.nonneg_iff.mp hp.det_nonneg).1
  have hd' := hd ε hε hεδ
  simp [heatTimeFourierHankelMatrix, Matrix.det_fin_two,
    heatTimeFourierCovariance_eq_real ht hω] at hn
  nlinarith

end UV
