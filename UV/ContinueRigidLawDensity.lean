import UV.ContinueRigidLawExact

/-! Density of the positive-jump part of the rigid-source compound Poisson measure. -/

noncomputable section

open MeasureTheory Set Real Filter ProbabilityTheory
open scoped ENNReal MeasureTheory

namespace UV.ContinueRigidLaw

theorem nonneg_jumpPower (η : Measure ℝ) [IsFiniteMeasure η]
    (hη : ∀ᵐ y ∂η, 0 ≤ y) (n : ℕ) : ∀ᵐ y ∂jumpPower η n, 0 ≤ y := by
  induction n with
  | zero =>
      change ∀ᵐ y ∂Measure.dirac (0 : ℝ), 0 ≤ y
      exact (ae_dirac_iff (p := fun x : ℝ ↦ 0 ≤ x) measurableSet_Ici).2 le_rfl
  | succ n hn =>
      change ∀ᵐ y ∂(jumpPower η n ∗ η), 0 ≤ y
      exact conv_nonneg hn hη

/-- Convolving a finite measure with a density gives an average of translates. -/
def translatedDensity (μ : Measure ℝ) (f : ℝ → ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, f (y-x) ∂μ

theorem measurable_translatedDensity (μ : Measure ℝ) [SFinite μ] {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) : Measurable (translatedDensity μ f) :=
  (hf.comp (measurable_fst.sub measurable_snd)).lintegral_prod_right'

theorem conv_withDensity_eq (μ : Measure ℝ) [SFinite μ] {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    μ ∗ (volume : Measure ℝ).withDensity f = volume.withDensity (translatedDensity μ f) := by
  refine Measure.ext_of_lintegral _ fun g hg ↦ ?_
  rw [Measure.lintegral_conv hg, lintegral_withDensity_eq_lintegral_mul _
    (measurable_translatedDensity μ hf) hg]
  change (∫⁻ x, ∫⁻ y, g (x+y) ∂volume.withDensity f ∂μ) =
    ∫⁻ y, translatedDensity μ f y * g y ∂volume
  calc
    _ = ∫⁻ x, (∫⁻ y, f y * g (x+y) ∂volume) ∂μ := by
      apply lintegral_congr
      intro x
      exact lintegral_withDensity_eq_lintegral_mul _ hf (hg.comp (by fun_prop))
    _ = ∫⁻ x, (∫⁻ y, f (y-x) * g y ∂volume) ∂μ := by
      apply lintegral_congr
      intro x
      have hh := lintegral_add_left_eq_self (μ := (volume : Measure ℝ))
        (fun y ↦ f (y-x) * g y) x
      simpa only [add_comm x, add_sub_cancel_right] using hh
    _ = ∫⁻ y, (∫⁻ x, f (y-x) * g y ∂μ) ∂volume := by
      exact lintegral_lintegral_swap (f := fun x y ↦ f (y-x) * g y)
        ((hf.comp (measurable_snd.sub measurable_fst)).mul (hg.comp measurable_snd)).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro y
      have hm : Measurable (fun x : ℝ ↦ f (y-x)) := hf.comp (by fun_prop)
      exact lintegral_mul_const _ hm

/-- Density from the strictly positive jump counts of the Poisson series. -/
def positiveJumpDensity (f : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  let η := (volume : Measure ℝ).withDensity f
  ∑' n : ℕ, ENNReal.ofReal (exp (-(η.real univ)) / (n+1).factorial) *
    translatedDensity (jumpPower η n) f x

theorem measurable_positiveJumpDensity {f : ℝ → ℝ≥0∞}
    [IsFiniteMeasure ((volume : Measure ℝ).withDensity f)] (hf : Measurable f) :
    Measurable (positiveJumpDensity f) := by
  apply Measurable.ennreal_tsum
  intro n
  haveI := finite_jumpPower ((volume : Measure ℝ).withDensity f) n
  exact measurable_const.mul (measurable_translatedDensity _ hf)

private theorem compoundPoisson_split (η : Measure ℝ) :
    compoundPoisson η = ENNReal.ofReal (exp (-(η.real univ))) • Measure.dirac 0 +
      Measure.sum (fun n : ℕ ↦ ENNReal.ofReal (exp (-(η.real univ)) / (n+1).factorial) •
        jumpPower η (n+1)) := by
  apply Measure.ext
  intro s hs
  let h (n : ℕ) := (ENNReal.ofReal (exp (-(η.real univ)) / n.factorial) • jumpPower η n) s
  have h₀ : h 0 = (ENNReal.ofReal (exp (-(η.real univ))) • Measure.dirac 0) s := by
    simp only [h, Nat.factorial_zero, Nat.cast_one, div_one, jumpPower]
  have hh : (∑' n : ℕ, h n) = h 0 + ∑' n : ℕ, h (n+1) :=
    tsum_eq_zero_add' (f := h) ENNReal.summable
  rw [compoundPoisson, Measure.sum_apply _ hs, Measure.add_apply _ _ s,
    Measure.sum_apply _ hs]
  exact hh.trans (congrArg (fun z : ℝ≥0∞ ↦ z + ∑' n : ℕ, h (n+1)) h₀)

private theorem positiveJumpMeasure_eq_density {η : Measure ℝ} [IsFiniteMeasure η]
    {f : ℝ → ℝ≥0∞} (hη : η = volume.withDensity f) (hf : Measurable f) :
    Measure.sum (fun n : ℕ ↦ ENNReal.ofReal (exp (-(η.real univ)) / (n+1).factorial) •
        jumpPower η (n+1)) =
      volume.withDensity (fun x ↦ ∑' n : ℕ,
        ENNReal.ofReal (exp (-(η.real univ)) / (n+1).factorial) *
          translatedDensity (jumpPower η n) f x) := by
  let g (n : ℕ) := fun x : ℝ ↦ ENNReal.ofReal (exp (-(η.real univ)) / (n+1).factorial) *
    translatedDensity (jumpPower η n) f x
  have hm (n : ℕ) : Measurable (g n) := by
    haveI := finite_jumpPower η n
    exact measurable_const.mul (measurable_translatedDensity _ hf)
  have hg : (fun x : ℝ ↦ ∑' n : ℕ, g n x) = ∑' n, g n := by
    ext x
    exact (tsum_apply (Pi.summable.2 fun _ ↦ ENNReal.summable)).symm
  change _ = volume.withDensity (fun x : ℝ ↦ ∑' n : ℕ, g n x)
  rw [hg, withDensity_tsum hm]
  apply congrArg Measure.sum
  funext n
  haveI := finite_jumpPower η n
  have hconv : jumpPower η (n+1) = volume.withDensity (translatedDensity (jumpPower η n) f) := by
    change jumpPower η n ∗ η = _
    conv_lhs => arg 2; rw [hη]
    exact conv_withDensity_eq _ hf
  rw [hconv, ← withDensity_smul _ (measurable_translatedDensity _ hf)]
  rfl

theorem compoundPoisson_eq_atom_add_density {f : ℝ → ℝ≥0∞}
    [IsFiniteMeasure ((volume : Measure ℝ).withDensity f)] (hf : Measurable f) :
    let η := (volume : Measure ℝ).withDensity f
    compoundPoisson η = ENNReal.ofReal (exp (-(η.real univ))) • Measure.dirac 0 +
      volume.withDensity (positiveJumpDensity f) := by
  intro η
  rw [compoundPoisson_split, positiveJumpMeasure_eq_density (η := η) rfl hf]
  rfl

theorem positiveJumpDensity_of_nonpos {f : ℝ → ℝ≥0∞}
    [IsFiniteMeasure ((volume : Measure ℝ).withDensity f)] (hf : ∀ x ≤ 0, f x = 0)
    {x : ℝ} (hx : x ≤ 0) : positiveJumpDensity f x = 0 := by
  let η := (volume : Measure ℝ).withDensity f
  have hs : ∀ᵐ y ∂η, 0 ≤ y := by
    rw [ae_iff]
    simp only [not_le]
    change ((volume : Measure ℝ).withDensity f) (Iio 0) = 0
    rw [withDensity_apply _ measurableSet_Iio,
      setLIntegral_congr_fun (g := fun _ ↦ 0) measurableSet_Iio, lintegral_zero]
    intro y hy
    exact hf y hy.le
  unfold positiveJumpDensity
  have hzero (n : ℕ) : translatedDensity (jumpPower η n) f x = 0 := by
    unfold translatedDensity
    rw [lintegral_congr_ae ((nonneg_jumpPower η hs n).mono fun _ hy ↦ hf _ (by linarith))]
    exact lintegral_zero
  change (∑' n : ℕ, ENNReal.ofReal (exp (-(η.real univ)) / (n+1).factorial) *
    translatedDensity (jumpPower η n) f x) = 0
  simp only [hzero, mul_zero, tsum_zero]

private theorem jumpPower_mass (η : Measure ℝ) [IsFiniteMeasure η] (n : ℕ) :
    jumpPower η n univ = η univ ^ n := by
  rw [← laplaceTransform_zero, laplaceTransform_jumpPower, laplaceTransform_zero]

theorem positiveJumpDensity_le {f : ℝ → ℝ≥0∞}
    [IsFiniteMeasure ((volume : Measure ℝ).withDensity f)] {K : ℝ≥0∞}
    (hf : ∀ x, f x ≤ K) (x : ℝ) : positiveJumpDensity f x ≤ K := by
  let η := (volume : Measure ℝ).withDensity f
  let M := η.real univ
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hηM : ENNReal.ofReal M = η univ := ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hbound (n : ℕ) : translatedDensity (jumpPower η n) f x ≤ K * η univ ^ n := by
    calc
      _ ≤ ∫⁻ _ : ℝ, K ∂jumpPower η n := lintegral_mono fun y ↦ hf (x-y)
      _ = _ := by rw [lintegral_const, jumpPower_mass]
  have hcoeff (n : ℕ) :
      ENNReal.ofReal (exp (-M) / (n+1).factorial) * η univ ^ n ≤
        ENNReal.ofReal (exp (-M) * (M ^ n / n.factorial)) := by
    rw [← hηM, ← ENNReal.ofReal_pow hM, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hn : (n.factorial : ℝ) ≤ (n+1).factorial := by
      exact_mod_cast Nat.factorial_le (Nat.le_succ n)
    have hd := div_le_div_of_nonneg_left (mul_nonneg (exp_pos (-M)).le (pow_nonneg hM n))
      (by positivity : 0 < (n.factorial : ℝ)) hn
    calc
      _ = (exp (-M) * M^n) / (n+1).factorial := by ring
      _ ≤ (exp (-M) * M^n) / n.factorial := hd
      _ = _ := by ring
  have hs : Summable (fun n : ℕ ↦ M ^ n / (n.factorial : ℝ)) :=
    Real.summable_pow_div_factorial M
  have hexp : (∑' n : ℕ, M ^ n / (n.factorial : ℝ)) = exp M := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  unfold positiveJumpDensity
  change (∑' n : ℕ, ENNReal.ofReal (exp (-M) / (n+1).factorial) *
      translatedDensity (jumpPower η n) f x) ≤ K
  calc
    _ ≤ ∑' n : ℕ, K * ENNReal.ofReal (exp (-M) * (M ^ n / n.factorial)) := by
      apply ENNReal.tsum_le_tsum
      intro n
      calc
        _ ≤ ENNReal.ofReal (exp (-M) / (n+1).factorial) * (K * η univ ^ n) :=
          mul_le_mul_left' (hbound n) _
        _ = K * (ENNReal.ofReal (exp (-M) / (n+1).factorial) * η univ ^ n) := by ac_rfl
        _ ≤ _ := mul_le_mul_left' (hcoeff n) _
    _ = _ := by
      rw [ENNReal.tsum_mul_left,
        ← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) (hs.mul_left _),
        hs.tsum_mul_left, hexp, ← exp_add, neg_add_cancel, exp_zero, ENNReal.ofReal_one, mul_one]

end UV.ContinueRigidLaw
