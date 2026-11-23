import UV.ContinueRigidLawResidual
import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Group.Convolution

/-! The gamma and compound-Poisson emitted-energy laws of a rigid source.
These measure identities use nonnegative energy and the scalar rate measure on the
chosen reconstructed sector-plane. -/

noncomputable section

open MeasureTheory Set Real Filter ProbabilityTheory
open scoped ENNReal MeasureTheory

namespace UV.ContinueRigidLaw

/-- Laplace transform of a positive measure on emitted energy. -/
def laplaceTransform (μ : Measure ℝ) (τ : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, laplaceTest τ y ∂μ

theorem laplaceTransform_zero (μ : Measure ℝ) : laplaceTransform μ 0 = μ univ := by
  simp [laplaceTransform, laplaceTest]

theorem laplaceTransform_conv (μ η : Measure ℝ) [SFinite η] (τ : ℝ) :
    laplaceTransform (μ ∗ η) τ = laplaceTransform μ τ * laplaceTransform η τ := by
  simp only [laplaceTransform]
  rw [Measure.lintegral_conv (measurable_laplaceTest τ)]
  have hτ : ∀ x y, laplaceTest τ (x+y) = laplaceTest τ x * laplaceTest τ y := by
    intro x y
    unfold laplaceTest
    rw [← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
    congr 2
    ring
  simp_rw [hτ, lintegral_const_mul _ (measurable_laplaceTest τ),
    lintegral_mul_const _ (measurable_laplaceTest τ)]

theorem conv_nonneg {μ η : Measure ℝ} [SFinite η]
    (hμ : ∀ᵐ y ∂μ, 0 ≤ y) (hη : ∀ᵐ y ∂η, 0 ≤ y) :
    ∀ᵐ y ∂(μ ∗ η), 0 ≤ y := by
  unfold Measure.conv
  refine (ae_map_iff (by fun_prop) (by exact measurableSet_Ici)).2 ?_
  change ∀ᵐ p ∂(μ.prod η), 0 ≤ p.1 + p.2
  apply (Measure.ae_prod_iff_ae_ae (p := fun p : ℝ × ℝ ↦ 0 ≤ p.1 + p.2)
    (measurableSet_Ici.preimage (f := fun p : ℝ × ℝ ↦ p.1 + p.2) (by fun_prop))).2
  filter_upwards [hμ] with x hx
  filter_upwards [hη] with y hy
  exact add_nonneg hx hy

theorem laplaceTransform_le_mass {μ : Measure ℝ} (hμ : ∀ᵐ y ∂μ, 0 ≤ y)
    {τ : ℝ} (hτ : 0 ≤ τ) : laplaceTransform μ τ ≤ μ univ := by
  unfold laplaceTransform
  rw [← lintegral_one]
  apply lintegral_mono_ae
  filter_upwards [hμ] with y hy
  exact ENNReal.ofReal_le_one.mpr (exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hτ hy)))

/-- Convolution powers of the jump measure, with the zero-fold contribution at zero. -/
def jumpPower (η : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n+1 => jumpPower η n ∗ η

theorem finite_jumpPower (η : Measure ℝ) [IsFiniteMeasure η] (n : ℕ) :
    IsFiniteMeasure (jumpPower η n) := by
  induction n with
  | zero => change IsFiniteMeasure (Measure.dirac (0 : ℝ)); infer_instance
  | succ n hn => change IsFiniteMeasure (jumpPower η n ∗ η); infer_instance

theorem laplaceTransform_jumpPower (η : Measure ℝ) [SFinite η] (τ : ℝ) (n : ℕ) :
    laplaceTransform (jumpPower η n) τ = laplaceTransform η τ ^ n := by
  induction n with
  | zero => simp [jumpPower, laplaceTransform, lintegral_dirac, laplaceTest]
  | succ n hn => rw [jumpPower, laplaceTransform_conv, hn, pow_succ]

/-- The exponential series of positive convolution powers, normalized by its atom. -/
def compoundPoisson (η : Measure ℝ) : Measure ℝ :=
  Measure.sum (fun n : ℕ ↦ ENNReal.ofReal (exp (-(η.real univ)) / n.factorial) • jumpPower η n)

theorem laplaceTransform_compoundPoisson (η : Measure ℝ) [IsFiniteMeasure η]
    (hη : ∀ᵐ y ∂η, 0 ≤ y) {τ : ℝ} (hτ : 0 ≤ τ) :
    laplaceTransform (compoundPoisson η) τ =
      ENNReal.ofReal (exp ((laplaceTransform η τ).toReal - η.real univ)) := by
  have ht : laplaceTransform η τ ≠ ⊤ := ((laplaceTransform_le_mass hη hτ).trans_lt
    (measure_lt_top _ _)).ne
  set L := (laplaceTransform η τ).toReal
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hL' : ENNReal.ofReal L = laplaceTransform η τ := ENNReal.ofReal_toReal ht
  unfold laplaceTransform compoundPoisson
  rw [lintegral_sum_measure]
  simp only [lintegral_smul_measure, smul_eq_mul]
  change (∑' n : ℕ, ENNReal.ofReal (exp (-(η.real univ)) / n.factorial) *
      laplaceTransform (jumpPower η n) τ) = _
  have hc (n : ℕ) :
      ENNReal.ofReal (exp (-(η.real univ)) / n.factorial) * laplaceTransform (jumpPower η n) τ =
      ENNReal.ofReal (exp (-(η.real univ)) * (L ^ n / n.factorial)) := by
    rw [laplaceTransform_jumpPower, ← hL', ← ENNReal.ofReal_pow hL,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  simp_rw [hc]
  have hs : Summable (fun n : ℕ ↦ L ^ n / (n.factorial : ℝ)) := Real.summable_pow_div_factorial L
  have hexp : (∑' n : ℕ, L ^ n / (n.factorial : ℝ)) = exp L := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) (hs.mul_left _),
    hs.tsum_mul_left, hexp, ← exp_add]
  congr 2
  ring

theorem probability_compoundPoisson (η : Measure ℝ) [IsFiniteMeasure η]
    (hη : ∀ᵐ y ∂η, 0 ≤ y) : IsProbabilityMeasure (compoundPoisson η) := by
  constructor
  rw [← laplaceTransform_zero, laplaceTransform_compoundPoisson η hη le_rfl,
    laplaceTransform_zero, measureReal_def]
  simp

theorem nonneg_compoundPoisson (η : Measure ℝ) [IsFiniteMeasure η]
    (hη : ∀ᵐ y ∂η, 0 ≤ y) : ∀ᵐ y ∂compoundPoisson η, 0 ≤ y := by
  have hpow : ∀ n, ∀ᵐ y ∂jumpPower η n, 0 ≤ y := by
    intro n
    induction n with
    | zero =>
        change ∀ᵐ y ∂Measure.dirac (0 : ℝ), 0 ≤ y
        exact (ae_dirac_iff (p := fun x : ℝ ↦ 0 ≤ x) measurableSet_Ici).2 le_rfl
    | succ n hn =>
        change ∀ᵐ y ∂(jumpPower η n ∗ η), 0 ≤ y
        exact conv_nonneg hn hη
  have hzero : ∀ n, jumpPower η n (Iio 0) = 0 := by
    intro n
    simpa only [ae_iff, not_le] using hpow n
  rw [ae_iff]
  simp only [not_le]
  change compoundPoisson η (Iio 0) = 0
  rw [compoundPoisson, Measure.sum_apply _ measurableSet_Iio]
  simp [hzero]

theorem laplaceTransform_gamma {α B τ : ℝ} (hα : 0 < α) (hB : 0 < B) (hτ : 0 ≤ τ) :
    laplaceTransform (gammaMeasure α B) τ = ENNReal.ofReal ((B/(B+τ)) ^ α) := by
  unfold laplaceTransform gammaMeasure
  have hm (r : ℝ) : Measurable (gammaPDF α r) :=
    (measurable_gammaPDFReal α r).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ (hm B) (measurable_laplaceTest τ)]
  have hBt : 0 < B+τ := by linarith
  set c := (B/(B+τ)) ^ α
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have he (x : ℝ) : gammaPDF α B x * laplaceTest τ x =
      ENNReal.ofReal c * gammaPDF α (B+τ) x := by
    by_cases hx : 0 ≤ x
    · rw [gammaPDF_of_nonneg hx, gammaPDF_of_nonneg hx, laplaceTest,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ B^α / Gamma α * x^(α-1) * exp (-(B*x))),
        ← ENNReal.ofReal_mul hc]
      congr 1
      dsimp only [c]
      rw [div_rpow hB.le hBt.le]
      calc
        _ = B^α / Gamma α * x^(α-1) * (exp (-(B*x)) * exp (-(τ*x))) := by ring
        _ = _ := by
          rw [← exp_add, show -(B*x) + -(τ*x) = -((B+τ)*x) by ring]
          field_simp [ne_of_gt (rpow_pos_of_pos hBt α)]
    · simp [gammaPDF_of_neg (not_le.mp hx)]
  change (∫⁻ y, gammaPDF α B y * laplaceTest τ y) = _
  simp_rw [he]
  rw [lintegral_const_mul _ (hm _), lintegral_gammaPDF_eq_one hα hBt, mul_one]

/-- The scalar emitted-energy law at positive soft exponent, before threshold translation. -/
def emittedEnergyLaw (ν : Measure ℝ) (B : ℝ) : Measure ℝ :=
  gammaMeasure (ν.real univ) B ∗ compoundPoisson (residualMeasure ν B)

theorem emittedEnergyLaw_absolutelyContinuous (ν : Measure ℝ) (B b₀ : ℝ)
    [IsFiniteMeasure ν] (hb₀ : 0 < b₀) (hB : b₀ ≤ B)
    (hν : ∀ᵐ b ∂ν, b₀ ≤ b ∧ b ≤ B) (hα : 0 < ν.real univ) :
    emittedEnergyLaw ν B ≪ (volume : Measure ℝ) := by
  haveI := finite_residualMeasure ν hb₀ hB hν
  have hη : ∀ᵐ y ∂residualMeasure ν B, 0 ≤ y := by
    have h : residualMeasure ν B (Iio 0) = 0 :=
      measure_mono_null Iio_subset_Iic_self (residualMeasure_below ν B)
    simpa only [ae_iff, not_le] using h
  haveI := probability_compoundPoisson _ hη
  haveI := isProbabilityMeasure_gammaMeasure hα (hb₀.trans_le hB)
  rw [emittedEnergyLaw, Measure.conv_comm]
  exact Measure.conv_absolutelyContinuous (withDensity_absolutelyContinuous _ _)

/-- The scalar emitted-energy law has no atom, at the threshold or elsewhere. -/
theorem emittedEnergyLaw_noAtom (ν : Measure ℝ) (B b₀ : ℝ) [IsFiniteMeasure ν]
    (hb₀ : 0 < b₀) (hB : b₀ ≤ B)
    (hν : ∀ᵐ b ∂ν, b₀ ≤ b ∧ b ≤ B) (hα : 0 < ν.real univ) (x : ℝ) :
    emittedEnergyLaw ν B {x} = 0 :=
  emittedEnergyLaw_absolutelyContinuous ν B b₀ hb₀ hB hν hα (measure_singleton _)

end UV.ContinueRigidLaw
