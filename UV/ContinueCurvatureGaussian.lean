import UV.ResumeCurvatureRawLaw
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Centered Gaussian laws of the actual raw signed-mode Schwartz readouts.
The characteristic functions use the standard preparation's variance 1/2,
and the physical variance is recovered after the source rescaling. -/

noncomputable section

open MeasureTheory Filter Real ProbabilityTheory
open scoped BigOperators Topology NNReal

namespace UV.ContinueCurvatureGaussian

open UV.NextCurvatureLaw UV.ExtendCurvaturePotential
open UV.ResumeCurvatureDistributions UV.ResumeCurvatureRawLaw UV.ResumeCurvatureRawIdentity
open UV.ResumeCurvatureRawBounds UV.FurtherCurvatureLine
open UV.RevisionCurvatureDeterminant (latticeFrequency)

local instance : MeasurableSpace RawDistribution := cylinderSpace

theorem sourceGaussianBase_eq_gaussianReal :
    sourceGaussianBase = gaussianReal 0 (1/2 : ℝ≥0) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num)]
  unfold sourceGaussianBase gaussianPDF gaussianPDFReal
  congr 1
  funext x
  congr 1
  have ha : (2 : ℝ) * π * ((1/2 : ℝ≥0) : ℝ) = π := by norm_num; ring
  have hb : (2 : ℝ) * ((1/2 : ℝ≥0) : ℝ) = 1 := by norm_num
  rw [ha, hb, sub_zero, div_one, div_eq_mul_inv, mul_comm]

private def phase (t x : ℝ) : ℂ := Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)

private theorem phase_continuous (t : ℝ) : Continuous (phase t) := by
  unfold phase
  fun_prop

private theorem phase_norm (t x : ℝ) : ‖phase t x‖ = 1 := by
  unfold phase
  rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]

private theorem integral_phase_gaussianBase (t w : ℝ) :
    (∫ x, phase t (w*x) ∂sourceGaussianBase) = Complex.exp (-(w : ℂ)^2 * (t : ℂ)^2/4) := by
  have he : (fun x : ℝ => phase t (w*x)) = fun x => phase (t*w) x := by
    funext x
    unfold phase
    push_cast
    ring_nf
  rw [he, sourceGaussianBase_eq_gaussianReal]
  change (∫ x, Complex.exp (((t*w : ℝ) : ℂ) * (x:ℂ) * Complex.I)
      ∂gaussianReal 0 (1/2 : ℝ≥0)) = _
  rw [← charFun_apply_real, charFun_gaussianReal]
  congr 1
  push_cast
  norm_num
  ring

def finiteLinear {n : ℕ} (s : Finset (ModeSlot n)) (w X : ModeSlot n → ℝ) : ℝ :=
  ∑ i ∈ s, w i * X i

theorem finiteLinear_measurable {n : ℕ} (s : Finset (ModeSlot n)) (w : ModeSlot n → ℝ) :
    Measurable (finiteLinear s w) := by
  unfold finiteLinear
  apply Finset.measurable_sum
  intro i _
  exact (show Measurable (fun X : ModeSlot n → ℝ => X i) from
    measurable_pi_apply i).const_mul (w i)

private theorem finite_phase_integral {n : ℕ} (s : Finset (ModeSlot n))
    (w : ModeSlot n → ℝ) (t : ℝ) :
    (∫ X, phase t (finiteLinear s w X) ∂commonGaussian n) =
      Complex.exp (-((∑ i ∈ s, w i ^ 2 : ℝ) : ℂ) * (t:ℂ)^2 / 4) := by
  let ν : Measure (s → ℝ) := Measure.pi (fun _ : s => sourceGaussianBase)
  have hp : MeasurePreserving s.restrict (commonGaussian n) ν :=
    ⟨Finset.measurable_restrict _, Measure.infinitePi_map_restrict _⟩
  let f (x : s → ℝ) : ℂ := phase t (∑ i : s, w i * x i)
  have hf : Measurable f := by unfold f; exact (phase_continuous t).measurable.comp (by fun_prop)
  have hmap : (∫ X, phase t (finiteLinear s w X) ∂commonGaussian n) = ∫ x, f x ∂ν := by
    rw [← hp.map_eq, integral_map hp.measurable.aemeasurable hf.aestronglyMeasurable]
    apply integral_congr_ae
    exact Eventually.of_forall fun X => by
      change phase t (∑ i ∈ s, w i * X i) = phase t (∑ i : s, w i.1 * X i.1)
      rw [Finset.sum_coe_sort (f := fun i => w i * X i)]
  have hprod (x : s → ℝ) : f x = ∏ i : s, phase t (w i * x i) := by
    unfold f phase
    rw [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul, Complex.exp_sum]
  rw [hmap]
  simp_rw [hprod]
  calc
    _ = ∏ i : s, ∫ x : ℝ, phase t (w i * x) ∂sourceGaussianBase :=
      integral_fintype_prod_eq_prod (fun i : s => fun x : ℝ => phase t (w i * x))
    _ = _ := by
      simp_rw [integral_phase_gaussianBase]
      rw [← Complex.exp_sum]
      congr 1
      rw [Finset.sum_coe_sort (f := fun i => -(w i : ℂ)^2 * (t:ℂ)^2 / 4)]
      push_cast
      rw [← Finset.sum_div, ← Finset.sum_mul, ← Finset.sum_neg_distrib]

/-- The Gaussian product determines the law of a summable-variance limit.
Almost-sure convergence of the finite readouts suffices since the
characteristic-function tests have unit modulus. -/
theorem gaussian_of_aemeasurable_cutoff_limit {n : ℕ}
    (s : ℝ → Finset (ModeSlot n)) (hs : Tendsto s atTop atTop)
    (w : ModeSlot n → ℝ) (Y : (ModeSlot n → ℝ) → ℝ) (hm : Measurable Y)
    (hv : Summable (fun i => w i ^ 2))
    (hlim : ∀ᵐ X ∂commonGaussian n,
      Tendsto (fun Λ : ℝ => finiteLinear (s Λ) w X) atTop (𝓝 (Y X))) :
    (commonGaussian n).map Y =
      gaussianReal 0 ⟨(∑' i, w i ^ 2)/2, div_nonneg (tsum_nonneg (fun _ => sq_nonneg _)) zero_le_two⟩ := by
  letI : IsProbabilityMeasure ((commonGaussian n).map Y) := Measure.isProbabilityMeasure_map hm.aemeasurable
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply_real]
  change (∫ y, phase t y ∂(commonGaussian n).map Y) = _
  rw [integral_map hm.aemeasurable (phase_continuous t).measurable.aestronglyMeasurable,
    charFun_gaussianReal]
  let Q (z : ℝ) := Complex.exp (-(z:ℂ) * (t:ℂ)^2 / 4)
  have hQ : Continuous Q := by unfold Q; fun_prop
  have hlim' : ∀ᵐ X ∂commonGaussian n,
      Tendsto (fun Λ : ℝ => phase t (finiteLinear (s Λ) w X)) atTop (𝓝 (phase t (Y X))) := by
    filter_upwards [hlim] with X hX
    exact (phase_continuous t).continuousAt.tendsto.comp hX
  have hD := tendsto_integral_filter_of_dominated_convergence
    (μ := commonGaussian n) (fun _ => (1:ℝ))
    (Eventually.of_forall fun Λ =>
      ((phase_continuous t).measurable.comp (finiteLinear_measurable (s Λ) w)).aestronglyMeasurable)
    (Eventually.of_forall fun _ => Eventually.of_forall fun _ => (phase_norm _ _).le)
    (integrable_const _) hlim'
  have hC : Tendsto (fun Λ : ℝ => ∫ X, phase t (finiteLinear (s Λ) w X) ∂commonGaussian n)
      atTop (𝓝 (Q (∑' i, w i ^ 2))) := by
    simp_rw [finite_phase_integral]
    exact hQ.continuousAt.tendsto.comp (hv.hasSum.comp hs)
  change (∫ X, phase t (Y X) ∂commonGaussian n) = _
  rw [tendsto_nhds_unique hD hC]
  unfold Q
  congr 1
  push_cast
  ring


abbrev ReadoutTests (n : ℕ) := Fin 2 → Fin n → SchwartzTest

def distributionReadout {n : ℕ} (φ : ReadoutTests n)
    (U : Fin 2 → Fin n → RawDistribution) : ℝ :=
  ∑ a, ∑ c, U a c (φ a c)

private theorem raw_eval_measurable (φ : SchwartzTest) :
    Measurable (fun T : RawDistribution => T φ) :=
  (measurable_pi_apply φ).comp
    (show Measurable (fun T : RawDistribution => fun ψ : SchwartzTest => T ψ) from
      measurable_iff_comap_le.mpr le_rfl)

theorem distributionReadout_measurable {n : ℕ} (φ : ReadoutTests n) :
    Measurable (distributionReadout φ) := by
  unfold distributionReadout
  apply Finset.measurable_sum
  intro a _
  apply Finset.measurable_sum
  intro c _
  exact (raw_eval_measurable (φ a c)).comp
    ((measurable_pi_apply c).comp (measurable_pi_apply a))

def weightedReadout {n : ℕ} (ℓ : ℝ) (φ : ReadoutTests n) (X : ModeSlot n → ℝ) : ℝ :=
  distributionReadout φ (fun a c => rawSample ℓ a c X)

private theorem jointSample_measurable {n : ℕ} (ℓ : ℝ) :
    Measurable (fun (X : ModeSlot n → ℝ) a c => rawSample ℓ a c X) := by
  apply measurable_pi_lambda
  intro a
  apply measurable_pi_lambda
  intro c
  exact rawSample_measurable ℓ a c

private def readoutWeight {n : ℕ} (ℓ : ℝ) (φ : ReadoutTests n) (i : ModeSlot n) : ℝ :=
  sqrt (2 * curvatureCovariance ℓ i.1) * modeTestPair i.1 (φ i.2.1 i.2.2)

private def readoutSlots {n : ℕ} (Λ : ℝ) : Finset (ModeSlot n) :=
  (retainedModes Λ).product Finset.univ

private theorem readoutSlots_cofinal {n : ℕ} :
    Tendsto (readoutSlots (n := n)) atTop atTop := by
  refine tendsto_atTop.mpr fun s => eventually_atTop.mpr ⟨∑ i ∈ s, latticeFrequency i.1, ?_⟩
  intro Λ hΛ i hi
  have hz : latticeFrequency i.1 ≤ Λ := (Finset.single_le_sum
    (f := fun j : ModeSlot n => latticeFrequency j.1) (fun _ _ => sqrt_nonneg _) hi).trans hΛ
  exact Finset.mem_product.mpr ⟨(mem_retainedModes Λ i.1).mpr hz, Finset.mem_univ _⟩

private theorem readoutCutoff_eq {n : ℕ} (Λ ℓ : ℝ) (φ : ReadoutTests n) (X : ModeSlot n → ℝ) :
    finiteLinear (readoutSlots Λ) (readoutWeight ℓ φ) X =
      ∑ a, ∑ c, cutoffRawDistribution Λ ℓ X a c (φ a c) := by
  have he (k : MeanZeroMode) (j : Fin 2 × Fin n) :
      readoutWeight ℓ φ (k,j) * X (k,j) =
        depthRescale ℓ X (k,j) * modeTestPair k (φ j.1 j.2) := by
    unfold depthRescale readoutWeight
    ring
  calc
    _ = ∑ j : Fin 2 × Fin n, ∑ k ∈ retainedModes Λ, readoutWeight ℓ φ (k,j) * X (k,j) :=
      Finset.sum_product_right (retainedModes Λ) (Finset.univ : Finset (Fin 2 × Fin n))
        (fun i : ModeSlot n => readoutWeight ℓ φ i * X i)
    _ = _ := by simp_rw [cutoffRawDistribution_eq_mode_pair_sum, he, Fintype.sum_prod_type]

private theorem readoutCutoff_limit {n : ℕ} (ℓ : ℝ) (φ : ReadoutTests n) :
    ∀ᵐ X ∂commonGaussian n, Tendsto (fun Λ : ℝ =>
      finiteLinear (readoutSlots Λ) (readoutWeight ℓ φ) X) atTop (𝓝 (weightedReadout ℓ φ X)) := by
  have he : ∀ᵐ X ∂commonGaussian n, ∀ a c,
      rawSample ℓ a c X = fullRawDistribution ℓ X a c := by
    simp only [eventually_countable_forall]
    exact fun a c => rawSample_ae_eq ℓ a c
  filter_upwards [he, ae_rawDistribution_weak_limit n] with X hX hlim
  unfold weightedReadout distributionReadout
  simp_rw [readoutCutoff_eq, hX]
  apply tendsto_finset_sum
  intro a _
  apply tendsto_finset_sum
  intro c _
  exact hlim ℓ a c (φ a c)

private theorem covariance_nonneg (ℓ : ℝ) (k : MeanZeroMode) :
    0 ≤ curvatureCovariance ℓ k := by unfold curvatureCovariance; positivity

private theorem rescaleFactor_bound (ℓ : ℝ) (k : MeanZeroMode) :
    sqrt (2 * curvatureCovariance ℓ k) ≤ 2 := by
  have hr : 1 ≤ latticeFrequency k := by
    have hi : (1:ℝ) ≤ (UV.FurtherCurvatureShell.latticeHeight k : ℝ) :=
      Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (UV.FurtherCurvatureShell.latticeHeight_ne_zero k.2))
    exact hi.trans (UV.FurtherCurvatureShell.latticeHeight_le_latticeFrequency k)
  have hc : (latticeFrequency k ^ 2)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ hr)
  apply (sqrt_le_left zero_le_two).2
  linarith [(mode_covariance_le_boundary ℓ k).trans hc]

private theorem modeTestPair_bound (k : MeanZeroMode) (ψ : SchwartzTest) :
    |modeTestPair k ψ| ≤
      (‖testPeriodicPair (ellipticTestCube ψ)‖ * sqrt 2) * rawRegularization k := by
  let A := (1 + latticeFrequency k ^ 2)^3
  have hA : 0 < A := by dsimp [A]; positivity
  have hb : |modeTestPair k (ellipticTestCube ψ)| ≤
      ‖testPeriodicPair (ellipticTestCube ψ)‖ * sqrt 2 := by
    rw [← Real.norm_eq_abs]
    unfold modeTestPair
    exact ((testPeriodicPair _).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (realTorusMode_norm_bound k) (norm_nonneg _))
  rw [mode_elliptic_pair, abs_mul, abs_of_nonneg hA.le] at hb
  unfold rawRegularization
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hA).2
  simpa only [mul_comm] using hb

private theorem readoutWeight_abs_summable {n : ℕ} (ℓ : ℝ) (φ : ReadoutTests n) :
    Summable (fun i => |readoutWeight ℓ φ i|) := by
  let A (j : Fin 2 × Fin n) := ‖testPeriodicPair (ellipticTestCube (φ j.1 j.2))‖ * sqrt 2
  let C := ∑ j, A j
  have hA (j : Fin 2 × Fin n) : 0 ≤ A j := by dsimp [A]; positivity
  have hC (j : Fin 2 × Fin n) : A j ≤ C :=
    Finset.single_le_sum (fun k _ => hA k) (Finset.mem_univ _)
  have hs : Summable (fun i : ModeSlot n => rawRegularization i.1) := by
    apply (summable_prod_of_nonneg (fun i : ModeSlot n => rawRegularization_nonneg i.1)).2
    refine ⟨fun _ => summable_of_finite_support (Set.toFinite _), ?_⟩
    simp only [tsum_fintype, Finset.sum_const, nsmul_eq_mul]
    exact rawRegularization_summable.mul_left _
  apply (hs.mul_left (2*C)).of_nonneg_of_le (fun _ => abs_nonneg _)
  intro i
  unfold readoutWeight
  rw [abs_mul, abs_of_nonneg (sqrt_nonneg _), mul_assoc]
  exact mul_le_mul (rescaleFactor_bound ℓ i.1)
    ((modeTestPair_bound _ _).trans
      (mul_le_mul_of_nonneg_right (hC i.2) (rawRegularization_nonneg _)))
    (abs_nonneg _) zero_le_two

private theorem readoutWeight_sq_summable {n : ℕ} (ℓ : ℝ) (φ : ReadoutTests n) :
    Summable (fun i => readoutWeight ℓ φ i ^ 2) := by
  have hs := readoutWeight_abs_summable ℓ φ
  let C := ∑' i, |readoutWeight ℓ φ i|
  apply (hs.mul_left C).of_nonneg_of_le (fun _ => sq_nonneg _)
  intro i
  have hc : |readoutWeight ℓ φ i| ≤ C :=
    hs.le_tsum i (fun j _ => abs_nonneg _)
  rw [← sq_abs, pow_two]
  exact mul_le_mul_of_nonneg_right hc (abs_nonneg (readoutWeight ℓ φ i))

def readoutVariance {n : ℕ} (ℓ : ℝ) (φ : ReadoutTests n) : ℝ≥0 :=
  ⟨∑' i : ModeSlot n, curvatureCovariance ℓ i.1 * modeTestPair i.1 (φ i.2.1 i.2.2)^2,
    tsum_nonneg fun i => mul_nonneg (covariance_nonneg ℓ i.1) (sq_nonneg _)⟩

theorem readout_variance_summable {n : ℕ} (ℓ : ℝ) (φ : ReadoutTests n) :
    Summable fun i : ModeSlot n =>
      curvatureCovariance ℓ i.1 * modeTestPair i.1 (φ i.2.1 i.2.2)^2 := by
  have h := (readoutWeight_sq_summable ℓ φ).div_const 2
  apply h.congr
  intro i
  unfold readoutWeight
  rw [mul_pow, Real.sq_sqrt (mul_nonneg zero_le_two (covariance_nonneg ℓ i.1))]
  ring

/-- Every real linear combination of Schwartz-test evaluations of the two
actual raw fields has centered Gaussian law, with the physical variance
computed from the signed modes and the original covariance. -/
theorem rawJointSchwartzReadout_gaussian {n : ℕ} (ℓ : ℝ) (φ : ReadoutTests n) :
    (rawJointCylinderLaw (n := n) ℓ).map (distributionReadout φ) =
      gaussianReal 0 (readoutVariance ℓ φ) := by
  unfold rawJointCylinderLaw
  rw [Measure.map_map (distributionReadout_measurable φ) (jointSample_measurable ℓ)]
  have h := gaussian_of_aemeasurable_cutoff_limit readoutSlots readoutSlots_cofinal
    (readoutWeight ℓ φ) (weightedReadout ℓ φ)
    ((distributionReadout_measurable φ).comp (jointSample_measurable ℓ))
    (readoutWeight_sq_summable ℓ φ) (readoutCutoff_limit ℓ φ)
  change (commonGaussian n).map (weightedReadout ℓ φ) = _
  rw [h]
  congr 1
  apply NNReal.eq
  change (∑' i, readoutWeight ℓ φ i ^ 2)/2 =
    ∑' i : ModeSlot n, curvatureCovariance ℓ i.1 * modeTestPair i.1 (φ i.2.1 i.2.2)^2
  rw [← tsum_div_const]
  apply tsum_congr
  intro i
  unfold readoutWeight
  rw [mul_pow, Real.sq_sqrt (mul_nonneg zero_le_two (covariance_nonneg ℓ i.1))]
  ring

end UV.ContinueCurvatureGaussian
