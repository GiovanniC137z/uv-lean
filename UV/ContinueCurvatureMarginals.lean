import UV.ExtendCurvatureMoments
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Algebra.MvPolynomial.Eval

/-! The normalized expectation calculus for the actual pushed-forward
finite-mode probability measures of the compact-torus bracket source. -/

noncomputable section

open MeasureTheory Filter Real
open scoped BigOperators Topology ENNReal NNReal

namespace UV.ContinueCurvatureMarginals

open UV.NextCurvatureLaw UV.ExtendCurvaturePotential
open UV.ExtendCurvatureGibbs UV.ExtendCurvatureMoments
open UV.FurtherCurvatureDeterminant UV.FurtherCurvatureShell
open UV.RevisionCurvatureDeterminant (relative_determinant_bounds latticeFrequency)

private theorem integral_weighted_pushforward_eq {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (ν : Measure Ω) (w : Ω → ℝ) (hwm : AEMeasurable w ν) (hw : 0 ≤ᵐ[ν] w)
    {Z : ℝ} (hZ : 0 < Z) (R : Ω → E) (hR : Measurable R) (F : E → ℝ) (hF : Measurable F) :
    (∫ y, F y ∂(ν.withDensity (fun p => ENNReal.ofReal (w p / Z))).map R) =
      (∫ p, w p * F (R p) ∂ν) / Z := by
  have hd : AEMeasurable (fun p => ENNReal.ofReal (w p / Z)) ν :=
    (hwm.div_const Z).ennreal_ofReal
  rw [integral_map hR.aemeasurable hF.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀ hd
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards [hw] with p hp
  change (ENNReal.ofReal (w p/Z)).toReal * F (R p) = w p * F (R p) / Z
  rw [ENNReal.toReal_ofReal (div_nonneg hp hZ.le)]
  ring

private theorem integrable_weighted_pushforward {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (ν : Measure Ω) (w : Ω → ℝ) (hwm : AEMeasurable w ν) (hw : 0 ≤ᵐ[ν] w)
    {Z : ℝ} (hZ : 0 < Z) (R : Ω → E) (hR : Measurable R) (F : E → ℝ) (hF : Measurable F)
    (h : Integrable (fun p => w p * F (R p)) ν) :
    Integrable F ((ν.withDensity (fun p => ENNReal.ofReal (w p / Z))).map R) := by
  rw [integrable_map_measure hF.aestronglyMeasurable hR.aemeasurable]
  have hd : AEMeasurable (fun p => ENNReal.ofReal (w p / Z)) ν :=
    (hwm.div_const Z).ennreal_ofReal
  rw [integrable_withDensity_iff_integrable_smul₀' hd
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply (h.div_const Z).congr
  filter_upwards [hw] with p hp
  change w p * F (R p) / Z = (ENNReal.ofReal (w p/Z)).toReal * F (R p)
  rw [ENNReal.toReal_ofReal (div_nonneg hp hZ.le)]
  ring

private theorem weighted_probability {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (w : Ω → ℝ) (h : Integrable w ν) (hw : 0 ≤ᵐ[ν] w) (hZ : 0 < ∫ p, w p ∂ν) :
    IsProbabilityMeasure (ν.withDensity fun p => ENNReal.ofReal (w p / ∫ q, w q ∂ν)) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (h.div_const _)
      (hw.mono fun _ hp => div_nonneg hp hZ.le),
    integral_div, div_self hZ.ne', ENNReal.ofReal_one]

def cutoffPartition {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) (g Λ : ℝ) : ℝ :=
  ∫ p, cutoffWeight B g Λ p ∂preparationMeasure n μ

theorem cutoffPartition_pos {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hpos : μ (Set.Ioi 0) ≠ 0)
    {g : ℝ} (hg : 0 ≤ g) (Λ : ℝ) : 0 < cutoffPartition B μ g Λ := by
  have hi := cutoffWeight_integrable B μ hg Λ
  have hs (p : Preparation n) : 0 < cutoffWeight B g Λ p := by
    unfold cutoffWeight
    exact mul_pos (relative_determinant_bounds (sphericalModes Λ) latticeFrequency p.1 n).1
      (exp_pos _)
  unfold cutoffPartition
  apply (integral_pos_iff_support_of_nonneg (fun p => (hs p).le) hi).2
  apply pos_iff_ne_zero.mpr
  have hmass : (preparationMeasure n μ) Set.univ = μ Set.univ := by
    unfold preparationMeasure
    have he : commonGaussian n Set.univ = 1 := measure_univ
    rw [← Set.univ_prod_univ, Measure.prod_prod, he, mul_one]
  rw [show Function.support (cutoffWeight B g Λ) = Set.univ by
    ext p
    simp [Function.mem_support, (hs p).ne'], hmass]
  exact fun h => hpos (measure_mono_null (Set.subset_univ _) h)

def cutoffGibbsMeasure {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) (g Λ : ℝ) : Measure (Preparation n) :=
  (preparationMeasure n μ).withDensity
    (fun p => ENNReal.ofReal (cutoffWeight B g Λ p / cutoffPartition B μ g Λ))

theorem cutoffGibbsMeasure_probability {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hpos : μ (Set.Ioi 0) ≠ 0)
    {g : ℝ} (hg : 0 ≤ g) (Λ : ℝ) :
    IsProbabilityMeasure (cutoffGibbsMeasure B μ g Λ) :=
  weighted_probability (preparationMeasure n μ) (cutoffWeight B g Λ)
    (cutoffWeight_integrable B μ hg Λ) (Eventually.of_forall fun p => (cutoffWeight_range B hg Λ p).1)
    (cutoffPartition_pos B μ hpos hg Λ)

def finiteModeLaw {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) (g : ℝ) (S : Finset (ModeSlot n)) : Measure (S → ℝ) :=
  (gibbsMeasure B μ g).map (fixedReadout S)

def cutoffModeLaw {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) (g Λ : ℝ) (S : Finset (ModeSlot n)) : Measure (S → ℝ) :=
  (cutoffGibbsMeasure B μ g Λ).map (cutoffReadout S Λ)

theorem finiteModeLaw_probability {n : ℕ} (hn : 0 < n) (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ)
    (hpos : μ (Set.Ioi 0) ≠ 0) {g : ℝ} (hg : 0 ≤ g) (S : Finset (ModeSlot n)) :
    IsProbabilityMeasure (finiteModeLaw B μ g S) := by
  letI := gibbsMeasure_probability hn B μ hμ hpos hg
  exact Measure.isProbabilityMeasure_map (fixedReadout_measurable S).aemeasurable

theorem cutoffModeLaw_probability {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hpos : μ (Set.Ioi 0) ≠ 0) {g : ℝ} (hg : 0 ≤ g)
    (Λ : ℝ) (S : Finset (ModeSlot n)) :
    IsProbabilityMeasure (cutoffModeLaw B μ g Λ S) := by
  letI := cutoffGibbsMeasure_probability B μ hpos hg Λ
  exact Measure.isProbabilityMeasure_map (cutoffReadout_measurable S Λ).aemeasurable

theorem integral_finiteModeLaw_eq {n : ℕ} (hn : 0 < n) (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ)
    (hpos : μ (Set.Ioi 0) ≠ 0) {g : ℝ} (hg : 0 ≤ g) (S : Finset (ModeSlot n))
    (F : (S → ℝ) → ℝ) (hF : Measurable F) :
    (∫ y, F y ∂finiteModeLaw B μ g S) =
      (∫ p, fullWeight B g p * F (fixedReadout S p) ∂preparationMeasure n μ) / partition B μ g :=
  integral_weighted_pushforward_eq (preparationMeasure n μ) (fullWeight B g)
    (fullWeight_aestronglyMeasurable hn B μ hμ hg).aemeasurable
    (Eventually.of_forall fun p => (fullWeight_range B hg p).1)
    (partition_pos_le hn B μ hμ hpos hg).1 (fixedReadout S) (fixedReadout_measurable S) F hF

theorem integral_cutoffModeLaw_eq {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hpos : μ (Set.Ioi 0) ≠ 0)
    {g : ℝ} (hg : 0 ≤ g) (Λ : ℝ) (S : Finset (ModeSlot n))
    (F : (S → ℝ) → ℝ) (hF : Measurable F) :
    (∫ y, F y ∂cutoffModeLaw B μ g Λ S) =
      (∫ p, cutoffWeight B g Λ p * F (cutoffReadout S Λ p) ∂preparationMeasure n μ) /
      cutoffPartition B μ g Λ :=
  integral_weighted_pushforward_eq (preparationMeasure n μ) (cutoffWeight B g Λ)
    (cutoffWeight_measurable B g Λ).aemeasurable
    (Eventually.of_forall fun p => (cutoffWeight_range B hg Λ p).1)
    (cutoffPartition_pos B μ hpos hg Λ) (cutoffReadout S Λ) (cutoffReadout_measurable S Λ) F hF

/-- Bounded measurable tests of each finite collection of modes converge
under the corresponding actual probability marginals. -/
theorem finiteModeLaw_bounded_integral_limit {n : ℕ} (hn : 0 < n) (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ)
    (hpos : μ (Set.Ioi 0) ≠ 0) {g : ℝ} (hg : 0 ≤ g) (S : Finset (ModeSlot n))
    (F : (S → ℝ) → ℝ) (hF : Measurable F) {C : ℝ} (hB : ∀ y, ‖F y‖ ≤ C) :
    Tendsto (fun Λ : ℝ => ∫ y, F y ∂cutoffModeLaw B μ g Λ S) atTop
      (𝓝 (∫ y, F y ∂finiteModeLaw B μ g S)) := by
  simp_rw [integral_cutoffModeLaw_eq B μ hpos hg _ S F hF,
    integral_finiteModeLaw_eq hn B μ hμ hpos hg S F hF, cutoffPartition]
  exact bounded_finite_observable_limit hn B μ hμ hpos hg S F hF hB

/-- The same finite-coordinate laws have finite continuum monomial
moments, and all of their finite-cutoff moments converge. -/
theorem finiteModeLaw_monomial_limit {n : ℕ} (hn : 0 < n) (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ)
    (hpos : μ (Set.Ioi 0) ≠ 0) {g : ℝ} (hg : 0 ≤ g) (S : Finset (ModeSlot n)) (powers : S → ℕ) :
    Integrable (monomial powers) (finiteModeLaw B μ g S) ∧
      Tendsto (fun Λ : ℝ => ∫ y, monomial powers y ∂cutoffModeLaw B μ g Λ S) atTop
        (𝓝 (∫ y, monomial powers y ∂finiteModeLaw B μ g S)) := by
  have hm := normalized_monomial_limit hn B μ hμ hpos hg S powers
  have hF : Measurable (monomial powers) := by unfold monomial; fun_prop
  constructor
  · exact integrable_weighted_pushforward (preparationMeasure n μ) (fullWeight B g)
      (fullWeight_aestronglyMeasurable hn B μ hμ hg).aemeasurable
      (Eventually.of_forall fun p => (fullWeight_range B hg p).1)
      (partition_pos_le hn B μ hμ hpos hg).1 (fixedReadout S) (fixedReadout_measurable S)
      (monomial powers) hF hm.1
  · simp_rw [integral_cutoffModeLaw_eq B μ hpos hg _ S (monomial powers) hF,
      integral_finiteModeLaw_eq hn B μ hμ hpos hg S (monomial powers) hF, cutoffPartition]
    exact hm.2

private theorem absBasePower_integrable (q : ℕ) :
    Integrable (fun x : ℝ => |x| ^ q) sourceGaussianBase := by
  have h := sourceGaussian_power_integrable (1/2 : ℝ) q
  have he : sourceGaussian (1/2 : ℝ) = sourceGaussianBase := by
    unfold sourceGaussian
    norm_num
  simpa only [he, norm_pow, Real.norm_eq_abs] using h.norm

private theorem uniform_variance_envelope {n : ℕ} (S : Finset (ModeSlot n))
    (Λ : ℝ) (p : Preparation n) (i : S) :
    ‖cutoffReadout S Λ p i‖ ≤ 2 * |p.2 i.1| := by
  unfold cutoffReadout
  split
  · unfold depthRescale
    rw [norm_mul, Real.norm_of_nonneg (sqrt_nonneg _), Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    have hr : 1 ≤ latticeFrequency i.1.1 := by
      have hi : (1 : ℝ) ≤ (latticeHeight i.1.1 : ℝ) :=
        Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (latticeHeight_ne_zero i.1.1.2))
      exact hi.trans (latticeHeight_le_latticeFrequency _)
    have hc : (latticeFrequency i.1.1 ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hr)
    apply (sqrt_le_left zero_le_two).2
    linarith [(mode_covariance_le_boundary p.1 i.1.1).trans hc]
  · rw [norm_zero]
    positivity

private theorem cutoffModeLaw_monomial_integrable {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hpos : μ (Set.Ioi 0) ≠ 0) {g : ℝ} (hg : 0 ≤ g)
    (Λ : ℝ) (S : Finset (ModeSlot n)) (powers : S → ℕ) :
    Integrable (monomial powers) (cutoffModeLaw B μ g Λ S) := by
  have hF : Measurable (monomial powers) := by unfold monomial; fun_prop
  apply integrable_weighted_pushforward (preparationMeasure n μ) (cutoffWeight B g Λ)
    (cutoffWeight_measurable B g Λ).aemeasurable
    (Eventually.of_forall fun p => (cutoffWeight_range B hg Λ p).1)
    (cutoffPartition_pos B μ hpos hg Λ) (cutoffReadout S Λ) (cutoffReadout_measurable S Λ)
    (monomial powers) hF
  let b (X : ModeSlot n → ℝ) := ∏ i : S, (2 * |X i.1|)^powers i
  have hp : MeasurePreserving S.restrict (commonGaussian n)
      (Measure.pi (fun _ : S => sourceGaussianBase)) :=
    ⟨Finset.measurable_restrict _, Measure.infinitePi_map_restrict _⟩
  let f (i : S) (x : ℝ) : ℝ := (2 * |x|)^powers i
  have hf (i : S) : Integrable (f i) sourceGaussianBase := by
    unfold f
    simp_rw [mul_pow]
    exact (absBasePower_integrable _).const_mul _
  have hbase : Integrable b (commonGaussian n) := by
    have hm := hp.integrable_comp_of_integrable (Integrable.fintype_prod hf)
    simpa only [b, f, Function.comp_def, Finset.restrict] using hm
  have hb : Integrable (fun p : Preparation n => b p.2) (preparationMeasure n μ) :=
    hbase.comp_snd μ
  refine hb.mono'
    (((cutoffWeight_measurable B g Λ).mul (hF.comp (cutoffReadout_measurable S Λ))).aestronglyMeasurable)
    (Eventually.of_forall fun p => ?_)
  rw [norm_mul, Real.norm_of_nonneg (cutoffWeight_range B hg Λ p).1]
  refine (mul_le_of_le_one_left (norm_nonneg _) (cutoffWeight_range B hg Λ p).2).trans ?_
  unfold b monomial
  rw [norm_prod]
  simp_rw [norm_pow]
  exact Finset.prod_le_prod (fun _ _ => by positivity)
    (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (uniform_variance_envelope S Λ p i) _)

/-- Every actual multivariate polynomial on the fixed finite mode set has
finite moments under both distributions and convergent spherical moments. -/
theorem finiteModeLaw_polynomial_limit {n : ℕ} (hn : 0 < n) (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ)
    (hpos : μ (Set.Ioi 0) ≠ 0) {g : ℝ} (hg : 0 ≤ g) (S : Finset (ModeSlot n))
    (P : MvPolynomial S ℝ) :
    (∀ Λ : ℝ, Integrable (fun y => MvPolynomial.eval y P) (cutoffModeLaw B μ g Λ S)) ∧
    Integrable (fun y => MvPolynomial.eval y P) (finiteModeLaw B μ g S) ∧
      Tendsto (fun Λ : ℝ => ∫ y, MvPolynomial.eval y P ∂cutoffModeLaw B μ g Λ S) atTop
        (𝓝 (∫ y, MvPolynomial.eval y P ∂finiteModeLaw B μ g S)) := by
  have hpoly (x : S → ℝ) : MvPolynomial.eval x P =
      ∑ d ∈ P.support, P.coeff d * monomial d x := MvPolynomial.eval_eq' x P
  have hint (ν : Measure (S → ℝ)) (h : ∀ p : S → ℕ, Integrable (monomial p) ν) :
      Integrable (fun y => MvPolynomial.eval y P) ν := by
    simp_rw [hpoly]
    exact integrable_finset_sum _ (fun d _ => (h d).const_mul _)
  have hsum (ν : Measure (S → ℝ)) (h : ∀ p : S → ℕ, Integrable (monomial p) ν) :
      (∫ y, MvPolynomial.eval y P ∂ν) =
        ∑ d ∈ P.support, P.coeff d * ∫ y, monomial d y ∂ν := by
    simp_rw [hpoly]
    calc
      _ = ∑ d ∈ P.support, ∫ y, P.coeff d * monomial d y ∂ν :=
        integral_finset_sum (μ := ν) P.support (fun d _ => (h d).const_mul _)
      _ = _ := by simp_rw [integral_const_mul]
  have hcut (Λ : ℝ) (p : S → ℕ) := cutoffModeLaw_monomial_integrable B μ hpos hg Λ S p
  have hm (p : S → ℕ) := finiteModeLaw_monomial_limit hn B μ hμ hpos hg S p
  refine ⟨fun Λ => hint _ (hcut Λ), hint _ (fun p => (hm p).1), ?_⟩
  simp_rw [hsum _ (hcut _), hsum _ (fun p => (hm p).1)]
  exact tendsto_finset_sum _ (fun d _ => (hm d).2.const_mul (P.coeff d))

/-- The zero-depth atom does not contribute to the continuum partition.
The upper bound is exactly the incoming mass on positive depths. -/
theorem partition_le_positive_depth_mass {n : ℕ} (hn : 0 < n)
    (B : Fin n → Fin n → Fin n → ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ) {g : ℝ} (hg : 0 ≤ g) :
    partition B μ g ≤ (μ (Set.Ioi 0)).toReal := by
  let A := (Prod.fst : Preparation n → ℝ) ⁻¹' Set.Ioi (0 : ℝ)
  have hA : MeasurableSet A := measurable_fst measurableSet_Ioi
  have ha : ∀ᵐ p ∂preparationMeasure n μ, 0 ≤ p.1 := by
    apply (Measure.ae_prod_iff_ae_ae (p := fun p : Preparation n => 0 ≤ p.1)
      (measurable_fst measurableSet_Ici)).2
    exact hμ.mono fun ℓ hℓ => Eventually.of_forall fun _ => hℓ
  have hub : ∀ᵐ p ∂preparationMeasure n μ,
      fullWeight B g p ≤ A.indicator (fun _ => (1 : ℝ)) p := by
    filter_upwards [ha] with p hp
    by_cases hpos : 0 < p.1
    · rw [Set.indicator_of_mem (show p ∈ A from hpos)]
      exact (fullWeight_range B hg p).2
    · have h0 : p.1 = 0 := le_antisymm (le_of_not_gt hpos) hp
      rw [Set.indicator_of_notMem (show p ∉ A from hpos)]
      simp [fullWeight, h0, fullDeterminant, hn.ne']
  have hi := integral_mono_ae (fullWeight_integrable hn B μ hμ hg)
    ((integrable_const (1:ℝ)).indicator hA) hub
  have hm : (preparationMeasure n μ) A = μ (Set.Ioi 0) := by
    have hmPres := @measurePreserving_fst ℝ (ModeSlot n → ℝ) _ _ μ (commonGaussian n) _
    unfold preparationMeasure
    dsimp only [A]
    rw [← Measure.map_apply measurable_fst measurableSet_Ioi, hmPres.map_eq]
  unfold partition
  calc
    _ ≤ ∫ p, A.indicator (fun _ => (1 : ℝ)) p ∂preparationMeasure n μ := hi
    _ = _ := by rw [integral_indicator hA, integral_const, smul_eq_mul, mul_one,
      Measure.real, Measure.restrict_apply_univ, hm]

/-- The exact compact-volume partition is continuous at every real
nonnegative coupling, using its same determinant and bounded density. -/
theorem partition_continuous_nonnegative {n : ℕ} (hn : 0 < n)
    (B : Fin n → Fin n → Fin n → ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ) : Continuous (fun g : ℝ≥0 => partition B μ g) := by
  rw [continuous_iff_continuousAt]
  intro g
  unfold ContinuousAt partition
  refine tendsto_integral_filter_of_dominated_convergence (μ := preparationMeasure n μ)
    (fun _ => (1:ℝ))
    (Eventually.of_forall fun j => fullWeight_aestronglyMeasurable hn B μ hμ j.2)
    (Eventually.of_forall fun j => Eventually.of_forall fun p => ?_) (integrable_const 1) ?_
  · change ‖fullWeight B (j : ℝ) p‖ ≤ 1
    calc
      _ = fullWeight B j p := Real.norm_of_nonneg (fullWeight_range B j.2 p).1
      _ ≤ 1 := (fullWeight_range B j.2 p).2
  · apply Eventually.of_forall
    intro p
    have h : Continuous (fun j : ℝ≥0 => fullWeight B j p) := by unfold fullWeight; fun_prop
    exact h.continuousAt

def elementarySourceMap {n : ℕ} (p : Preparation n) : ModeSlot n → ℝ :=
  depthRescale p.1 p.2

def cutoffElementarySourceMap {n : ℕ} (Λ : ℝ) (p : Preparation n) (i : ModeSlot n) : ℝ :=
  if latticeFrequency i.1 ≤ Λ then depthRescale p.1 p.2 i else 0

private theorem cutoffElementarySourceMap_measurable (n : ℕ) (Λ : ℝ) :
    Measurable (cutoffElementarySourceMap (n := n) Λ) := by
  apply measurable_pi_lambda
  intro i
  unfold cutoffElementarySourceMap
  split
  · exact (measurable_pi_apply i).comp (depthRescale_jointly_measurable n)
  · exact measurable_const

/-- The continuum law is joint over all elementary mode coordinates,
and uses the original depth-rescaled common Gaussian preparation. -/
def elementarySourceLaw {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) (g : ℝ) : Measure (ModeSlot n → ℝ) :=
  (gibbsMeasure B μ g).map elementarySourceMap

def cutoffElementarySourceLaw {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) (g Λ : ℝ) : Measure (ModeSlot n → ℝ) :=
  (cutoffGibbsMeasure B μ g Λ).map (cutoffElementarySourceMap Λ)

theorem elementarySourceLaw_probability {n : ℕ} (hn : 0 < n)
    (B : Fin n → Fin n → Fin n → ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ) (hpos : μ (Set.Ioi 0) ≠ 0) {g : ℝ} (hg : 0 ≤ g) :
    IsProbabilityMeasure (elementarySourceLaw B μ g) := by
  letI := gibbsMeasure_probability hn B μ hμ hpos hg
  exact Measure.isProbabilityMeasure_map (depthRescale_jointly_measurable n).aemeasurable

theorem cutoffElementarySourceLaw_probability {n : ℕ}
    (B : Fin n → Fin n → Fin n → ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hpos : μ (Set.Ioi 0) ≠ 0) {g : ℝ} (hg : 0 ≤ g) (Λ : ℝ) :
    IsProbabilityMeasure (cutoffElementarySourceLaw B μ g Λ) := by
  letI := cutoffGibbsMeasure_probability B μ hpos hg Λ
  exact Measure.isProbabilityMeasure_map (cutoffElementarySourceMap_measurable n Λ).aemeasurable

theorem elementarySourceLaw_finite_marginal {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) (g : ℝ) (S : Finset (ModeSlot n)) :
    (elementarySourceLaw B μ g).map S.restrict = finiteModeLaw B μ g S :=
  Measure.map_map (Finset.measurable_restrict S) (depthRescale_jointly_measurable n)

theorem cutoffElementarySourceLaw_finite_marginal {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) (g Λ : ℝ) (S : Finset (ModeSlot n)) :
    (cutoffElementarySourceLaw B μ g Λ).map S.restrict = cutoffModeLaw B μ g Λ S :=
  Measure.map_map (Finset.measurable_restrict S) (cutoffElementarySourceMap_measurable n Λ)

end UV.ContinueCurvatureMarginals
