import UV.ExtendCurvaturePotential
import UV.RevisionCurvaturePartition
import Mathlib.MeasureTheory.Integral.Pi

/-! Finite coupling in the same scaled Gaussian preparation and the
literal compact-torus bracket potential. -/

noncomputable section

open MeasureTheory Real Filter
open scoped Topology ENNReal NNReal BigOperators

namespace UV.ExtendCurvatureGibbs

open UV.NextCurvatureLaw UV.NextCurvatureFourierSummability
open UV.FurtherCurvatureDeterminant UV.FurtherCurvatureShell
open UV.RevisionCurvatureDeterminant UV.RevisionCurvaturePartition
open UV.ExtendCurvaturePotential

abbrev Preparation (n : ℕ) := ℝ × (ModeSlot n → ℝ)
def preparationMeasure (n : ℕ) (μ : Measure ℝ) : Measure (Preparation n) :=
  μ.prod (commonGaussian n)

instance (n : ℕ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IsFiniteMeasure (preparationMeasure n μ) := by
  unfold preparationMeasure
  infer_instance

def cutoffWeight {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (g Λ : ℝ)
    (p : Preparation n) : ℝ :=
  sphericalDeterminant n Λ p.1 * exp (-g * cutoffBracketPotential B Λ p.1 p.2)

def fullWeight {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (g : ℝ)
    (p : Preparation n) : ℝ :=
  fullDeterminant n p.1 * exp (-g * fullBracketPotential B p.1 p.2)

theorem cutoffWeight_range {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    {g : ℝ} (hg : 0 ≤ g) (Λ : ℝ) (p : Preparation n) :
    0 ≤ cutoffWeight B g Λ p ∧ cutoffWeight B g Λ p ≤ 1 := by
  have hD := relative_determinant_bounds (sphericalModes Λ) latticeFrequency p.1 n
  have he : exp (-g * cutoffBracketPotential B Λ p.1 p.2) ≤ 1 :=
    exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hg)
      (cutoffBracketPotential_nonneg B Λ p.1 p.2))
  unfold cutoffWeight
  exact ⟨mul_nonneg hD.1.le (exp_nonneg _), (mul_le_of_le_one_right hD.1.le he).trans hD.2⟩

private theorem fullDeterminant_range (n : ℕ) (ℓ : ℝ) :
    0 ≤ fullDeterminant n ℓ ∧ fullDeterminant n ℓ ≤ 1 := by
  unfold fullDeterminant
  split
  · split <;> simp
  refine ⟨exp_nonneg _, exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) ?_)⟩
  apply tsum_nonneg
  intro k
  apply log_nonneg
  have hd : 0 ≤ depthSpectrum ℓ k := by unfold depthSpectrum; split <;> positivity
  linarith

theorem fullWeight_range {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    {g : ℝ} (hg : 0 ≤ g) (p : Preparation n) :
    0 ≤ fullWeight B g p ∧ fullWeight B g p ≤ 1 := by
  have hD := fullDeterminant_range n p.1
  have he : exp (-g * fullBracketPotential B p.1 p.2) ≤ 1 :=
    exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hg)
      (fullBracketPotential_nonneg B p.1 p.2))
  unfold fullWeight
  exact ⟨mul_nonneg hD.1 (exp_nonneg _), (mul_le_of_le_one_right hD.1 he).trans hD.2⟩

theorem cutoffWeight_measurable {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (g Λ : ℝ) :
    Measurable (cutoffWeight B g Λ) := by
  have hD : Measurable (fun p : Preparation n => sphericalDeterminant n Λ p.1) := by
    unfold sphericalDeterminant relativeDeterminant
    apply Measurable.inv
    apply Finset.measurable_prod
    intro k _
    fun_prop
  unfold cutoffWeight
  exact hD.mul (((cutoffBracketPotential_measurable B Λ).const_mul (-g)).exp)

private def goodPreparation {n : ℕ} (p : Preparation n) : Prop :=
  p.1 = 0 ∨ (0 < p.1 ∧ Summable fun i : ModeSlot n => derivativeWeight 0 p.1 i.1 * |p.2 i|)

private theorem measurableSet_goodPreparation (n : ℕ) :
    MeasurableSet {p : Preparation n | goodPreparation p} := by
  let f (i : ModeSlot n) (p : Preparation n) : ℝ :=
    derivativeWeight 0 p.1 i.1 * |p.2 i|
  have hf (i : ModeSlot n) : Measurable (f i) := by
    unfold f derivativeWeight UV.FurtherCurvatureLine.curvatureCovariance
    fun_prop
  have hs : Measurable (fun p : Preparation n => ∑' i, ENNReal.ofReal (f i p)) :=
    Measurable.ennreal_tsum (fun i => (hf i).ennreal_ofReal)
  have he (p : Preparation n) : Summable (fun i => f i p) ↔
      (∑' i, ENNReal.ofReal (f i p)) ≠ ∞ := by
    let a (i : ModeSlot n) : ℝ≥0 :=
      ⟨f i p, mul_nonneg (derivativeWeight_nonneg 0 p.1 i.1) (abs_nonneg _)⟩
    have h (i : ModeSlot n) : ENNReal.ofReal (f i p) = (a i : ℝ≥0∞) :=
      ENNReal.ofReal_eq_coe_nnreal _
    simp_rw [h]
    change Summable (fun i => (a i : ℝ)) ↔ _
    exact ENNReal.tsum_coe_ne_top_iff_summable_coe.symm
  have hset : {p : Preparation n | goodPreparation p} =
      ((Prod.fst) ⁻¹' ({0} : Set ℝ)) ∪
        ((Prod.fst ⁻¹' Set.Ioi (0 : ℝ)) ∩
          ((fun p => ∑' i, ENNReal.ofReal (f i p)) ⁻¹' ({⊤} : Set ℝ≥0∞)ᶜ)) := by
    ext p
    change (_ = 0 ∨ (0 < p.1 ∧ Summable (fun i => f i p))) ↔ _
    rw [he]
    rfl
  rw [hset]
  exact (measurable_fst (measurableSet_singleton _)).union
    ((measurable_fst measurableSet_Ioi).inter (hs (measurableSet_singleton _).compl))

theorem ae_weight_limit {n : ℕ} (hn : 0 < n) (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ)
    {g : ℝ} (hg : 0 ≤ g) :
    ∀ᵐ p ∂preparationMeasure n μ,
      Tendsto (fun Λ : ℝ => cutoffWeight B g Λ p) atTop (𝓝 (fullWeight B g p)) := by
  have ha : ∀ᵐ p : Preparation n ∂preparationMeasure n μ, goodPreparation p := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_goodPreparation n)).2
    filter_upwards [hμ] with ℓ hℓ
    rcases hℓ.eq_or_lt with hz | hp
    · exact Eventually.of_forall fun _ => Or.inl hz.symm
    · exact (ae_weighted_transfer_summable n hp).mono fun _ h => Or.inr ⟨hp,h 0⟩
  filter_upwards [ha] with p hp
  rcases hp with h0 | hS
  · have hx : Tendsto (fun Λ : ℝ => sphericalDeterminant n Λ p.1) atTop (𝓝 0) := by
      rw [h0]
      simpa only [fullDeterminant, if_pos rfl, if_neg hn.ne'] using zero_depth_determinant_limit hn
    have hfull : fullWeight B g p = 0 := by simp [fullWeight, h0, fullDeterminant, hn.ne']
    rw [hfull]
    refine squeeze_zero (fun Λ => (cutoffWeight_range B hg Λ p).1) (fun Λ => ?_) hx
    have he : exp (-g * cutoffBracketPotential B Λ p.1 p.2) ≤ 1 :=
      exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hg)
        (cutoffBracketPotential_nonneg _ _ _ _))
    unfold cutoffWeight
    exact mul_le_of_le_one_right
      (relative_determinant_bounds _ _ _ _).1.le he
  · exact (positive_depth_determinant_limit n hS.1).mul
      (continuous_exp.continuousAt.tendsto.comp
        ((bracketPotential_limit B hS.2).const_mul (-g)))

theorem fullWeight_aestronglyMeasurable {n : ℕ} (hn : 0 < n) (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ)
    {g : ℝ} (hg : 0 ≤ g) :
    AEStronglyMeasurable (fullWeight B g) (preparationMeasure n μ) := by
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (fun j : ℕ => (cutoffWeight_measurable B g j).aestronglyMeasurable) ?_
  filter_upwards [ae_weight_limit hn B μ hμ hg] with p hp
  exact hp.comp tendsto_natCast_atTop_atTop

theorem cutoffWeight_integrable {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] {g : ℝ} (hg : 0 ≤ g) (Λ : ℝ) :
    Integrable (cutoffWeight B g Λ) (preparationMeasure n μ) := by
  apply Integrable.of_bound (cutoffWeight_measurable B g Λ).aestronglyMeasurable 1
  exact Eventually.of_forall fun p => by
    rw [Real.norm_of_nonneg (cutoffWeight_range B hg Λ p).1]
    exact (cutoffWeight_range B hg Λ p).2

theorem fullWeight_integrable {n : ℕ} (hn : 0 < n) (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ)
    {g : ℝ} (hg : 0 ≤ g) :
    Integrable (fullWeight B g) (preparationMeasure n μ) := by
  apply Integrable.of_bound (fullWeight_aestronglyMeasurable hn B μ hμ hg) 1
  exact Eventually.of_forall fun p => by
    rw [Real.norm_of_nonneg (fullWeight_range B hg p).1]
    exact (fullWeight_range B hg p).2

theorem weights_converge_L1 {n : ℕ} (hn : 0 < n) (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ)
    {g : ℝ} (hg : 0 ≤ g) :
    Tendsto (fun Λ : ℝ => ∫ p, ‖cutoffWeight B g Λ p - fullWeight B g p‖
        ∂preparationMeasure n μ)
      atTop (𝓝 0) := by
  have hm := fullWeight_aestronglyMeasurable hn B μ hμ hg
  have hlim : ∀ᵐ p ∂preparationMeasure n μ,
      Tendsto (fun Λ : ℝ => ‖cutoffWeight B g Λ p - fullWeight B g p‖) atTop (𝓝 0) := by
    filter_upwards [ae_weight_limit hn B μ hμ hg] with p hp
    have hh : Tendsto (fun _ : ℝ => fullWeight B g p) atTop (𝓝 (fullWeight B g p)) :=
      tendsto_const_nhds
    simpa using (hp.sub hh).norm
  have hd := tendsto_integral_filter_of_dominated_convergence
    (μ := preparationMeasure n μ) (f := fun _ => (0 : ℝ)) (fun _ => (2 : ℝ))
    (Eventually.of_forall fun Λ =>
      (((cutoffWeight_measurable B g Λ).aestronglyMeasurable.sub hm).norm))
    (Eventually.of_forall fun Λ => Eventually.of_forall fun p => by
      rw [norm_norm]
      exact (norm_sub_le _ _).trans (by
        rw [Real.norm_of_nonneg (cutoffWeight_range B hg Λ p).1,
          Real.norm_of_nonneg (fullWeight_range B hg p).1]
        linarith [(cutoffWeight_range B hg Λ p).2, (fullWeight_range B hg p).2]))
    (integrable_const _) hlim
  simpa using hd

def partition {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (μ : Measure ℝ) (g : ℝ) : ℝ :=
  ∫ p, fullWeight B g p ∂preparationMeasure n μ

theorem partition_pos_le {n : ℕ} (hn : 0 < n) (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ)
    (hpos : μ (Set.Ioi 0) ≠ 0) {g : ℝ} (hg : 0 ≤ g) :
    0 < partition B μ g ∧ partition B μ g ≤ (μ Set.univ).toReal := by
  have hi := fullWeight_integrable hn B μ hμ hg
  unfold partition
  constructor
  · apply (integral_pos_iff_support_of_nonneg (fun p => (fullWeight_range B hg p).1) hi).2
    apply pos_iff_ne_zero.mpr
    intro hzero
    apply hpos
    have h : (preparationMeasure n μ) (Prod.fst ⁻¹' Set.Ioi (0 : ℝ)) = μ (Set.Ioi 0) := by
      have hp := @measurePreserving_fst ℝ (ModeSlot n → ℝ) _ _ μ (commonGaussian n) _
      change (μ.prod (commonGaussian n)) _ = _
      rw [← Measure.map_apply measurable_fst measurableSet_Ioi, hp.map_eq]
    rw [← h]
    apply measure_mono_null _ hzero
    intro p hp
    exact (mul_pos (full_determinant_pos n hp) (exp_pos _)).ne'
  · have h := integral_mono hi (integrable_const 1) (fun p => (fullWeight_range B hg p).2)
    have hmass : (preparationMeasure n μ) Set.univ = μ Set.univ := by
      unfold preparationMeasure
      have hg : commonGaussian n Set.univ = 1 := measure_univ
      rw [← Set.univ_prod_univ, Measure.prod_prod, hg, mul_one]
    simpa only [integral_const, smul_eq_mul, Measure.real, mul_one, hmass] using h

/-- The nonzero finite partition normalizes the common preparation law. -/
def gibbsMeasure {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (μ : Measure ℝ) (g : ℝ) :
    Measure (Preparation n) :=
  (preparationMeasure n μ).withDensity (fun p => ENNReal.ofReal (fullWeight B g p / partition B μ g))

theorem gibbsMeasure_probability {n : ℕ} (hn : 0 < n) (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ)
    (hpos : μ (Set.Ioi 0) ≠ 0) {g : ℝ} (hg : 0 ≤ g) :
    IsProbabilityMeasure (gibbsMeasure B μ g) := by
  have hZ := (partition_pos_le hn B μ hμ hpos hg).1
  refine ⟨?_⟩
  unfold gibbsMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      ((fullWeight_integrable hn B μ hμ hg).div_const _) (Eventually.of_forall fun p =>
        div_nonneg (fullWeight_range B hg p).1 hZ.le),
    integral_div, ← partition, div_self hZ.ne', ENNReal.ofReal_one]

end UV.ExtendCurvatureGibbs
