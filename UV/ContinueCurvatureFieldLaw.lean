import UV.ContinueCurvatureGaussian
import UV.ContinueCurvatureMarginals

/-! The normalized interacting distribution-valued fields on the same
compact sector-plane torus. Both depths and fields use the declared common
Gaussian preparation. -/

noncomputable section

open MeasureTheory Filter Real
open scoped BigOperators Topology ENNReal NNReal

namespace UV.ContinueCurvatureFieldLaw

open UV.NextCurvatureLaw UV.ExtendCurvaturePotential
open UV.ResumeCurvatureDistributions UV.ResumeCurvatureRawBounds UV.ResumeCurvatureRawLaw
open UV.ExtendCurvatureGibbs UV.FurtherCurvatureDeterminant
open UV.RevisionCurvatureDeterminant (latticeFrequency)

local instance : MeasurableSpace RawDistribution := cylinderSpace

abbrev RawFields (n : ℕ) := Fin 2 → Fin n → RawDistribution

def jointRawReadout {n : ℕ} (p : Preparation n) : RawFields n :=
  fun a c => rawSample p.1 a c p.2

private def good {n : ℕ} (p : Preparation n) : Prop :=
  Summable fun i : ModeSlot n => rawRegularization i.1 * |depthRescale p.1 p.2 i|

private theorem good_measurable (n : ℕ) : MeasurableSet {p : Preparation n | good p} := by
  let f (i : ModeSlot n) (p : Preparation n) : ℝ :=
    rawRegularization i.1 * |depthRescale p.1 p.2 i|
  have hf (i : ModeSlot n) : Measurable (f i) := by
    have h : Measurable (fun p : Preparation n => depthRescale p.1 p.2 i) :=
      (measurable_pi_apply i).comp (depthRescale_jointly_measurable n)
    simpa only [f, Real.norm_eq_abs] using h.norm.const_mul (rawRegularization i.1)
  have hm := Measurable.ennreal_tsum (fun i => (hf i).ennreal_ofReal)
  have he (p : Preparation n) : good p ↔ (∑' i, ENNReal.ofReal (f i p)) ≠ ∞ := by
    let a (i : ModeSlot n) : ℝ≥0 :=
      ⟨f i p, mul_nonneg (rawRegularization_nonneg _) (abs_nonneg _)⟩
    have ha (i : ModeSlot n) : ENNReal.ofReal (f i p) = (a i : ℝ≥0∞) :=
      ENNReal.ofReal_eq_coe_nnreal _
    simp_rw [ha]
    change Summable (fun i => (a i : ℝ)) ↔ _
    exact ENNReal.tsum_coe_ne_top_iff_summable_coe.symm
  have hh : {p : Preparation n | good p} =
      (fun p => ∑' i, ENNReal.ofReal (f i p)) ⁻¹' ({⊤} : Set ℝ≥0∞)ᶜ := by
    ext p
    exact he p
  rw [hh]
  exact hm (measurableSet_singleton _).compl

private theorem potential_limit {n : ℕ} {p : Preparation n}
    (hp : good p) (a : Fin 2) (c : Fin n) :
    Tendsto (fun Λ : ℝ => cutoffRawPotential Λ p.1 p.2 a c) atTop
      (𝓝 (fullRawPotential p.1 p.2 a c)) := by
  let i : MeanZeroMode → ModeSlot n := fun k => (k,(a,c))
  have hi : Function.Injective i := fun _ _ hh => congrArg (fun j : ModeSlot n => j.1) hh
  have hs : Summable (fun k : MeanZeroMode => rawRegularization k * |depthRescale p.1 p.2 (k,(a,c))|) := by
    simpa only [Function.comp_def, i] using (show Summable _ from hp).comp_injective hi
  have ht : Summable (rawPotentialTerm p.1 p.2 a c) := by
    apply Summable.of_norm_bounded (hs.mul_left (sqrt 2))
    intro k
    unfold rawPotentialTerm
    rw [norm_smul, norm_mul, Real.norm_of_nonneg (rawRegularization_nonneg k), Real.norm_eq_abs,
      mul_comm (sqrt 2)]
    exact mul_le_mul_of_nonneg_left (realTorusMode_norm_bound k)
      (mul_nonneg (rawRegularization_nonneg k) (abs_nonneg _))
  have hco : Tendsto retainedModes atTop atTop := by
    refine tendsto_atTop.mpr fun s => eventually_atTop.mpr ⟨∑ k ∈ s, latticeFrequency k, ?_⟩
    intro Λ hΛ k hk
    exact (mem_retainedModes Λ k).mpr ((Finset.single_le_sum
      (f := fun k => latticeFrequency (k : MeanZeroMode)) (fun _ _ => sqrt_nonneg _) hk).trans hΛ)
  exact ht.hasSum.comp hco

/-- The raw sample is jointly measurable in the depth and in the full
Gaussian preparation, for the cylindrical measurable space. -/
theorem jointRawReadout_measurable (n : ℕ) : Measurable (jointRawReadout (n := n)) := by
  classical
  apply measurable_pi_lambda
  intro a
  apply measurable_pi_lambda
  intro c
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap (fun p : Preparation n => rawSample p.1 a c p.2) cylinderSpace ≤ _
  rw [cylinderSpace, MeasurableSpace.comap_comp]
  apply Measurable.comap_le
  apply measurable_pi_lambda
  intro φ
  let F (j : ℕ) (p : Preparation n) : ℝ :=
    if good p then cutoffRawDistribution j p.1 p.2 a c φ else 0
  have hm (j : ℕ) : Measurable (F j) :=
    Measurable.piecewise (good_measurable n)
      (cutoffRawDistribution_readout_measurable j a c φ) measurable_const
  apply measurable_of_tendsto_metrizable hm
  apply tendsto_pi_nhds.2
  intro p
  have hr : rawSample p.1 a c p.2 =
      if good p then fullRawDistribution p.1 p.2 a c else 0 := rfl
  change Tendsto (fun j => F j p) atTop (𝓝 (rawSample p.1 a c p.2 φ))
  rw [hr]
  by_cases hp : good p
  · simp only [F, if_pos hp]
    have h := (testPeriodicPair (ellipticTestCube φ)).continuous.continuousAt.tendsto.comp
      (potential_limit hp a c)
    exact h.comp tendsto_natCast_atTop_atTop
  · simp only [F, if_neg hp, ContinuousLinearMap.zero_apply]
    exact tendsto_const_nhds

def interactingRawFieldLaw {n : ℕ} (B : Fin n → Fin n → Fin n → ℝ) (μ : Measure ℝ) (g : ℝ) :
    Measure (RawFields n) :=
  (gibbsMeasure B μ g).map jointRawReadout

theorem interactingRawFieldLaw_probability {n : ℕ} (hn : 0 < n) (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ)
    (hpos : μ (Set.Ioi 0) ≠ 0) {g : ℝ} (hg : 0 ≤ g) :
    IsProbabilityMeasure (interactingRawFieldLaw B μ g) := by
  letI := gibbsMeasure_probability hn B μ hμ hpos hg
  exact Measure.isProbabilityMeasure_map (jointRawReadout_measurable n).aemeasurable

/-- The continuum partition has the manuscript's positive-depth
fibre formula with the same common-depth determinant. -/
theorem partition_fibre_formula {n : ℕ} (hn : 0 < n) (B : Fin n → Fin n → Fin n → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ ℓ ∂μ, 0 ≤ ℓ) {g : ℝ} (hg : 0 ≤ g) :
    partition B μ g =
      ∫ ℓ in Set.Ioi 0, fullDeterminant n ℓ *
        (∫ X, exp (-g * fullBracketPotential B ℓ X) ∂commonGaussian n) ∂μ := by
  let f (ℓ : ℝ) := fullDeterminant n ℓ *
    (∫ X, exp (-g * fullBracketPotential B ℓ X) ∂commonGaussian n)
  have hi : Integrable (fullWeight B g) (μ.prod (commonGaussian n)) :=
    fullWeight_integrable hn B μ hμ hg
  unfold partition preparationMeasure
  rw [integral_prod _ hi]
  simp_rw [fullWeight, integral_const_mul]
  change (∫ ℓ, f ℓ ∂μ) = _
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [hμ] with ℓ hℓ
  change f ℓ = (Set.Ioi (0 : ℝ)).indicator f ℓ
  by_cases hp : ℓ ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem hp]
  · have h0 : ℓ = 0 := le_antisymm (le_of_not_gt (show ¬0 < ℓ from hp)) hℓ
    rw [Set.indicator_of_notMem hp]
    simp [f, h0, fullDeterminant, hn.ne']

end UV.ContinueCurvatureFieldLaw
