import UV.ResumeCurvatureRawIdentity

/-! The raw distribution realization carries its cylindrical source law,
with the same Gaussian coordinate preparation. -/

noncomputable section

open MeasureTheory Filter Real
open scoped Topology ENNReal NNReal BigOperators

namespace UV.ResumeCurvatureRawLaw

open UV.NextCurvatureLaw UV.ExtendCurvaturePotential UV.ResumeCurvatureRawBounds
open UV.ResumeCurvatureDistributions
open UV.RevisionCurvatureDeterminant (latticeFrequency)

def cylinderSpace : MeasurableSpace RawDistribution :=
  MeasurableSpace.comap (fun t : RawDistribution => fun φ : SchwartzTest => t φ) inferInstance

local instance : MeasurableSpace RawDistribution := cylinderSpace

private def good {n : ℕ} (ℓ : ℝ) (X : ModeSlot n → ℝ) : Prop :=
  Summable fun i : ModeSlot n => rawRegularization i.1 * |depthRescale ℓ X i|

private theorem good_measurable {n : ℕ} (ℓ : ℝ) : MeasurableSet {X : ModeSlot n → ℝ | good ℓ X} := by
  let f (i : ModeSlot n) (X : ModeSlot n → ℝ) := rawRegularization i.1 * |depthRescale ℓ X i|
  have hf (i : ModeSlot n) : Measurable (f i) := by unfold f depthRescale; fun_prop
  have hm := Measurable.ennreal_tsum (fun i => (hf i).ennreal_ofReal)
  have he (X : ModeSlot n → ℝ) :
      good ℓ X ↔ (∑' i, ENNReal.ofReal (f i X)) ≠ ∞ := by
    let a (i : ModeSlot n) : ℝ≥0 :=
      ⟨f i X, mul_nonneg (rawRegularization_nonneg _) (abs_nonneg _)⟩
    have ha (i : ModeSlot n) : ENNReal.ofReal (f i X) = (a i : ℝ≥0∞) :=
      ENNReal.ofReal_eq_coe_nnreal _
    simp_rw [ha]
    change Summable (fun i => (a i : ℝ)) ↔ _
    exact ENNReal.tsum_coe_ne_top_iff_summable_coe.symm
  have hh : {X : ModeSlot n → ℝ | good ℓ X} =
      (fun X => ∑' i, ENNReal.ofReal (f i X)) ⁻¹' ({⊤} : Set ℝ≥0∞)ᶜ := by
    ext X
    exact he X
  rw [hh]
  exact hm (measurableSet_singleton _).compl

def rawSample {n : ℕ} (ℓ : ℝ) (a : Fin 2) (c : Fin n) (X : ModeSlot n → ℝ) : RawDistribution := by
  classical
  exact if good ℓ X then fullRawDistribution ℓ X a c else 0

theorem rawSample_ae_eq {n : ℕ} (ℓ : ℝ) (a : Fin 2) (c : Fin n) :
    rawSample ℓ a c =ᵐ[commonGaussian n] fun X => fullRawDistribution ℓ X a c := by
  filter_upwards [ae_regularized_coordinates_summable n] with X hX
  have hg : good ℓ X := hX ℓ
  simp [rawSample, hg]

private theorem potential_limit {n : ℕ} {ℓ : ℝ} {X : ModeSlot n → ℝ}
    (hX : good ℓ X) (a : Fin 2) (c : Fin n) :
    Tendsto (fun Λ : ℝ => cutoffRawPotential Λ ℓ X a c) atTop
      (𝓝 (fullRawPotential ℓ X a c)) := by
  let i : MeanZeroMode → ModeSlot n := fun k => (k,(a,c))
  have hi : Function.Injective i := fun _ _ hh => congrArg (fun j : ModeSlot n => j.1) hh
  have hs : Summable (fun k : MeanZeroMode => rawRegularization k * |depthRescale ℓ X (k,(a,c))|) := by
    simpa only [Function.comp_def, i] using (show Summable _ from hX).comp_injective hi
  have ht : Summable (rawPotentialTerm ℓ X a c) := by
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

theorem rawSample_measurable {n : ℕ} (ℓ : ℝ) (a : Fin 2) (c : Fin n) :
    Measurable (rawSample ℓ a c) := by
  classical
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap (rawSample ℓ a c) cylinderSpace ≤ _
  rw [cylinderSpace, MeasurableSpace.comap_comp]
  apply Measurable.comap_le
  apply measurable_pi_lambda
  intro φ
  let F (j : ℕ) (X : ModeSlot n → ℝ) : ℝ :=
    if good ℓ X then cutoffRawDistribution j ℓ X a c φ else 0
  have hm (j : ℕ) : Measurable (F j) := by
    have hmPair : Measurable (fun X : ModeSlot n → ℝ => (ℓ, X)) :=
      measurable_const.prodMk measurable_id
    have h := (cutoffRawDistribution_readout_measurable j a c φ).comp hmPair
    exact Measurable.piecewise (good_measurable ℓ) h measurable_const
  apply measurable_of_tendsto_metrizable hm
  apply tendsto_pi_nhds.2
  intro X
  change Tendsto (fun j => F j X) atTop (𝓝 (rawSample ℓ a c X φ))
  by_cases hg : good ℓ X
  · simp only [F, rawSample, if_pos hg]
    have h := (testPeriodicPair (ellipticTestCube φ)).continuous.continuousAt.tendsto.comp
      (potential_limit hg a c)
    exact h.comp tendsto_natCast_atTop_atTop
  · simp only [F, rawSample, if_neg hg, ContinuousLinearMap.zero_apply]
    exact tendsto_const_nhds

/-- Actual probability law of one selected raw field coordinate on the
cylindrical measurable space of continuous Schwartz-test functionals. -/
def rawCylinderLaw {n : ℕ} (ℓ : ℝ) (a : Fin 2) (c : Fin n) : Measure RawDistribution :=
  (commonGaussian n).map (rawSample ℓ a c)

theorem rawCylinderLaw_probability {n : ℕ} (ℓ : ℝ) (a : Fin 2) (c : Fin n) :
    IsProbabilityMeasure (rawCylinderLaw ℓ a c) :=
  Measure.isProbabilityMeasure_map (rawSample_measurable ℓ a c).aemeasurable

/-- Joint law of both adjoint fields, on the cylindrical sigma-algebra of
Schwartz-test evaluations, obtained from their common Gaussian coordinates. -/
def rawJointCylinderLaw {n : ℕ} (ℓ : ℝ) : Measure (Fin 2 → Fin n → RawDistribution) :=
  (commonGaussian n).map (fun X a c => rawSample ℓ a c X)

theorem rawJointCylinderLaw_probability {n : ℕ} (ℓ : ℝ) :
    IsProbabilityMeasure (rawJointCylinderLaw (n := n) ℓ) :=
  Measure.isProbabilityMeasure_map
    (measurable_pi_lambda _ (fun a => measurable_pi_lambda _ (fun c =>
      rawSample_measurable ℓ a c))).aemeasurable

end UV.ResumeCurvatureRawLaw
