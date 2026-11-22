import UV.ResumeCurvatureSmooth
import UV.ResumeCurvatureRawBounds
import Mathlib.Analysis.Distribution.SchwartzSpace

/-! A samplewise distribution construction for the raw Gaussian
coordinates. Its bounded periodic potential is obtained by the inverse
of the cubic elliptic multiplier, and the inverse smoothing is applied
on Schwartz tests. The normal-depth transfer is independent of this
auxiliary distribution realization. -/

noncomputable section

open MeasureTheory Filter Real
open scoped Topology BigOperators ENNReal SchwartzMap

namespace UV.ResumeCurvatureDistributions

open UV.NextCurvatureLaw UV.ResumeCurvatureSmooth UV.ResumeCurvatureRawBounds
open UV.ExtendCurvaturePotential
open UV.RevisionCurvatureDeterminant (latticeFrequency)

private theorem continuous_coverPoint : Continuous coverPoint := by
  apply continuous_pi
  intro j
  change Continuous (fun x : Cover => ((x j : ℝ) : AddCircle ((2 : ℝ) * π)))
  exact continuous_quot_mk.comp (continuous_apply j)

def rawPotentialTerm {n : ℕ} (ℓ : ℝ) (X : ModeSlot n → ℝ)
    (a : Fin 2) (c : Fin n) (k : MeanZeroMode) : ContinuousField :=
  (rawRegularization k * depthRescale ℓ X (k,(a,c))) • realTorusMode k

def cutoffRawPotential {n : ℕ} (Λ ℓ : ℝ) (X : ModeSlot n → ℝ)
    (a : Fin 2) (c : Fin n) : ContinuousField :=
  ∑ k ∈ retainedModes Λ, rawPotentialTerm ℓ X a c k

def fullRawPotential {n : ℕ} (ℓ : ℝ) (X : ModeSlot n → ℝ)
    (a : Fin 2) (c : Fin n) : ContinuousField :=
  ∑' k, rawPotentialTerm ℓ X a c k

private theorem retained_cofinal :
    Tendsto retainedModes atTop atTop := by
  refine tendsto_atTop.mpr fun s => eventually_atTop.mpr ⟨∑ k ∈ s, latticeFrequency k, ?_⟩
  intro Λ hΛ k hk
  apply (mem_retainedModes Λ k).mpr
  exact (Finset.single_le_sum (f := fun k => latticeFrequency (k : MeanZeroMode))
    (fun _ _ => sqrt_nonneg _) hk).trans hΛ

private theorem raw_potential_term_bound {n : ℕ} (ℓ : ℝ) (X : ModeSlot n → ℝ)
    (a : Fin 2) (c : Fin n) (k : MeanZeroMode) :
    ‖rawPotentialTerm ℓ X a c k‖ ≤
      sqrt 2 * (rawRegularization k * |depthRescale ℓ X (k,(a,c))|) := by
  unfold rawPotentialTerm
  rw [norm_smul, norm_mul, Real.norm_of_nonneg (rawRegularization_nonneg k), Real.norm_eq_abs,
    mul_comm (sqrt 2)]
  exact mul_le_mul_of_nonneg_left (realTorusMode_norm_bound k)
    (mul_nonneg (rawRegularization_nonneg k) (abs_nonneg _))

theorem ae_rawPotential_uniform_limit (n : ℕ) :
    ∀ᵐ X ∂commonGaussian n, ∀ (ℓ : ℝ) (a : Fin 2) (c : Fin n),
      Tendsto (fun Λ : ℝ => cutoffRawPotential Λ ℓ X a c) atTop
        (𝓝 (fullRawPotential ℓ X a c)) := by
  filter_upwards [ae_regularized_coordinates_summable n] with X h
  intro ℓ a c
  let i : MeanZeroMode → ModeSlot n := fun k => (k,(a,c))
  have hi : Function.Injective i := fun _ _ hh => congrArg (fun j : ModeSlot n => j.1) hh
  have hs : Summable (fun k : MeanZeroMode => rawRegularization k * |depthRescale ℓ X (k,(a,c))|) := by
    simpa only [Function.comp_def, i] using (h ℓ).comp_injective hi
  have ht : Summable (rawPotentialTerm ℓ X a c) :=
    Summable.of_norm_bounded (hs.mul_left (sqrt 2)) (raw_potential_term_bound ℓ X a c)
  exact ht.hasSum.comp retained_cofinal

abbrev SchwartzTest := 𝓢(Cover, ℝ)
abbrev RawDistribution := SchwartzTest →L[ℝ] ℝ

private theorem cover_pair_integrable (F : ContinuousField) (φ : SchwartzTest) :
    Integrable (fun x => F (coverPoint x) * φ x) volume := by
  refine (φ.integrable.norm.const_mul ‖F‖).mono'
    ((F.continuous.comp continuous_coverPoint).aestronglyMeasurable.mul φ.continuous.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm F _) (norm_nonneg _)

private theorem norm_cover_pair_le (F : ContinuousField) (φ : SchwartzTest) :
    ‖∫ x, F (coverPoint x) * φ x‖ ≤ ‖F‖ * ∫ x, ‖φ x‖ := by
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul]
  refine integral_mono (cover_pair_integrable F φ).norm (φ.integrable.norm.const_mul _) (fun x => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm F _) (norm_nonneg _)

/-- Each continuous periodic generator defines a genuine tempered
distribution by multiplication against Schwartz tests on the cover. -/
def coverDistribution (F : ContinuousField) : RawDistribution := by
  apply SchwartzMap.mkCLMtoNormedSpace (fun φ => ∫ x, F (coverPoint x) * φ x)
  · intro f g
    simp_rw [SchwartzMap.add_apply, mul_add]
    exact integral_add (cover_pair_integrable F f) (cover_pair_integrable F g)
  · intro a f
    simp_rw [SchwartzMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      show ∀ x : Cover, F (coverPoint x) * (a * f x) = a * (F (coverPoint x) * f x) by
        intro x; ring, integral_const_mul]
  obtain ⟨p, C, hC, hbound⟩ := SchwartzMap.norm_toLp_le_seminorm ℝ ℝ (1 : ℝ≥0∞)
    (volume : Measure Cover)
  refine ⟨Finset.Iic (p,0), ‖F‖ * C, mul_nonneg (norm_nonneg _) hC, fun f => ?_⟩
  have hn : ‖f.toLp 1 (volume : Measure Cover)‖ = ∫ x, ‖f x‖ := by
    exact L1.norm_of_fun_eq_integral_norm (μ := volume) f.integrable
  have hb := hbound f
  rw [hn] at hb
  rw [mul_assoc]
  exact (norm_cover_pair_le F f).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))

private theorem coverDistribution_apply (F : ContinuousField) (φ : SchwartzTest) :
    coverDistribution F φ = ∫ x, F (coverPoint x) * φ x := rfl

/-- For each Schwartz test, evaluation of the periodic distribution is a
continuous linear functional of the bounded periodic potential. -/
def testPeriodicPair (φ : SchwartzTest) : ContinuousField →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun F => ∫ x, F (coverPoint x) * φ x
      map_add' := by
        intro F G
        simp_rw [ContinuousMap.add_apply, add_mul]
        exact integral_add (cover_pair_integrable F φ) (cover_pair_integrable G φ)
      map_smul' := by
        intro r F
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, integral_const_mul] }
    (∫ x, ‖φ x‖) (fun F => (norm_cover_pair_le F φ).trans_eq (mul_comm _ _))

def unitCoordinate (j : Fin 4) : Cover :=
  EuclideanSpace.single j 1

theorem unitCoordinate_norm (j : Fin 4) : ‖unitCoordinate j‖ = 1 := by
  simp [unitCoordinate]

def secondCoordinate (j : Fin 4) : SchwartzTest →L[ℝ] SchwartzTest :=
  let D := SchwartzMap.pderivCLM ℝ (unitCoordinate j)
  D.comp D

def oneMinusLaplacian : SchwartzTest →L[ℝ] SchwartzTest :=
  ContinuousLinearMap.id ℝ SchwartzTest - ∑ j, secondCoordinate j

def ellipticTestCube : SchwartzTest →L[ℝ] SchwartzTest :=
  oneMinusLaplacian.comp (oneMinusLaplacian.comp oneMinusLaplacian)

def cutoffRawDistribution {n : ℕ} (Λ ℓ : ℝ) (X : ModeSlot n → ℝ)
    (a : Fin 2) (c : Fin n) : RawDistribution :=
  (coverDistribution (cutoffRawPotential Λ ℓ X a c)).comp ellipticTestCube

def fullRawDistribution {n : ℕ} (ℓ : ℝ) (X : ModeSlot n → ℝ)
    (a : Fin 2) (c : Fin n) : RawDistribution :=
  (coverDistribution (fullRawPotential ℓ X a c)).comp ellipticTestCube

/-- The common Gaussian coordinates have a samplewise realization by the
same weak distribution formula at every depth. The spherical versions
converge on every Schwartz test to the unrestricted distribution. -/
theorem ae_rawDistribution_weak_limit (n : ℕ) :
    ∀ᵐ X ∂commonGaussian n, ∀ (ℓ : ℝ) (a : Fin 2) (c : Fin n) (φ : SchwartzTest),
      Tendsto (fun Λ : ℝ => cutoffRawDistribution Λ ℓ X a c φ) atTop
        (𝓝 (fullRawDistribution ℓ X a c φ)) := by
  filter_upwards [ae_rawPotential_uniform_limit n] with X h
  intro ℓ a c φ
  change Tendsto (fun Λ : ℝ => testPeriodicPair (ellipticTestCube φ) (cutoffRawPotential Λ ℓ X a c))
    atTop (𝓝 (testPeriodicPair (ellipticTestCube φ) (fullRawPotential ℓ X a c)))
  exact (testPeriodicPair (ellipticTestCube φ)).continuous.continuousAt.tendsto.comp (h ℓ a c)

theorem cutoffRawDistribution_readout_measurable {n : ℕ} (Λ : ℝ)
    (a : Fin 2) (c : Fin n) (φ : SchwartzTest) :
    Measurable (fun p : ℝ × (ModeSlot n → ℝ) => cutoffRawDistribution Λ p.1 p.2 a c φ) := by
  change Measurable (fun p : ℝ × (ModeSlot n → ℝ) =>
    testPeriodicPair (ellipticTestCube φ) (cutoffRawPotential Λ p.1 p.2 a c))
  unfold cutoffRawPotential
  simp_rw [map_sum, rawPotentialTerm, map_smul, smul_eq_mul]
  apply Finset.measurable_sum
  intro k _
  have h : Measurable (fun p : ℝ × (ModeSlot n → ℝ) => depthRescale p.1 p.2 (k,(a,c))) :=
    (measurable_pi_apply (k,(a,c))).comp (depthRescale_jointly_measurable n)
  exact (h.const_mul (rawRegularization k)).mul_const _

theorem fullRawDistribution_readout_aemeasurable {n : ℕ}
    (ℓ : ℝ) (a : Fin 2) (c : Fin n) (φ : SchwartzTest) :
    AEMeasurable (fun X => fullRawDistribution ℓ X a c φ) (commonGaussian n) := by
  apply aemeasurable_of_tendsto_metrizable_ae' (f := fun Λ : ℕ => fun X =>
    cutoffRawDistribution Λ ℓ X a c φ)
  · intro j
    exact ((cutoffRawDistribution_readout_measurable j a c φ).comp
      (measurable_const.prodMk measurable_id)).aemeasurable
  · filter_upwards [ae_rawDistribution_weak_limit n] with X h
    exact (h ℓ a c φ).comp tendsto_natCast_atTop_atTop

end UV.ResumeCurvatureDistributions
