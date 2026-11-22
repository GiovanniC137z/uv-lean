import UV.ContinueSpectrumGreen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! A concrete common positive spectral realization of every finite family
of sampled layers. The off-support continuous extension is used only to
prove local finiteness; its atom and continuum are exactly the source data. -/

noncomputable section
open MeasureTheory Real Filter Set
open scoped Topology ENNReal

namespace UV.RevisionSpectrum

/-- One continuous representative for each layer amplitude on the common
positive boundary spectral law. -/
def continueLayerMultiplier (β b M₂ r s : ℝ) : ℝ :=
  Real.cos (Real.sqrt (s-M₂)*r) + ((b-s)*r/β)*Real.sinc (Real.sqrt (s-M₂)*r) +
    (max (M₂-s) 0/(M₂-bulkPole β b M₂))*
      (Real.exp (-r*bulkKappa β b M₂) - (1+(b-bulkPole β b M₂)*r/β))

theorem continueLayerMultiplier_continuous (β b M₂ r : ℝ) :
    Continuous (continueLayerMultiplier β b M₂ r) := by
  unfold continueLayerMultiplier
  fun_prop

theorem continueLayerMultiplier_at_atom {β b M₂ : ℝ} (hβ : 0<β) (hb : b<M₂) (r : ℝ) :
    continueLayerMultiplier β b M₂ r (bulkPole β b M₂)=Real.exp (-r*bulkKappa β b M₂) := by
  have hp := (bulkPole_unique hβ hb).2.1
  unfold continueLayerMultiplier
  rw [Real.sqrt_eq_zero_of_nonpos (by linarith),zero_mul,Real.cos_zero,Real.sinc_zero,mul_one,
    max_eq_left (by linarith),div_self (sub_ne_zero.mpr hp.ne')]
  ring

theorem continueLayerMultiplier_on_continuum {β b M₂ s : ℝ} (hβ : 0<β)
    (hs : M₂<s) (r : ℝ) :
    continueLayerMultiplier β b M₂ r s=normalMode β (Real.sqrt (s-M₂)) (b-s) r := by
  have hk : 0<Real.sqrt (s-M₂) := Real.sqrt_pos.mpr (sub_pos.mpr hs)
  unfold continueLayerMultiplier normalMode
  rw [max_eq_right (by linarith : M₂-s≤0),zero_div,zero_mul,add_zero]
  by_cases hr : r=0
  · simp [hr]
  · rw [Real.sinc_of_ne_zero (mul_ne_zero hk.ne' hr)]
    field_simp

/-- Every pair of layer amplitudes is integrable with the Stieltjes weight
on the same positive probability space. -/
theorem continue_layer_pair_measure {β b M₂ x r r' : ℝ}
    (hβ : 0<β) (hb₀ : 0<b) (hb : b<M₂) (hx : 0<x) (hr : 0≤r) (hr' : 0≤r') :
    Integrable (fun s : ℝ =>
      continueLayerMultiplier β b M₂ r s*continueLayerMultiplier β b M₂ r' s/(x+s))
      (resumeBulkBoundaryMeasure β b M₂) ∧
    (∫ s : ℝ,
      continueLayerMultiplier β b M₂ r s*continueLayerMultiplier β b M₂ r' s/(x+s)
      ∂resumeBulkBoundaryMeasure β b M₂) = continueBulkLayerGreen β b M₂ x r r' := by
  let f := fun s : ℝ => continueLayerMultiplier β b M₂ r s*continueLayerMultiplier β b M₂ r' s/(x+s)
  have hρ (s : ℝ) : 0≤bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s) := by
    unfold bulkBoundaryDensity
    positivity
  have ha : Integrable f (ENNReal.ofReal (bulkResidue β b M₂) • Measure.dirac (bulkPole β b M₂)) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hc : Integrable f ((volume.restrict (Ioi M₂)).withDensity
      (fun s => ENNReal.ofReal (bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s)))) := by
    rw [integrable_withDensity_iff_integrable_smul' (by unfold bulkBoundaryDensity; fun_prop)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply (continue_layer_integrable hβ hb₀ hb hx hr hr').congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    dsimp only [f]
    rw [ENNReal.toReal_ofReal (hρ s),smul_eq_mul,
      continueLayerMultiplier_on_continuum hβ hs r,continueLayerMultiplier_on_continuum hβ hs r']
    unfold continueLayerDensity
    ring
  refine ⟨ha.add_measure hc,?_⟩
  change (∫ s,f s ∂resumeBulkBoundaryMeasure β b M₂)=_
  unfold resumeBulkBoundaryMeasure
  rw [integral_add_measure ha hc,integral_smul_measure,integral_dirac,
    ENNReal.toReal_ofReal (bulkResidue_positive hβ hb).le,
    integral_withDensity_eq_integral_toReal_smul (by unfold bulkBoundaryDensity; fun_prop)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  dsimp only [f]
  rw [continueLayerMultiplier_at_atom hβ hb r,continueLayerMultiplier_at_atom hβ hb r']
  simp only [smul_eq_mul,ENNReal.toReal_ofReal (hρ _)]
  have he : (∫ s : ℝ in Ioi M₂,
      bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s)*
        (continueLayerMultiplier β b M₂ r s*continueLayerMultiplier β b M₂ r' s/(x+s))) =
      ∫ s : ℝ in Ioi M₂,continueLayerDensity β b M₂ r r' s/(x+s) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp only
    rw [continueLayerMultiplier_on_continuum hβ hs r,continueLayerMultiplier_on_continuum hβ hs r']
    unfold continueLayerDensity
    ring
  rw [he]
  convert (continue_bulk_layer_stieltjes hβ hb₀ hb hx hr hr').2 using 1
  ring

variable {ι : Type*} [Fintype ι]

def continueLayerFormMeasure (β b M₂ : ℝ) (r v : ι → ℝ) : Measure ℝ :=
  (resumeBulkBoundaryMeasure β b M₂).withDensity
    (fun s => ENNReal.ofReal ((∑ i,v i*continueLayerMultiplier β b M₂ (r i) s)^2))

theorem continueLayerFormMeasure_locallyFinite {β b M₂ : ℝ} (hβ : 0<β) (hb : b<M₂)
    (r v : ι → ℝ) : IsLocallyFiniteMeasure (continueLayerFormMeasure β b M₂ r v) := by
  letI := resumeBulkBoundaryMeasure_probability hβ hb
  unfold continueLayerFormMeasure
  apply IsLocallyFiniteMeasure.withDensity_ofReal
  apply Continuous.pow
  exact continuous_finset_sum _ (fun i _ => continuous_const.mul (continueLayerMultiplier_continuous _ _ _ _))

theorem continueLayerFormMeasure_nonnegative_support {β b M₂ : ℝ}
    (hβ : 0<β) (hb₀ : 0<b) (hb : b<M₂) (r v : ι → ℝ) :
    ∀ᵐ s ∂continueLayerFormMeasure β b M₂ r v,0≤s :=
  (withDensity_absolutelyContinuous _ _).ae_le (resumeBulkBoundaryMeasure_nonnegative_support hβ hb₀ hb)

/-- The finite sampled layer source defines an actual positive locally
finite quadratic-form measure and the prescribed Green quadratic form. -/
theorem continueLayerFormMeasure_stieltjes {β b M₂ x : ℝ}
    (hβ : 0<β) (hb₀ : 0<b) (hb : b<M₂) (hx : 0<x)
    (r v : ι → ℝ) (hr : ∀ i,0≤r i) :
    Integrable (fun s : ℝ => (x+s)⁻¹) (continueLayerFormMeasure β b M₂ r v) ∧
    (∫ s : ℝ,(x+s)⁻¹ ∂continueLayerFormMeasure β b M₂ r v) =
      ∑ i,∑ j,v i*continueBulkLayerGreen β b M₂ x (r i) (r j)*v j := by
  let μ := resumeBulkBoundaryMeasure β b M₂
  let f := fun s : ℝ => (∑ i,v i*continueLayerMultiplier β b M₂ (r i) s)^2/(x+s)
  have hij (i j : ι) : Integrable (fun s : ℝ =>
      v i*v j*(continueLayerMultiplier β b M₂ (r i) s*continueLayerMultiplier β b M₂ (r j) s/(x+s))) μ :=
    ((continue_layer_pair_measure hβ hb₀ hb hx (hr i) (hr j)).1).const_mul _
  have he (s : ℝ) : f s=∑ i,∑ j,
      v i*v j*(continueLayerMultiplier β b M₂ (r i) s*continueLayerMultiplier β b M₂ (r j) s/(x+s)) := by
    dsimp [f]
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hfi : Integrable f μ := by
    change Integrable (fun s => f s) μ
    simp_rw [he]
    exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hij i j))
  have hfVal : (∫ s,f s ∂μ)=∑ i,∑ j,v i*continueBulkLayerGreen β b M₂ x (r i) (r j)*v j := by
    simp_rw [he]
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hij i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finset_sum _ (fun j _ => hij i j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul,(continue_layer_pair_measure hβ hb₀ hb hx (hr i) (hr j)).2]
    ring
  have hfMeas : Measurable (fun s : ℝ => ENNReal.ofReal ((∑ i,v i*continueLayerMultiplier β b M₂ (r i) s)^2)) := by
    apply Measurable.ennreal_ofReal
    apply Continuous.measurable
    apply Continuous.pow
    exact continuous_finset_sum _ (fun i _ => continuous_const.mul (continueLayerMultiplier_continuous _ _ _ _))
  have hi : Integrable (fun s : ℝ => (x+s)⁻¹) (continueLayerFormMeasure β b M₂ r v) := by
    unfold continueLayerFormMeasure
    rw [integrable_withDensity_iff_integrable_smul' hfMeas (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul,← div_eq_mul_inv] using hfi
  refine ⟨hi,?_⟩
  unfold continueLayerFormMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hfMeas (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul,← div_eq_mul_inv]
  exact hfVal

/-- The positive form measure has precisely the source atom and continuum;
the auxiliary continuous extension contributes no additional spectral mass. -/
theorem continueLayerFormMeasure_eq_source {β b M₂ : ℝ}
    (hβ : 0<β) (hb : b<M₂) (r v : ι → ℝ) :
    continueLayerFormMeasure β b M₂ r v =
      ENNReal.ofReal (bulkResidue β b M₂ *
        (∑ i,v i*Real.exp (-r i*bulkKappa β b M₂))^2) •
        Measure.dirac (bulkPole β b M₂) +
      (volume.restrict (Ioi M₂)).withDensity (fun s =>
        ENNReal.ofReal (bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s) *
          (∑ i,v i*normalMode β (Real.sqrt (s-M₂)) (b-s) (r i))^2)) := by
  classical
  let W := fun s : ℝ => ENNReal.ofReal
    ((∑ i,v i*continueLayerMultiplier β b M₂ (r i) s)^2)
  have hW : Measurable W := by
    apply Measurable.ennreal_ofReal
    apply Continuous.measurable
    apply Continuous.pow
    exact continuous_finset_sum _ (fun i _ =>
      continuous_const.mul (continueLayerMultiplier_continuous _ _ _ _))
  have hd : (Measure.dirac (bulkPole β b M₂)).withDensity W =
      W (bulkPole β b M₂) • Measure.dirac (bulkPole β b M₂) := by
    ext s hs
    rw [withDensity_apply _ hs,setLIntegral_dirac]
    by_cases hp : bulkPole β b M₂∈s <;> simp [hp]
  unfold continueLayerFormMeasure resumeBulkBoundaryMeasure
  rw [withDensity_add_measure,withDensity_smul_measure,hd,smul_smul]
  apply congrArg₂ (·+·)
  · dsimp only [W]
    simp_rw [continueLayerMultiplier_at_atom hβ hb]
    rw [← ENNReal.ofReal_mul (bulkResidue_positive hβ hb).le]
  · rw [← withDensity_mul _ (by unfold bulkBoundaryDensity; fun_prop) hW]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    dsimp only [Pi.mul_apply,W]
    simp_rw [continueLayerMultiplier_on_continuum hβ hs]
    exact (ENNReal.ofReal_mul (by unfold bulkBoundaryDensity; positivity)).symm

theorem continueLayerMultiplier_zero (β b M₂ s : ℝ) :
    continueLayerMultiplier β b M₂ 0 s=1 := by
  simp [continueLayerMultiplier]

/-- Boundary/layer spectrum of the positive normal comparison: an actual
common positive spectral law, positive locally finite finite-source forms,
all displayed Green blocks, and exact boundary normalization. -/
theorem continue_positive_bulk_spectrum {β b M₂ : ℝ}
    (hβ : 0<β) (hb₀ : 0<b) (hb : b<M₂)
    (r : ι → ℝ) (hr : ∀ i,0≤r i) :
    IsProbabilityMeasure (resumeBulkBoundaryMeasure β b M₂) ∧
    (∀ᵐ s ∂resumeBulkBoundaryMeasure β b M₂,0≤s) ∧
    (bulkResidue β b M₂ + ∫ s : ℝ in Ioi M₂,
      bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s)=1) ∧
    (∀ v : ι → ℝ,
      IsLocallyFiniteMeasure (continueLayerFormMeasure β b M₂ r v) ∧
      (∀ᵐ s ∂continueLayerFormMeasure β b M₂ r v,0≤s) ∧
      ∀ x : ℝ,0<x →
        Integrable (fun s : ℝ => (x+s)⁻¹) (continueLayerFormMeasure β b M₂ r v) ∧
        (∫ s : ℝ,(x+s)⁻¹ ∂continueLayerFormMeasure β b M₂ r v)=
          ∑ i,∑ j,v i*continueBulkLayerGreen β b M₂ x (r i) (r j)*v j) ∧
    (∀ i j : ι,∀ x : ℝ,0<x →
      Integrable (fun s : ℝ =>
        continueLayerMultiplier β b M₂ (r i) s*continueLayerMultiplier β b M₂ (r j) s/(x+s))
        (resumeBulkBoundaryMeasure β b M₂) ∧
      (∫ s : ℝ,
        continueLayerMultiplier β b M₂ (r i) s*continueLayerMultiplier β b M₂ (r j) s/(x+s)
        ∂resumeBulkBoundaryMeasure β b M₂)=continueBulkLayerGreen β b M₂ x (r i) (r j)) := by
  refine ⟨resumeBulkBoundaryMeasure_probability hβ hb,
    resumeBulkBoundaryMeasure_nonnegative_support hβ hb₀ hb,(bulkBoundary_mass hβ hb).2,?_,?_⟩
  · intro v
    exact ⟨continueLayerFormMeasure_locallyFinite hβ hb r v,
      continueLayerFormMeasure_nonnegative_support hβ hb₀ hb r v,
      fun _ hx => continueLayerFormMeasure_stieltjes hβ hb₀ hb hx r v hr⟩
  · intro i j x hx
    exact continue_layer_pair_measure hβ hb₀ hb hx (hr i) (hr j)

end UV.RevisionSpectrum
