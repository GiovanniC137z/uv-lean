import UV.ContinueWilsonShellDensityBound
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! A pointwise continuous displacement density for the actual independent
A4 marks. Its values on a closed polygon, including a single hop of zero
displacement, are fixed by the law and continuity. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal Topology RealInnerProductSpace

namespace UV

variable {ι : Type*} [Fintype ι]

def wilsonMarkLaw (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) : Measure OSFourSpace :=
  (wilsonBallMeasure ι).map (wilsonSingleDisplacement L T)

instance (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) : IsProbabilityMeasure (wilsonMarkLaw L T) :=
  Measure.isProbabilityMeasure_map (wilsonSingleDisplacement L T).continuous.measurable.aemeasurable

def wilsonMarkDensity (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (x : OSFourSpace) : ℝ :=
  ((wilsonMarkLaw L T).rnDeriv volume x).toReal

theorem wilson_mark_density_memLp {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    MemLp (wilsonMarkDensity L T) 2 volume := by
  obtain ⟨C,hC,hdom⟩ := wilson_single_density_bound hL T
  let μ := wilsonMarkLaw L T
  have h₁ : Integrable (wilsonMarkDensity L T) volume :=
    integrableOn_univ.mp (Measure.integrableOn_toReal_rnDeriv (μ := μ) (ν := volume) (measure_ne_top _ _))
  have hb := wilson_rn_density_bounded (μ := μ) hdom
  apply (memLp_two_iff_integrable_sq h₁.aestronglyMeasurable).mpr
  apply (h₁.mul_const C.toReal).mono' (h₁.aestronglyMeasurable.pow 2)
  filter_upwards [hb] with x hx
  have hn : 0 ≤ wilsonMarkDensity L T x := ENNReal.toReal_nonneg
  change ‖wilsonMarkDensity L T x ^ 2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _),pow_two]
  exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hC hx) hn

theorem wilson_two_mark_convolution (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    wilsonDisplacementMeasure L T = (wilsonMarkLaw L T) ∗ (wilsonMarkLaw L T) := by
  let R := wilsonSingleDisplacement L T
  rw [Measure.conv,wilsonMarkLaw,Measure.map_prod_map _ _ R.continuous.measurable R.continuous.measurable,
    Measure.map_map (measurable_fst.add measurable_snd) (R.continuous.measurable.prodMap R.continuous.measurable)]
  unfold wilsonDisplacementMeasure
  congr 1
  funext z
  exact map_add R z.1 z.2

def wilsonContinuousDensity (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (x : OSFourSpace) : ℝ :=
  ∫ y, wilsonMarkDensity L T y * wilsonMarkDensity L T (x-y)

theorem wilson_continuous_density_nonneg (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (x : OSFourSpace) :
    0 ≤ wilsonContinuousDensity L T x := integral_nonneg (fun _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

theorem wilson_continuous_density_continuous {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    Continuous (wilsonContinuousDensity L T) := by
  let f := wilsonMarkDensity L T
  let hf := wilson_mark_density_memLp hL T
  let F := hf.toLp f
  let g : OSFourSpace → C(OSFourSpace,OSFourSpace) := fun x => ⟨fun y => x-y,continuous_const.sub continuous_id⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry _ (continuous_fst.sub continuous_snd)
  have hmp (x) : MeasurePreserving (g x) volume volume := volume.measurePreserving_sub_left x
  let A := fun x => Lp.compMeasurePreserving (g x) (hmp x) F
  have hA : Continuous A := (continuous_const (y := F)).compMeasurePreservingLp hg hmp (by norm_num)
  have he (x) : ⟪F,A x⟫ = wilsonContinuousDensity L T x := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,Lp.coeFn_compMeasurePreserving F (hmp x),
      (hmp x).quasiMeasurePreserving.ae hf.coeFn_toLp] with y hy hy' hy''
    change ⟪F y, Lp.compMeasurePreserving (g x) (hmp x) F y⟫ = f y * f (x-y)
    rw [hy']
    change ⟪F y,F (g x y)⟫ = _
    rw [hy,hy'']
    exact real_inner_comm _ _ |>.trans (by rfl)
  simpa only [←funext he] using continuous_const.inner (𝕜 := ℝ) hA

theorem wilson_continuous_density_law {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    volume.withDensity (fun x => ENNReal.ofReal (wilsonContinuousDensity L T x)) = wilsonDisplacementMeasure L T := by
  let μ := wilsonMarkLaw L T
  let R := μ.rnDeriv volume
  let f := wilsonMarkDensity L T
  obtain ⟨_,_,hdom⟩ := wilson_single_density_bound hL T
  have hac : μ ≪ volume := absolutelyContinuous_of_le_smul hdom
  rw [wilson_two_mark_convolution,conv_eq_withDensity_lconvolution_rnDeriv hac hac]
  congr 1
  funext x
  have hmp := volume.measurePreserving_sub_left x
  have hf := wilson_mark_density_memLp hL T
  have hi : Integrable (fun y => f y * f (x-y)) volume := hf.integrable_mul (hf.comp_measurePreserving hmp)
  rw [wilsonContinuousDensity,ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ =>
    mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg),lconvolution_def]
  apply lintegral_congr_ae
  filter_upwards [Measure.rnDeriv_lt_top μ volume,hmp.quasiMeasurePreserving.ae (Measure.rnDeriv_lt_top μ volume)]
    with y hy hy'
  change ENNReal.ofReal ((R y).toReal * (R (x-y)).toReal) = R y * R (-y+x)
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal hy.ne,ENNReal.ofReal_toReal hy'.ne,sub_eq_neg_add]

theorem wilson_continuous_density_ae {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    (fun x => ENNReal.ofReal (wilsonContinuousDensity L T x)) =ᵐ[volume] wilsonDisplacementDensity L T :=
  by
    have he := (wilson_continuous_density_law hL T).trans (wilson_displacement_density_eq hL T).symm
    apply ((withDensity_eq_iff (Measure.measurable_rnDeriv _ _).aemeasurable
      (wilson_continuous_density_continuous hL T).measurable.ennreal_ofReal.aemeasurable
      ((wilson_displacement_density_mass hL T).trans_ne ENNReal.one_ne_top)).mp he.symm).symm

theorem wilson_continuous_density_support {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    {x : OSFourSpace} (hx : 2*L < ‖x‖) : wilsonContinuousDensity L T x = 0 := by
  let f := wilsonContinuousDensity L T
  let U := (closedBall (0:OSFourSpace) (2*L))ᶜ
  have ho : IsOpen U := isClosed_closedBall.isOpen_compl
  have hzero : wilsonDisplacementMeasure L T U = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    simpa only [U,notMem_compl_iff,mem_closedBall,dist_zero_right] using wilson_displacement_band hL.le T
  rw [←wilson_continuous_density_law hL T,withDensity_apply _ ho.measurableSet] at hzero
  have he : f =ᵐ[volume.restrict U] 0 := by
    filter_upwards [(lintegral_eq_zero_iff (wilson_continuous_density_continuous hL T).measurable.ennreal_ofReal).mp hzero] with y hy
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp hy) (wilson_continuous_density_nonneg L T y)
  apply eqOn_open_of_ae_eq he ho (wilson_continuous_density_continuous hL T).continuousOn continuous_const.continuousOn
  simpa only [U,mem_compl_iff,mem_closedBall,dist_zero_right,not_le] using hx

theorem wilson_continuous_density_compact {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    HasCompactSupport (wilsonContinuousDensity L T) :=
  HasCompactSupport.intro' (isCompact_closedBall (0:OSFourSpace) (2*L)) isClosed_closedBall
    (fun x hx => wilson_continuous_density_support hL T (by simpa using hx))

/-- The pointwise bound also controls closures at zero and collinear or
repeated displacements, where an unspecified density representative
would give no pointwise bound. -/
theorem wilson_continuous_density_bounded {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, wilsonContinuousDensity L T x ≤ C := by
  let f := wilsonContinuousDensity L T
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:OSFourSpace) (2*L)).bddAbove_image
    (wilson_continuous_density_continuous hL T).continuousOn
  refine ⟨max 0 C,le_max_left _ _,fun x => ?_⟩
  by_cases hx : x ∈ closedBall (0:OSFourSpace) (2*L)
  · exact (hC (mem_image_of_mem _ hx)).trans (le_max_right _ _)
  · rw [wilson_continuous_density_support hL T (by simpa using hx)]
    exact le_max_left _ _

theorem wilson_continuous_density_mass {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    (∫ x, wilsonContinuousDensity L T x) = 1 := by
  have hm : Integrable (wilsonContinuousDensity L T) volume :=
    (wilson_continuous_density_continuous hL T).integrable_of_hasCompactSupport (wilson_continuous_density_compact hL T)
  have h := congrArg (fun μ : Measure OSFourSpace => μ univ) (wilson_continuous_density_law hL T)
  dsimp only at h
  rw [withDensity_apply _ MeasurableSet.univ,restrict_univ,←ofReal_integral_eq_lintegral_ofReal hm
    (Eventually.of_forall (wilson_continuous_density_nonneg L T)),measure_univ] at h
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (wilson_continuous_density_nonneg L T)),ENNReal.toReal_one]
    using congrArg ENNReal.toReal h

end UV
