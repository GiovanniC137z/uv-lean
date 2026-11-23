import UV.ContinueThinCurrentSchwartz

/-! The exact inverse-transform trace along an original unit tangent.
The transverse coordinates have the Lebesgue normalization inherited
from the orthonormal four-plane. -/

noncomputable section

open MeasureTheory Filter Set Bornology
open scoped BigOperators InnerProductSpace RealInnerProductSpace FourierTransform SchwartzMap Topology ENNReal

namespace UV

abbrev ThinFrequencyThree := Fin 3 → ℝ
abbrev ThinCurrentBasis := OrthonormalBasis (Fin 4) ℝ ThinCurrentPlane

def thinFrequencyPoint (b : ThinCurrentBasis) (s : ℝ) (q : ThinFrequencyThree) : ThinCurrentPlane :=
  b.repr.symm (WithLp.toLp 2 (Fin.cons s q))

private def thinFrequencyChart (b : ThinCurrentBasis) :
    ThinCurrentPlane ≃ᵐ ℝ × ThinFrequencyThree :=
  b.measurableEquiv.trans ((EuclideanSpace.measurableEquiv (Fin 4)).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0))

private theorem thinFrequencyChart_preserving (b : ThinCurrentBasis) :
    MeasurePreserving (thinFrequencyChart b) volume
      ((volume : Measure ℝ).prod (volume : Measure ThinFrequencyThree)) :=
  ((volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).comp
    (EuclideanSpace.volume_preserving_measurableEquiv (Fin 4))).comp
    b.measurePreserving_measurableEquiv

private theorem thinFrequencyChart_symm (b : ThinCurrentBasis) (s : ℝ) (q : ThinFrequencyThree) :
    (thinFrequencyChart b).symm (s,q) = thinFrequencyPoint b s q := by
  change b.repr.symm (WithLp.toLp 2 ((0 : Fin 4).insertNth s q)) = _
  rw [Fin.insertNth_zero']
  rfl

theorem thinFrequencyPoint_continuous (b : ThinCurrentBasis) :
    Continuous (fun sq : ℝ × ThinFrequencyThree => thinFrequencyPoint b sq.1 sq.2) := by
  change Continuous (b.repr.symm ∘ WithLp.toLp 2 ∘ (fun sq : ℝ × ThinFrequencyThree =>
    Fin.cons sq.1 sq.2))
  apply b.repr.symm.continuous.comp (PiLp.continuous_toLp 2 _ |>.comp ?_)
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using (continuous_fst : Continuous (Prod.fst : ℝ × ThinFrequencyThree → ℝ))
  · simpa only [Fin.cons_succ] using (continuous_apply j).comp
      (continuous_snd : Continuous (Prod.snd : ℝ × ThinFrequencyThree → ThinFrequencyThree))

private theorem thinFrequency_inner (b : ThinCurrentBasis) (s : ℝ) (q : ThinFrequencyThree) :
    inner ℝ (thinFrequencyPoint b s q) (b 0) = s := by
  rw [real_inner_comm, ← b.repr_apply_apply]
  simp [thinFrequencyPoint]

theorem thinFrequency_norm_le (b : ThinCurrentBasis) (s : ℝ) (q : ThinFrequencyThree) :
    ‖q‖ ≤ ‖thinFrequencyPoint b s q‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  change ‖q i‖ ≤ ‖b.repr.symm (WithLp.toLp 2 (Fin.cons s q))‖
  rw [LinearIsometryEquiv.norm_map]
  exact PiLp.norm_apply_le (p := 2) (β := fun _ : Fin 4 => ℝ)
    (WithLp.toLp 2 (Fin.cons s q)) i.succ

def thinFrequencyMarginal (b : ThinCurrentBasis) (φ : ThinCurrentPlane → ℝ) (s : ℝ) : ℂ :=
  ∫ q : ThinFrequencyThree, (φ (thinFrequencyPoint b s q) : ℂ)

private theorem thinFrequencyMarginal_integrable (b : ThinCurrentBasis) {φ : ThinCurrentPlane → ℝ}
    (hφI : Integrable φ) : Integrable (thinFrequencyMarginal b φ) := by
  have hφC : Integrable (fun p => (φ p : ℂ)) := hφI.ofReal
  have h := ((thinFrequencyChart_preserving b).symm (thinFrequencyChart b)).integrable_comp_emb
    (thinFrequencyChart b).symm.measurableEmbedding |>.mpr hφC
  have h' := h.integral_prod_left
  change Integrable (fun s : ℝ => ∫ q : ThinFrequencyThree,
      (φ ((thinFrequencyChart b).symm (s,q)) : ℂ)) at h'
  simp_rw [thinFrequencyChart_symm] at h'
  exact h'

private theorem thinFrequencyMarginal_continuous (b : ThinCurrentBasis) {φ : ThinCurrentPlane → ℝ}
    (hφ : Continuous φ) {B : ℝ} (hb : ∀ p, |φ p| ≤ B)
    (hs : ∀ p, φ p ≠ 0 → ‖p‖ < 2) : Continuous (thinFrequencyMarginal b φ) := by
  let A : Set ThinFrequencyThree := Metric.closedBall 0 2
  let μ : Measure ThinFrequencyThree := volume.restrict A
  haveI : IsFiniteMeasure μ :=
    ⟨by simp only [μ, Measure.restrict_apply_univ]; exact (isCompact_closedBall (0 : ThinFrequencyThree) 2).measure_lt_top⟩
  have hcut (s : ℝ) : thinFrequencyMarginal b φ s =
      ∫ q : ThinFrequencyThree, (φ (thinFrequencyPoint b s q) : ℂ) ∂μ := by
    unfold thinFrequencyMarginal
    rw [← integral_indicator measurableSet_closedBall]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro q
    by_cases hq : q ∈ A
    · rw [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_notMem hq]
      have hp : φ (thinFrequencyPoint b s q) = 0 := by
        by_contra hp
        apply hq
        exact Metric.mem_closedBall.mpr (by
          rw [dist_zero_right]
          exact (thinFrequency_norm_le b s q).trans ((hs _ hp).le))
      simp [hp]
  change Continuous (fun s => thinFrequencyMarginal b φ s)
  simp_rw [hcut]
  apply continuous_iff_continuousAt.mpr
  intro s
  have hjoint := (Complex.continuous_ofReal.comp hφ).comp (thinFrequencyPoint_continuous b)
  refine tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := 𝓝 s) (fun _ => B) ?_ ?_ (integrable_const _) ?_
  · apply Eventually.of_forall
    intro t
    exact (hjoint.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · apply Eventually.of_forall
    intro t
    exact Eventually.of_forall fun q => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hb (thinFrequencyPoint b t q)
  · apply Eventually.of_forall
    intro q
    exact (hjoint.comp (continuous_id.prodMk continuous_const)).continuousAt.tendsto

private theorem thinFrequencyMarginal_fourierInv (b : ThinCurrentBasis) {φ : ThinCurrentPlane → ℝ}
    (hφI : Integrable φ) (z : ℝ) :
    𝓕⁻ (thinFrequencyMarginal b φ) z = 𝓕⁻ (fun p => (φ p : ℂ)) (z • b 0) := by
  rw [Real.fourierIntegralInv_eq', Real.fourierIntegralInv_eq']
  let f : ThinCurrentPlane → ℂ := fun p =>
    Complex.exp ((2 * Real.pi * inner ℝ p (z • b 0) : ℝ) * Complex.I) * (φ p : ℂ)
  have hf : Integrable f := by
    have hm : AEStronglyMeasurable f volume := by
      refine (Continuous.aestronglyMeasurable (show Continuous (fun p : ThinCurrentPlane =>
        Complex.exp ((2 * Real.pi * inner ℝ p (z • b 0) : ℝ) * Complex.I)) by fun_prop)).mul hφI.ofReal.aestronglyMeasurable
    refine hφI.norm.mono' hm (Eventually.of_forall fun p => ?_)
    simp [f, Complex.norm_exp, Complex.mul_re]
  have hp := (thinFrequencyChart_preserving b).symm (thinFrequencyChart b)
  have hi := (hp.integrable_comp_emb ((thinFrequencyChart b).symm.measurableEmbedding)).mpr hf
  change _ = ∫ p, f p
  rw [← hp.integral_comp' f]
  change _ = ∫ x, (f ∘ (thinFrequencyChart b).symm) x ∂((volume : Measure ℝ).prod volume)
  rw [integral_prod _ hi]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro s
  change Complex.exp ((2 * Real.pi * inner ℝ s z : ℝ) * Complex.I) •
    (∫ q : ThinFrequencyThree, (φ (thinFrequencyPoint b s q) : ℂ)) =
    ∫ q : ThinFrequencyThree, f ((thinFrequencyChart b).symm (s,q))
  rw [smul_eq_mul, ← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro q
  dsimp only
  rw [thinFrequencyChart_symm]
  simp only [f, real_inner_smul_right, thinFrequency_inner, RCLike.inner_apply, conj_trivial]

/-- Integrating the inverse Fourier transform along an original unit
tangent is precisely the slice at zero transverse frequency coordinate. -/
theorem thinWindowInverse_lineTrace (b : ThinCurrentBasis) {φ : ThinCurrentPlane → ℝ}
    (hφ : Continuous φ) (hφI : Integrable φ) {B : ℝ} (hb : ∀ p, |φ p| ≤ B)
    (hs : ∀ p, φ p ≠ 0 → ‖p‖ < 2)
    (hK : ∃ K : 𝓢(ThinCurrentPlane, ℂ), thinWindowInverse φ = K) :
    (∫ z : ℝ, thinWindowInverse φ (z • b 0)) =
      (((2 * Real.pi) ^ 3)⁻¹ : ℝ) • thinFrequencyMarginal b φ 0 := by
  obtain ⟨K, hK⟩ := hK
  obtain ⟨_, dom, hdi, hdom⟩ := thinSchwartz_kernel_controls K
  have hline : Integrable (fun z : ℝ => thinWindowInverse φ (z • b 0)) := by
    rw [hK]
    refine hdi.mono' (K.continuous.comp (continuous_id.smul continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun z => hdom _ z ?_)
    rw [norm_smul, Real.norm_eq_abs, b.orthonormal.norm_eq_one, mul_one]
  let c : ℝ := ((2 * Real.pi) ^ 4)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have heq (z : ℝ) :
      thinWindowInverse φ (z • b 0) =
        c • 𝓕⁻ (thinFrequencyMarginal b φ) (thinFourierScale * z) := by
    rw [thinWindowInverse_eq_fourier, thinFrequencyMarginal_fourierInv b hφI,
      smul_smul]
  have hFTI : Integrable (𝓕⁻ (thinFrequencyMarginal b φ)) := by
    apply (integrable_comp_mul_left_iff (𝓕⁻ (thinFrequencyMarginal b φ))
      thinFourierScale_pos.ne').mp
    apply (hline.smul c⁻¹).congr
    exact Eventually.of_forall fun z => by
      change c⁻¹ • thinWindowInverse φ (z • b 0) =
        𝓕⁻ (thinFrequencyMarginal b φ) (thinFourierScale * z)
      rw [heq, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  have hF : Integrable (𝓕 (thinFrequencyMarginal b φ)) := by
    have hi := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_emb
      (Homeomorph.neg ℝ).measurableEmbedding |>.mpr hFTI
    apply hi.congr
    apply Eventually.of_forall
    intro z
    change 𝓕⁻ (thinFrequencyMarginal b φ) (-z) = 𝓕 (thinFrequencyMarginal b φ) z
    rw [Real.fourierIntegralInv_eq_fourierIntegral_neg, neg_neg]
  have hinv := (thinFrequencyMarginal_integrable b hφI).fourier_inversion_inv hF (v := (0 : ℝ))
    (thinFrequencyMarginal_continuous b hφ hb hs).continuousAt
  have hval : (∫ z : ℝ, 𝓕⁻ (thinFrequencyMarginal b φ) z) = thinFrequencyMarginal b φ 0 := by
    rw [Real.fourierIntegral_eq'] at hinv
    simpa using hinv
  simp_rw [heq]
  rw [integral_smul, Measure.integral_comp_mul_left _ thinFourierScale,
    abs_of_pos (inv_pos.mpr thinFourierScale_pos), hval, smul_smul]
  congr 1
  unfold c thinFourierScale
  field_simp [Real.pi_ne_zero]

end UV
