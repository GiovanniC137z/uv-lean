import UV.GlobalConvergence
import UV.ScalarTube
import UV.PolydiscBudget
import UV.TwoLoopLines
import UV.InverseDenominator

noncomputable section
open MeasureTheory Set Real Filter Metric
open scoped BigOperators Topology InnerProductSpace

namespace UV

abbrev TwoLoopVariables := LoopMomentum × LoopMomentum

def twoLoopTube : Set TubeMomentum := {P | ‖tubeImag P‖ < 1}

theorem twoLoopTube_isOpen : IsOpen twoLoopTube :=
  isOpen_lt tubeImag_continuous.norm continuous_const

def twoLoopDenominator (u : LoopMomentum) (P : TubeMomentum) : ℂ :=
  complexMomentumSquare (fun ν => (u ν : ℂ) + P ν) + 1

theorem twoLoopDenominator_re (u : LoopMomentum) (P : TubeMomentum) :
    (twoLoopDenominator u P).re =
      ‖u + tubeReal P‖ ^ 2 + 1 - ‖tubeImag P‖ ^ 2 := by
  have hr : tubeReal (fun ν => (u ν : ℂ) + P ν) = u + tubeReal P := by
    ext ν
    simp [tubeReal]
  have hi : tubeImag (fun ν => (u ν : ℂ) + P ν) = tubeImag P := by
    ext ν
    simp [tubeImag]
  unfold twoLoopDenominator
  rw [Complex.add_re, Complex.one_re, complexMomentumSquare_re, hr, hi]
  ring

theorem twoLoopDenominator_norm_lower {d : ℝ} (hd : 0 ≤ d)
    {P : TubeMomentum} (hP : ‖tubeImag P‖ ≤ d) (u : LoopMomentum) :
    1 - d ^ 2 ≤ ‖twoLoopDenominator u P‖ := by
  have hr := Complex.re_le_norm (twoLoopDenominator u P)
  rw [twoLoopDenominator_re] at hr
  have hh := mul_nonneg (sub_nonneg.mpr hP) (add_nonneg hd (norm_nonneg (tubeImag P)))
  nlinarith [sq_nonneg ‖u + tubeReal P‖]

theorem twoLoopDenominator_ne_zero {P : TubeMomentum} (hP : P ∈ twoLoopTube)
    (u : LoopMomentum) : twoLoopDenominator u P ≠ 0 := by
  have hl := twoLoopDenominator_norm_lower (norm_nonneg (tubeImag P)) le_rfl u
  have hd : 0 < 1 - ‖tubeImag P‖ ^ 2 := by
    have hp := norm_nonneg (tubeImag P)
    change ‖tubeImag P‖ < 1 at hP
    nlinarith
  exact norm_pos_iff.mp (hd.trans_le hl)

def weightedTwoLoopIntegrand (w : TwoLoopVariables → ℝ) (P : TubeMomentum)
    (k : TwoLoopVariables) : ℂ := (w k : ℂ) / twoLoopDenominator (k.1 - k.2) P

def weightedTwoLoopIntegral (w : TwoLoopVariables → ℝ) (P : TubeMomentum) : ℂ :=
  ∫ k, weightedTwoLoopIntegrand w P k ∂volume.prod volume

theorem weightedTwoLoopIntegrand_measurable (w : TwoLoopVariables → ℝ)
    (hw : Measurable w) (P : TubeMomentum) : Measurable (weightedTwoLoopIntegrand w P) := by
  unfold weightedTwoLoopIntegrand twoLoopDenominator complexMomentumSquare
  fun_prop

theorem weightedTwoLoopIntegrand_norm_bound (w : TwoLoopVariables → ℝ)
    (hpos : ∀ k, 0 ≤ w k) {d : ℝ} (hd : 0 ≤ d) (hd1 : d < 1)
    {P : TubeMomentum} (hP : ‖tubeImag P‖ ≤ d) (k : TwoLoopVariables) :
    ‖weightedTwoLoopIntegrand w P k‖ ≤ w k / (1 - d ^ 2) := by
  unfold weightedTwoLoopIntegrand
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hpos k)]
  have hden : 0 < 1 - d ^ 2 := by nlinarith
  exact div_le_div_of_nonneg_left (hpos k) hden (twoLoopDenominator_norm_lower hd hP _)

theorem weightedTwoLoopIntegrand_integrable (w : TwoLoopVariables → ℝ)
    (hm : Measurable w) (hw : Integrable w (volume.prod volume))
    (hpos : ∀ k, 0 ≤ w k) {P : TubeMomentum} (hP : P ∈ twoLoopTube) :
    Integrable (weightedTwoLoopIntegrand w P) (volume.prod volume) := by
  refine (hw.div_const (1 - ‖tubeImag P‖ ^ 2)).mono'
    (weightedTwoLoopIntegrand_measurable w hm P).aestronglyMeasurable ?_
  exact Eventually.of_forall (weightedTwoLoopIntegrand_norm_bound w hpos
    (norm_nonneg _) hP le_rfl)

theorem weightedTwoLoopIntegral_norm_bound (w : TwoLoopVariables → ℝ)
    (hm : Measurable w) (hw : Integrable w (volume.prod volume))
    (hpos : ∀ k, 0 ≤ w k) {d : ℝ} (hd : 0 ≤ d) (hd1 : d < 1)
    {P : TubeMomentum} (hP : ‖tubeImag P‖ ≤ d) :
    ‖weightedTwoLoopIntegral w P‖ ≤ (∫ k, w k ∂volume.prod volume) / (1 - d ^ 2) := by
  have hPt : P ∈ twoLoopTube := hP.trans_lt hd1
  unfold weightedTwoLoopIntegral
  calc
    _ ≤ ∫ k, ‖weightedTwoLoopIntegrand w P k‖ ∂volume.prod volume := norm_integral_le_integral_norm _
    _ ≤ ∫ k, w k / (1 - d ^ 2) ∂volume.prod volume :=
      integral_mono_ae (weightedTwoLoopIntegrand_integrable w hm hw hpos hPt).norm
        (hw.div_const _) (Eventually.of_forall (weightedTwoLoopIntegrand_norm_bound w hpos hd hd1 hP))
    _ = _ := integral_div _ _

theorem weightedTwoLoopIntegral_differentiableOn (w : TwoLoopVariables → ℝ)
    (hm : Measurable w) (hw : Integrable w (volume.prod volume))
    (hpos : ∀ k, 0 ≤ w k) :
    DifferentiableOn ℂ (weightedTwoLoopIntegral w) twoLoopTube := by
  apply holomorphy_from_local_graph_majorants twoLoopTube_isOpen
  · intro P _
    exact (weightedTwoLoopIntegrand_measurable w hm P).aestronglyMeasurable
  · apply Eventually.of_forall
    intro k P hP
    have hd : DifferentiableAt ℂ (twoLoopDenominator (k.1 - k.2)) P := by
      unfold twoLoopDenominator complexMomentumSquare
      fun_prop
    have hc : DifferentiableAt ℂ (fun _ : TubeMomentum => (w k : ℂ)) P :=
      differentiableAt_const _
    simpa only [div_eq_mul_inv] using
      (hc.mul (hd.inv (twoLoopDenominator_ne_zero hP _))).differentiableWithinAt
  · intro P hP
    let d := (‖tubeImag P‖ + 1) / 2
    have hd : 0 ≤ d := by dsimp [d]; positivity
    have hd1 : d < 1 := by change ‖tubeImag P‖ < 1 at hP; dsimp [d]; linarith
    have hPd : ‖tubeImag P‖ < d := by change ‖tubeImag P‖ < 1 at hP; dsimp [d]; linarith
    have hV : IsOpen {Q : TubeMomentum | ‖tubeImag Q‖ < d} :=
      isOpen_lt tubeImag_continuous.norm continuous_const
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV P hPd
    refine ⟨r, hr, fun Q hQ => (hball hQ).trans hd1,
      (fun k => w k / (1 - d ^ 2)), hw.div_const _, Eventually.of_forall ?_⟩
    intro k Q hQ
    exact weightedTwoLoopIntegrand_norm_bound w hpos hd hd1 (hball hQ).le k

theorem twoLoop_polydisc_imag_bound (p0 : LoopMomentum) {r : ℝ} (hr : 0 ≤ r)
    {P : TubeMomentum} (hP : P ∈ closedPolydisc (complexifyMomentum p0) (fun _ => r)) :
    ‖tubeImag P‖ ^ 2 ≤ 4 * r ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [tubeImag, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ ∑ _ : Fin 4, r ^ 2 := by
      apply Finset.sum_le_sum
      intro ν _
      have hd : ‖P ν - (p0 ν : ℂ)‖ ≤ r := by
        simpa only [dist_eq_norm, complexifyMomentum] using hP ν
      have hi := Complex.abs_im_le_norm (P ν - (p0 ν : ℂ))
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hi
      have ha := hi.trans hd
      have hs : |(P ν).im| ^ 2 ≤ r ^ 2 := (sq_le_sq₀ (abs_nonneg _) hr).mpr ha
      simpa only [sq_abs] using hs
    _ = _ := by simp

theorem twoLoop_polydisc_subset_tube (p0 : LoopMomentum) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1 / 2) :
    closedPolydisc (complexifyMomentum p0) (fun _ => r) ⊆ twoLoopTube := by
  intro P hP
  have hh := twoLoop_polydisc_imag_bound p0 hr.le hP
  change ‖tubeImag P‖ < 1
  nlinarith [norm_nonneg (tubeImag P)]

/-- The source's sharp four-coordinate mixed derivative budget for an actual
integrable nonnegative selected-line weight. -/
theorem weightedTwoLoopIntegral_mixed_derivative_bound
    (w : TwoLoopVariables → ℝ) (hm : Measurable w)
    (hw : Integrable w (volume.prod volume)) (hpos : ∀ k, 0 ≤ w k)
    (p0 : LoopMomentum) {r : ℝ} (hr : 0 < r) (hr1 : r < 1 / 2)
    (α : Fin 4 → ℕ) :
    ‖orderedMixedDeriv α (weightedTwoLoopIntegral w) (complexifyMomentum p0)‖ ≤
      (∏ j, ((α j).factorial : ℝ)) * r⁻¹ ^ (∑ j, α j) *
        ((∫ k, w k ∂volume.prod volume) / (1 - 4 * r ^ 2)) := by
  have hclosed := twoLoop_polydisc_subset_tube p0 hr hr1
  have hb : ∀ P ∈ closedPolydisc (complexifyMomentum p0) (fun _ => r),
      ‖weightedTwoLoopIntegral w P‖ ≤ (∫ k, w k ∂volume.prod volume) / (1 - 4 * r ^ 2) := by
    intro P hP
    have hp : ‖tubeImag P‖ ≤ 2 * r := by
      have hs := twoLoop_polydisc_imag_bound p0 hr.le hP
      nlinarith [norm_nonneg (tubeImag P)]
    have h := weightedTwoLoopIntegral_norm_bound w hm hw hpos (by linarith : 0 ≤ 2 * r)
      (by linarith : 2 * r < 1) hp
    simpa only [show (2 * r) ^ 2 = 4 * r ^ 2 by ring] using h
  have h := ordered_mixed_cauchy_budget_of_differentiable α twoLoopTube_isOpen
    (weightedTwoLoopIntegral_differentiableOn w hm hw hpos) (fun _ => hr) hclosed hb
  simpa only [Finset.prod_pow_eq_pow_sum] using h

/-- The literal complex two-loop amplitude from the source example. -/
def twoLoopComplexAmplitude (P : TubeMomentum) : ℂ :=
  weightedTwoLoopIntegral twoLoopSelectedWeight P


def weightedTwoLoopRealIntegrand (w : TwoLoopVariables → ℝ) (p : LoopMomentum)
    (k : TwoLoopVariables) : ℝ := w k / (1 + ‖k.1 - k.2 + p‖ ^ 2)

def weightedTwoLoopRealIntegral (w : TwoLoopVariables → ℝ) (p : LoopMomentum) : ℝ :=
  ∫ k, weightedTwoLoopRealIntegrand w p k ∂volume.prod volume

theorem weightedTwoLoopRealIntegrand_measurable (w : TwoLoopVariables → ℝ)
    (hm : Measurable w) (p : LoopMomentum) : Measurable (weightedTwoLoopRealIntegrand w p) := by
  unfold weightedTwoLoopRealIntegrand
  fun_prop

theorem weightedTwoLoopRealIntegrand_integrable (w : TwoLoopVariables → ℝ)
    (hm : Measurable w) (hw : Integrable w (volume.prod volume))
    (hpos : ∀ k, 0 ≤ w k) (p : LoopMomentum) :
    Integrable (weightedTwoLoopRealIntegrand w p) (volume.prod volume) := by
  refine hw.mono' (weightedTwoLoopRealIntegrand_measurable w hm p).aestronglyMeasurable ?_
  apply Eventually.of_forall
  intro k
  unfold weightedTwoLoopRealIntegrand
  rw [Real.norm_of_nonneg (div_nonneg (hpos k) (by positivity))]
  exact div_le_self (hpos k) (by nlinarith [sq_nonneg ‖k.1 - k.2 + p‖])

/-- The original nonnegative real comparison amplitude. -/
def twoLoopRealAmplitude (p : LoopMomentum) : ℝ :=
  weightedTwoLoopRealIntegral twoLoopSelectedWeight p

theorem twoLoopComplexAmplitude_differentiableOn :
    DifferentiableOn ℂ twoLoopComplexAmplitude twoLoopTube :=
  weightedTwoLoopIntegral_differentiableOn _ twoLoopSelectedWeight_measurable
    twoLoopSelectedWeight_integrable twoLoopSelectedWeight_nonneg

theorem twoLoopComplexAmplitude_norm_bound {P : TubeMomentum} (hP : P ∈ twoLoopTube) :
    ‖twoLoopComplexAmplitude P‖ ≤
      1 / (768 * Real.pi ^ 4 * (1 - ‖tubeImag P‖ ^ 2)) := by
  have h := weightedTwoLoopIntegral_norm_bound _ twoLoopSelectedWeight_measurable
    twoLoopSelectedWeight_integrable twoLoopSelectedWeight_nonneg
    (norm_nonneg (tubeImag P)) hP le_rfl
  rw [twoLoopSelectedWeight_integral, div_div] at h
  exact h

theorem twoLoopComplexAmplitude_mixed_derivative_bound (p0 : LoopMomentum)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1 / 2) (α : Fin 4 → ℕ) :
    ‖orderedMixedDeriv α twoLoopComplexAmplitude (complexifyMomentum p0)‖ ≤
      ((∏ j, ((α j).factorial : ℝ)) * r⁻¹ ^ (∑ j, α j)) /
        (768 * Real.pi ^ 4 * (1 - 4 * r ^ 2)) := by
  have h := weightedTwoLoopIntegral_mixed_derivative_bound _ twoLoopSelectedWeight_measurable
    twoLoopSelectedWeight_integrable twoLoopSelectedWeight_nonneg p0 hr hr1 α
  rw [twoLoopSelectedWeight_integral, div_div] at h
  convert h using 1
  ring

theorem twoLoopDenominator_real (u p : LoopMomentum) :
    twoLoopDenominator u (complexifyMomentum p) = ((1 + ‖u + p‖ ^ 2 : ℝ) : ℂ) := by
  have hs : (fun ν => (u ν : ℂ) + complexifyMomentum p ν) = complexifyMomentum (u + p) := by
    funext ν
    simp [complexifyMomentum]
  unfold twoLoopDenominator
  rw [hs, complexMomentumSquare_complexify]
  simp only [Complex.ofReal_add, Complex.ofReal_one]
  ring

theorem weightedTwoLoopIntegrand_real (w : TwoLoopVariables → ℝ) (p : LoopMomentum)
    (k : TwoLoopVariables) :
    weightedTwoLoopIntegrand w (complexifyMomentum p) k =
      ((w k / (1 + ‖k.1 - k.2 + p‖ ^ 2) : ℝ) : ℂ) := by
  unfold weightedTwoLoopIntegrand
  rw [twoLoopDenominator_real, Complex.ofReal_div]

theorem twoLoopComplexAmplitude_real (p : LoopMomentum) :
    twoLoopComplexAmplitude (complexifyMomentum p) = (twoLoopRealAmplitude p : ℂ) := by
  unfold twoLoopComplexAmplitude weightedTwoLoopIntegral twoLoopRealAmplitude
    weightedTwoLoopRealIntegral weightedTwoLoopRealIntegrand
  simp_rw [weightedTwoLoopIntegrand_real]
  exact integral_ofReal

def twoLoopGradientSample (w : TwoLoopVariables → ℝ) (p : LoopMomentum)
    (k : TwoLoopVariables) : LoopMomentum :=
  w k • inverseDenominatorGradient (k.1 - k.2 + p)

def weightedTwoLoopGradient (w : TwoLoopVariables → ℝ) (p : LoopMomentum) : LoopMomentum :=
  ∫ k, twoLoopGradientSample w p k ∂volume.prod volume

def twoLoopDual : LoopMomentum →L[ℝ] (LoopMomentum →L[ℝ] ℝ) :=
  (InnerProductSpace.toDual ℝ LoopMomentum).toContinuousLinearEquiv.toContinuousLinearMap

theorem twoLoopDual_apply (u h : LoopMomentum) : twoLoopDual u h = ⟪u, h⟫_ℝ := by
  simp [twoLoopDual, InnerProductSpace.toDual_apply]

theorem twoLoopDual_norm (u : LoopMomentum) : ‖twoLoopDual u‖ = ‖u‖ :=
  (InnerProductSpace.toDual ℝ LoopMomentum).norm_map u

theorem twoLoopGradientSample_measurable (w : TwoLoopVariables → ℝ) (hm : Measurable w)
    (p : LoopMomentum) : Measurable (twoLoopGradientSample w p) := by
  unfold twoLoopGradientSample
  fun_prop

theorem twoLoopGradientSample_norm_bound (w : TwoLoopVariables → ℝ)
    (hpos : ∀ k, 0 ≤ w k) (p : LoopMomentum) (k : TwoLoopVariables) :
    ‖twoLoopGradientSample w p k‖ ≤ inverseDenominatorGradientBound * w k := by
  unfold twoLoopGradientSample
  rw [norm_smul, Real.norm_of_nonneg (hpos k)]
  exact (mul_le_mul_of_nonneg_left (inverseDenominatorGradient_norm_le _) (hpos k)).trans_eq (by ring)

theorem twoLoopGradientSample_integrable (w : TwoLoopVariables → ℝ)
    (hm : Measurable w) (hw : Integrable w (volume.prod volume))
    (hpos : ∀ k, 0 ≤ w k) (p : LoopMomentum) :
    Integrable (twoLoopGradientSample w p) (volume.prod volume) :=
  (hw.const_mul inverseDenominatorGradientBound).mono'
    (twoLoopGradientSample_measurable w hm p).aestronglyMeasurable
    (Eventually.of_forall (twoLoopGradientSample_norm_bound w hpos p))

theorem weightedTwoLoopRealIntegrand_hasFDerivAt (w : TwoLoopVariables → ℝ)
    (p : LoopMomentum) (k : TwoLoopVariables) :
    HasFDerivAt (fun q => weightedTwoLoopRealIntegrand w q k)
      (twoLoopDual (twoLoopGradientSample w p k)) p := by
  have hs : HasFDerivAt (fun q : LoopMomentum => k.1 - k.2 + q)
      (ContinuousLinearMap.id ℝ LoopMomentum) p := (hasFDerivAt_id p).const_add _
  have hg := (inverseDenominator_hasGradientAt (k.1 - k.2 + p)).hasFDerivAt.comp p hs
  convert hg.const_mul (w k) using 1
  ext h
  simp [twoLoopDual, twoLoopGradientSample, InnerProductSpace.toDual_apply]

theorem weightedTwoLoopRealIntegrand_lipschitz (w : TwoLoopVariables → ℝ)
    (hpos : ∀ k, 0 ≤ w k) (p q : LoopMomentum) (k : TwoLoopVariables) :
    ‖weightedTwoLoopRealIntegrand w q k - weightedTwoLoopRealIntegrand w p k‖ ≤
      (inverseDenominatorGradientBound * w k) * ‖q - p‖ := by
  have hh := inverseDenominator_lipschitz (k.1 - k.2 + q) (k.1 - k.2 + p)
  rw [show (k.1 - k.2 + q) - (k.1 - k.2 + p) = q - p by abel] at hh
  calc
    _ = w k * |inverseDenominator (k.1 - k.2 + q) - inverseDenominator (k.1 - k.2 + p)| := by
      simp only [weightedTwoLoopRealIntegrand, div_eq_mul_inv, inverseDenominator,
        ← mul_sub, norm_mul, Real.norm_of_nonneg (hpos k), Real.norm_eq_abs]
    _ ≤ w k * (inverseDenominatorGradientBound * ‖q - p‖) :=
      mul_le_mul_of_nonneg_left hh (hpos k)
    _ = _ := by ring

/-- The actual graph gradient is the weighted integral of the actual third-line
gradient, derived by dominated differentiation. -/
theorem weightedTwoLoopReal_hasGradientAt (w : TwoLoopVariables → ℝ)
    (hm : Measurable w) (hw : Integrable w (volume.prod volume))
    (hpos : ∀ k, 0 ≤ w k) (p : LoopMomentum) :
    HasGradientAt (weightedTwoLoopRealIntegral w) (weightedTwoLoopGradient w p) p := by
  have hDmeas : AEStronglyMeasurable (fun k => twoLoopDual (twoLoopGradientSample w p k))
      (volume.prod volume) :=
    (twoLoopDual.continuous.measurable.comp (twoLoopGradientSample_measurable w hm p)).aestronglyMeasurable
  obtain ⟨_, hd⟩ := hasFDerivAt_integral_of_dominated_loc_of_lip'
    (F := weightedTwoLoopRealIntegrand w) (x₀ := p) (ε := 1)
    (bound := fun k => inverseDenominatorGradientBound * w k)
    (F' := fun k => twoLoopDual (twoLoopGradientSample w p k)) zero_lt_one
    (fun q _ => (weightedTwoLoopRealIntegrand_measurable w hm q).aestronglyMeasurable)
    (weightedTwoLoopRealIntegrand_integrable w hm hw hpos p) hDmeas
    (Eventually.of_forall fun k q _ => weightedTwoLoopRealIntegrand_lipschitz w hpos p q k)
    (hw.const_mul _) (Eventually.of_forall (weightedTwoLoopRealIntegrand_hasFDerivAt w p))
  have hcomm := twoLoopDual.integral_comp_comm (twoLoopGradientSample_integrable w hm hw hpos p)
  rw [hcomm] at hd
  exact hd

theorem weightedTwoLoopReal_gradient_eq (w : TwoLoopVariables → ℝ)
    (hm : Measurable w) (hw : Integrable w (volume.prod volume))
    (hpos : ∀ k, 0 ≤ w k) (p : LoopMomentum) :
    gradient (weightedTwoLoopRealIntegral w) p = weightedTwoLoopGradient w p :=
  (weightedTwoLoopReal_hasGradientAt w hm hw hpos p).gradient

theorem weightedTwoLoopGradient_norm_bound (w : TwoLoopVariables → ℝ)
    (hw : Integrable w (volume.prod volume)) (hpos : ∀ k, 0 ≤ w k) (p : LoopMomentum) :
    ‖weightedTwoLoopGradient w p‖ ≤
      inverseDenominatorGradientBound * ∫ k, w k ∂volume.prod volume := by
  unfold weightedTwoLoopGradient
  calc
    _ ≤ ∫ k, inverseDenominatorGradientBound * w k ∂volume.prod volume :=
      norm_integral_le_of_norm_le (hw.const_mul _)
        (Eventually.of_forall (twoLoopGradientSample_norm_bound w hpos p))
    _ = _ := integral_const_mul _ _

theorem weightedTwoLoopReal_fderiv_norm_bound (w : TwoLoopVariables → ℝ)
    (hm : Measurable w) (hw : Integrable w (volume.prod volume))
    (hpos : ∀ k, 0 ≤ w k) (p : LoopMomentum) :
    ‖fderiv ℝ (weightedTwoLoopRealIntegral w) p‖ ≤
      inverseDenominatorGradientBound * ∫ k, w k ∂volume.prod volume := by
  rw [(weightedTwoLoopReal_hasGradientAt w hm hw hpos p).hasFDerivAt.fderiv]
  change ‖twoLoopDual (weightedTwoLoopGradient w p)‖ ≤ _
  rw [twoLoopDual_norm]
  exact weightedTwoLoopGradient_norm_bound w hw hpos p

theorem weightedTwoLoopReal_lipschitz (w : TwoLoopVariables → ℝ)
    (hm : Measurable w) (hw : Integrable w (volume.prod volume))
    (hpos : ∀ k, 0 ≤ w k) (p q : LoopMomentum) :
    |weightedTwoLoopRealIntegral w p - weightedTwoLoopRealIntegral w q| ≤
      (inverseDenominatorGradientBound * ∫ k, w k ∂volume.prod volume) * ‖p - q‖ := by
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (s := (univ : Set LoopMomentum))
    (f := weightedTwoLoopRealIntegral w) (x := q) (y := p)
    (fun x _ => (weightedTwoLoopReal_hasGradientAt w hm hw hpos x).differentiableAt)
    (fun x _ => weightedTwoLoopReal_fderiv_norm_bound w hm hw hpos x)
    convex_univ (mem_univ _) (mem_univ _)
  simpa only [Real.norm_eq_abs] using h

theorem twoLoopGradientSample_difference_bound (w : TwoLoopVariables → ℝ)
    (hpos : ∀ k, 0 ≤ w k) (p q : LoopMomentum) (k : TwoLoopVariables) :
    ‖twoLoopGradientSample w p k - twoLoopGradientSample w q k‖ ≤
      (2 * ‖p - q‖) * w k := by
  unfold twoLoopGradientSample
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hpos k)]
  have hh := inverseDenominatorGradient_lipschitz (k.1 - k.2 + p) (k.1 - k.2 + q)
  rw [show (k.1 - k.2 + p) - (k.1 - k.2 + q) = p - q by abel] at hh
  exact (mul_le_mul_of_nonneg_left hh (hpos k)).trans_eq (by ring)

theorem weightedTwoLoopGradient_lipschitz (w : TwoLoopVariables → ℝ)
    (hm : Measurable w) (hw : Integrable w (volume.prod volume))
    (hpos : ∀ k, 0 ≤ w k) (p q : LoopMomentum) :
    ‖weightedTwoLoopGradient w p - weightedTwoLoopGradient w q‖ ≤
      (2 * ∫ k, w k ∂volume.prod volume) * ‖p - q‖ := by
  unfold weightedTwoLoopGradient
  calc
    _ = ‖∫ k, twoLoopGradientSample w p k - twoLoopGradientSample w q k ∂volume.prod volume‖ := by
      rw [integral_sub (twoLoopGradientSample_integrable w hm hw hpos p)
        (twoLoopGradientSample_integrable w hm hw hpos q)]
    _ ≤ ∫ k, (2 * ‖p - q‖) * w k ∂volume.prod volume :=
      norm_integral_le_of_norm_le (hw.const_mul _)
        (Eventually.of_forall (twoLoopGradientSample_difference_bound w hpos p q))
    _ = _ := by rw [integral_const_mul]; ring

/-- The graph's first-order remainder is obtained by integrating the actual
pointwise quadratic remainder, with the exact factor one. -/
theorem weightedTwoLoopReal_taylor_error (w : TwoLoopVariables → ℝ)
    (hm : Measurable w) (hw : Integrable w (volume.prod volume))
    (hpos : ∀ k, 0 ≤ w k) (p h : LoopMomentum) :
    |weightedTwoLoopRealIntegral w (p + h) - weightedTwoLoopRealIntegral w p -
      ⟪weightedTwoLoopGradient w p, h⟫_ℝ| ≤
      (∫ k, w k ∂volume.prod volume) * ‖h‖ ^ 2 := by
  let Lh : LoopMomentum →L[ℝ] ℝ := (ContinuousLinearMap.apply ℝ ℝ h).comp twoLoopDual
  have hLh (u : LoopMomentum) : Lh u = ⟪u, h⟫_ℝ := twoLoopDual_apply u h
  have hG := twoLoopGradientSample_integrable w hm hw hpos p
  have hfun : (fun k => Lh (twoLoopGradientSample w p k)) =
      (fun k => ⟪twoLoopGradientSample w p k, h⟫_ℝ) := funext fun k => hLh _
  have hi : Integrable (fun k => ⟪twoLoopGradientSample w p k, h⟫_ℝ)
      (volume.prod volume) := by
    rw [← hfun]
    exact Lh.integrable_comp hG
  have he : (∫ k, ⟪twoLoopGradientSample w p k, h⟫_ℝ ∂volume.prod volume) =
      ⟪weightedTwoLoopGradient w p, h⟫_ℝ := by
    calc
      _ = ∫ k, Lh (twoLoopGradientSample w p k) ∂volume.prod volume := by rw [hfun]
      _ = Lh (weightedTwoLoopGradient w p) := Lh.integral_comp_comm hG
      _ = _ := hLh _
  let rem : TwoLoopVariables → ℝ := fun k => weightedTwoLoopRealIntegrand w (p + h) k -
    weightedTwoLoopRealIntegrand w p k - ⟪twoLoopGradientSample w p k, h⟫_ℝ
  have hrem : ∀ k, ‖rem k‖ ≤ ‖h‖ ^ 2 * w k := by
    intro k
    have heq : rem k = w k *
        (inverseDenominator ((k.1 - k.2 + p) + h) - inverseDenominator (k.1 - k.2 + p) -
          ⟪inverseDenominatorGradient (k.1 - k.2 + p), h⟫_ℝ) := by
      dsimp only [rem, weightedTwoLoopRealIntegrand, twoLoopGradientSample]
      rw [show k.1 - k.2 + (p + h) = (k.1 - k.2 + p) + h by abel,
        real_inner_smul_left]
      unfold inverseDenominator
      ring
    rw [heq, norm_mul, Real.norm_of_nonneg (hpos k), Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (inverseDenominator_taylor_error (k.1 - k.2 + p) h)
      (hpos k)).trans_eq (by ring)
  have hid : (∫ k, rem k ∂volume.prod volume) =
      weightedTwoLoopRealIntegral w (p + h) - weightedTwoLoopRealIntegral w p -
        ⟪weightedTwoLoopGradient w p, h⟫_ℝ := by
    dsimp only [rem]
    have hpint := weightedTwoLoopRealIntegrand_integrable w hm hw hpos (p + h)
    have h0int := weightedTwoLoopRealIntegrand_integrable w hm hw hpos p
    have hout : (∫ k, weightedTwoLoopRealIntegrand w (p + h) k -
        weightedTwoLoopRealIntegrand w p k - ⟪twoLoopGradientSample w p k, h⟫_ℝ
        ∂volume.prod volume) =
        (∫ k, weightedTwoLoopRealIntegrand w (p + h) k - weightedTwoLoopRealIntegrand w p k
          ∂volume.prod volume) - ∫ k, ⟪twoLoopGradientSample w p k, h⟫_ℝ ∂volume.prod volume :=
      integral_sub (f := fun k => weightedTwoLoopRealIntegrand w (p + h) k -
        weightedTwoLoopRealIntegrand w p k) (g := fun k => ⟪twoLoopGradientSample w p k, h⟫_ℝ)
        (hpint.sub h0int) hi
    have hin : (∫ k, weightedTwoLoopRealIntegrand w (p + h) k - weightedTwoLoopRealIntegrand w p k
        ∂volume.prod volume) = weightedTwoLoopRealIntegral w (p + h) - weightedTwoLoopRealIntegral w p :=
      integral_sub hpint h0int
    rw [hout, hin, he]
  rw [← hid, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ k, ‖h‖ ^ 2 * w k ∂volume.prod volume :=
      norm_integral_le_of_norm_le (hw.const_mul _) (Eventually.of_forall hrem)
    _ = _ := by rw [integral_const_mul]; ring

theorem twoLoopRealAmplitude_hasGradientAt (p : LoopMomentum) :
    HasGradientAt twoLoopRealAmplitude (weightedTwoLoopGradient twoLoopSelectedWeight p) p :=
  weightedTwoLoopReal_hasGradientAt _ twoLoopSelectedWeight_measurable
    twoLoopSelectedWeight_integrable twoLoopSelectedWeight_nonneg p

theorem twoLoopRealAmplitude_gradient_bound (p : LoopMomentum) :
    ‖gradient twoLoopRealAmplitude p‖ ≤
      (9 / (8 * Real.sqrt 3)) * (1 / (768 * Real.pi ^ 4)) := by
  rw [(twoLoopRealAmplitude_hasGradientAt p).gradient]
  have h := weightedTwoLoopGradient_norm_bound _ twoLoopSelectedWeight_integrable
    twoLoopSelectedWeight_nonneg p
  simpa only [inverseDenominatorGradientBound, twoLoopSelectedWeight_integral] using h

theorem twoLoopRealAmplitude_lipschitz (p q : LoopMomentum) :
    |twoLoopRealAmplitude p - twoLoopRealAmplitude q| ≤
      (9 / (6144 * Real.sqrt 3 * Real.pi ^ 4)) * ‖p - q‖ := by
  have h := weightedTwoLoopReal_lipschitz _ twoLoopSelectedWeight_measurable
    twoLoopSelectedWeight_integrable twoLoopSelectedWeight_nonneg p q
  rw [twoLoopSelectedWeight_integral] at h
  convert h using 1
  unfold inverseDenominatorGradientBound
  field_simp
  ring

theorem twoLoopRealAmplitude_gradient_lipschitz (p q : LoopMomentum) :
    ‖gradient twoLoopRealAmplitude p - gradient twoLoopRealAmplitude q‖ ≤
      ‖p - q‖ / (384 * Real.pi ^ 4) := by
  rw [(twoLoopRealAmplitude_hasGradientAt p).gradient, (twoLoopRealAmplitude_hasGradientAt q).gradient]
  have h := weightedTwoLoopGradient_lipschitz _ twoLoopSelectedWeight_measurable
    twoLoopSelectedWeight_integrable twoLoopSelectedWeight_nonneg p q
  rw [twoLoopSelectedWeight_integral] at h
  convert h using 1
  field_simp
  ring

theorem twoLoopRealAmplitude_taylor_error (p h : LoopMomentum) :
    |twoLoopRealAmplitude (p + h) - twoLoopRealAmplitude p -
      ⟪gradient twoLoopRealAmplitude p, h⟫_ℝ| ≤ ‖h‖ ^ 2 / (768 * Real.pi ^ 4) := by
  rw [(twoLoopRealAmplitude_hasGradientAt p).gradient]
  have hh := weightedTwoLoopReal_taylor_error _ twoLoopSelectedWeight_measurable
    twoLoopSelectedWeight_integrable twoLoopSelectedWeight_nonneg p h
  rw [twoLoopSelectedWeight_integral] at hh
  convert hh using 1
  ring

/-- The full named two-loop complex/real certificate, with the literal
selected-line weight and all four source stability constants. -/
theorem two_loop_complex_certificate :
    DifferentiableOn ℂ twoLoopComplexAmplitude twoLoopTube ∧
      (∀ P ∈ twoLoopTube, ‖twoLoopComplexAmplitude P‖ ≤
        1 / (768 * Real.pi ^ 4 * (1 - ‖tubeImag P‖ ^ 2))) ∧
      (∀ (p0 : LoopMomentum) (r : ℝ), 0 < r → r < 1 / 2 → ∀ α : Fin 4 → ℕ,
        ‖orderedMixedDeriv α twoLoopComplexAmplitude (complexifyMomentum p0)‖ ≤
          ((∏ j, ((α j).factorial : ℝ)) * r⁻¹ ^ (∑ j, α j)) /
            (768 * Real.pi ^ 4 * (1 - 4 * r ^ 2))) ∧
      (∀ p, twoLoopComplexAmplitude (complexifyMomentum p) = (twoLoopRealAmplitude p : ℂ)) ∧
      (∀ p, ‖gradient twoLoopRealAmplitude p‖ ≤
        (9 / (8 * Real.sqrt 3)) * (1 / (768 * Real.pi ^ 4))) ∧
      (∀ p q, |twoLoopRealAmplitude p - twoLoopRealAmplitude q| ≤
        (9 / (6144 * Real.sqrt 3 * Real.pi ^ 4)) * ‖p - q‖) ∧
      (∀ p q, ‖gradient twoLoopRealAmplitude p - gradient twoLoopRealAmplitude q‖ ≤
        ‖p - q‖ / (384 * Real.pi ^ 4)) ∧
      (∀ p h, |twoLoopRealAmplitude (p + h) - twoLoopRealAmplitude p -
        ⟪gradient twoLoopRealAmplitude p, h⟫_ℝ| ≤ ‖h‖ ^ 2 / (768 * Real.pi ^ 4)) := by
  exact ⟨twoLoopComplexAmplitude_differentiableOn,
    fun _ hP => twoLoopComplexAmplitude_norm_bound hP,
    fun p0 _ hr hr1 α => twoLoopComplexAmplitude_mixed_derivative_bound p0 hr hr1 α,
    twoLoopComplexAmplitude_real, twoLoopRealAmplitude_gradient_bound,
    twoLoopRealAmplitude_lipschitz, twoLoopRealAmplitude_gradient_lipschitz,
    twoLoopRealAmplitude_taylor_error⟩

end UV
