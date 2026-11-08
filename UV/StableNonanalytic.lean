import UV.StableCovariance
import UV.StableConvolutionRegularity
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-! The literal stable-half scalar bubble is C^5 and is not C^6 at zero.
All Fourier identities, the exact coordinate tail and the divergent sixth
moment are derived from the actual positive heat-mixture measures. -/

noncomputable section
open MeasureTheory Real Filter
open scoped Topology ENNReal

namespace UV

theorem stableCoordinateCovariance_exact_tail {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {a m : ℝ} (ha : 0 < a) (hm : 0 < m)
    (x : ι → ScalarMomentum) (hx : Tendsto (fun i => ‖x i‖) l atTop) :
    Tendsto (fun i => ‖x i‖^5 * stableCoordinateCovariance a m (x i)) l
      (𝓝 (3*a/(4*Real.pi^2*m^2))) := stableConvolution_exact_tail ha hm x hx

theorem stableCoordinateCovariance_asymptotic {a m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    Asymptotics.IsEquivalent (Filter.comap (fun x : ScalarMomentum => ‖x‖) atTop)
      (stableCoordinateCovariance a m)
      (fun x : ScalarMomentum => (3*a/(4*Real.pi^2*m^2)) / ‖x‖^5) := by
  let l := Filter.comap (fun x : ScalarMomentum => ‖x‖) atTop
  let c : ℝ := 3*a/(4*Real.pi^2*m^2)
  have hc : 0 < c := by dsimp [c]; positivity
  have hn : ∀ᶠ x : ScalarMomentum in l, 0 < ‖x‖ :=
    (Filter.tendsto_comap : Tendsto (fun x : ScalarMomentum => ‖x‖) l atTop).eventually
      (eventually_gt_atTop 0)
  apply (Asymptotics.isEquivalent_iff_tendsto_one (hn.mono fun x hx => by
    exact (div_pos hc (pow_pos hx 5)).ne')).mpr
  have ht := (stableCoordinateCovariance_exact_tail ha hm (fun x : ScalarMomentum => x)
    (Filter.tendsto_comap : Tendsto (fun x : ScalarMomentum => ‖x‖) l atTop)).div_const c
  simp only [show 3*a/(4*Real.pi^2*m^2) = c from rfl, div_self hc.ne'] at ht
  convert ht using 1
  funext x
  dsimp only [Pi.div_apply, c]
  field_simp

theorem stableBubble_contDiff_five {a m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    ContDiff ℝ 5 (scalarBubble a 0 m) := by
  have he : scalarBubble a 0 m = fun P =>
      (coordinateSquareFourier (stableCoordinateConvolution a (stableGreenMeasure m)) P).re := by
    funext P
    simpa only [stableCoordinateCovariance, Complex.ofReal_re] using
      congrArg Complex.re (scalarBubble_stable_coordinate_square ha hm P)
  rw [he]
  exact Complex.reCLM.contDiff.comp (stableConvolution_fourier_contDiff_five ha hm)

theorem stableBubble_not_contDiffAt_six {a m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    ¬ ContDiffAt ℝ 6 (scalarBubble a 0 m) 0 := by
  intro hf
  apply stableConvolution_fourier_not_contDiffAt_six ha hm
  have he : (fun P => (scalarBubble a 0 m P : ℂ)) =
      coordinateSquareFourier (stableCoordinateConvolution a (stableGreenMeasure m)) := by
    funext P
    exact scalarBubble_stable_coordinate_square ha hm P
  rw [← he]
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp 0 hf

theorem scalarAxis_continuous : Continuous scalarAxis := by
  have he : scalarAxis = fun h : ℝ => h • scalarAxis 1 := by
    funext h
    ext i
    simp [scalarAxis, EuclideanSpace.single_apply]
  rw [he]
  exact continuous_id.smul continuous_const

theorem stableBubble_no_holomorphic_squared_momentum {a m : ℝ}
    (ha : 0 < a) (hm : 0 < m) :
    ¬ ∃ b : ℂ → ℂ, AnalyticAt ℂ b 0 ∧
      (∀ᶠ P : ScalarMomentum in 𝓝 0,
        b (((‖P‖^2 : ℝ) : ℂ)) = (scalarBubble a 0 m P : ℂ)) := by
  rintro ⟨b,hb,heq⟩
  apply stableConvolution_fourier_no_holomorphic_square ha hm
  refine ⟨b,hb,?_⟩
  have hzero : scalarAxis 0 = 0 := by
    ext i
    simp [scalarAxis, EuclideanSpace.single_apply]
  have ht : Tendsto scalarAxis (𝓝 0) (𝓝 0) := by
    simpa only [hzero] using scalarAxis_continuous.tendsto 0
  filter_upwards [ht.eventually heq] with h hh
  have he := scalarBubble_stable_coordinate_square ha hm (scalarAxis h)
  have hsq : (((‖scalarAxis h‖^2 : ℝ):ℂ)) = (h:ℂ)^2 := by
    rw [scalarAxis_norm, sq_abs, Complex.ofReal_pow]
  rw [hsq] at hh
  exact congrArg Complex.re (hh.trans he)

/-- Proposition stable-bubble-nonanalytic, including the exact coordinate
coefficient and exclusion of a local holomorphic squared-momentum extension. -/
theorem stable_bubble_nonanalytic {a m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    (∀ P, Integrable (scalarBubbleIntegrand a 0 m P)) ∧
    ContDiff ℝ 5 (scalarBubble a 0 m) ∧
    ¬ ContDiffAt ℝ 6 (scalarBubble a 0 m) 0 ∧
    Asymptotics.IsEquivalent (Filter.comap (fun x : ScalarMomentum => ‖x‖) atTop)
      (stableCoordinateCovariance a m)
      (fun x : ScalarMomentum => (3*a/(4*Real.pi^2*m^2)) / ‖x‖^5) ∧
    ¬ (∃ b : ℂ → ℂ, AnalyticAt ℂ b 0 ∧
      (∀ᶠ P : ScalarMomentum in 𝓝 0,
        b (((‖P‖^2 : ℝ) : ℂ)) = (scalarBubble a 0 m P : ℂ))) := by
  exact ⟨fun P => scalarBubbleIntegrand_integrable ha (by norm_num) hm P,
    stableBubble_contDiff_five ha hm, stableBubble_not_contDiffAt_six ha hm,
    stableCoordinateCovariance_asymptotic ha hm, stableBubble_no_holomorphic_squared_momentum ha hm⟩

end UV
