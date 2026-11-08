import UV.StableGreen
import UV.CoordinateSquareFourier

/-! The exact long tail, fifth moments and sixth-moment obstruction for the
actual positive massive Green--Poisson convolution. -/

noncomputable section
open MeasureTheory Real Filter
open scoped Topology ENNReal

namespace UV

theorem stableGreenPoissonEnvelope_integrable {a m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    Integrable (fun y : ScalarMomentum => (1+‖y‖/a)^5) (stableGreenMeasure m) := by
  obtain ⟨c,hc,hexp⟩ := stableGreenMeasure_has_exponential_moment hm
  exact stablePoissonEnvelope_integrable ha hc _ hexp

theorem stableConvolution_exact_tail {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {a m : ℝ} (ha : 0 < a) (hm : 0 < m) (x : ι → ScalarMomentum)
    (hx : Tendsto (fun i => ‖x i‖) l atTop) :
    Tendsto (fun i => ‖x i‖^5 *
      stableCoordinateConvolution a (stableGreenMeasure m) (x i)) l
      (𝓝 (3*a/(4*Real.pi^2*m^2))) := by
  letI := stableGreenMeasure_finite hm
  have ht := stableCoordinateConvolution_exact_tail ha (stableGreenMeasure m)
    (stableGreenPoissonEnvelope_integrable ha hm) x hx
  rw [stableGreenMeasure_real_mass hm] at ht
  convert ht using 1
  congr 1
  ring

theorem stableConvolution_square_moment_integrable {a m : ℝ}
    (ha : 0 < a) (hm : 0 < m) (n : ℕ) (hn : n ≤ 5) :
    Integrable (fun x : ScalarMomentum => ‖x‖^n *
      (stableCoordinateConvolution a (stableGreenMeasure m) x)^2) := by
  letI := stableGreenMeasure_finite hm
  exact stableCoordinateConvolution_square_moment_integrable ha _
    (stableGreenPoissonEnvelope_integrable ha hm) n hn

theorem stableConvolution_square_integrable {a m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    Integrable (fun x : ScalarMomentum =>
      (stableCoordinateConvolution a (stableGreenMeasure m) x)^2) := by
  simpa only [pow_zero, one_mul] using
    stableConvolution_square_moment_integrable ha hm 0 (by norm_num)

theorem stableConvolution_coordinate_six_infinite {a m : ℝ}
    (ha : 0 < a) (hm : 0 < m) :
    (∫⁻ x : ScalarMomentum, ENNReal.ofReal ((x 0)^6 *
      (stableCoordinateConvolution a (stableGreenMeasure m) x)^2)) = ∞ := by
  letI := stableGreenMeasure_finite hm
  have ht := stableConvolution_exact_tail ha hm (fun x : ScalarMomentum => x)
    (Filter.tendsto_comap : Tendsto (fun x : ScalarMomentum => ‖x‖)
      (Filter.comap (fun x : ScalarMomentum => ‖x‖) atTop) atTop)
  obtain ⟨R,hR,hlower⟩ := positive_norm_tail_lower_bound (by positivity) ht
  apply polynomial_tail_coordinate_six_infinite
    (stableCoordinateConvolution_continuous ha _).aestronglyMeasurable
    (by positivity : 0 < (3*a/(4*Real.pi^2*m^2))/2) hR hlower

theorem stableConvolution_fourier_contDiff_five {a m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    ContDiff ℝ 5 (coordinateSquareFourier
      (stableCoordinateConvolution a (stableGreenMeasure m))) := by
  letI := stableGreenMeasure_finite hm
  obtain ⟨K,hK,hdecay⟩ := stableCoordinateConvolution_polynomial_bound ha _
    (stableGreenPoissonEnvelope_integrable ha hm)
  exact coordinateSquareFourier_contDiff_five
    (stableCoordinateConvolution_continuous ha _).aestronglyMeasurable hK hdecay

theorem stableConvolution_fourier_not_contDiffAt_six {a m : ℝ}
    (ha : 0 < a) (hm : 0 < m) :
    ¬ ContDiffAt ℝ 6 (coordinateSquareFourier
      (stableCoordinateConvolution a (stableGreenMeasure m))) 0 := by
  letI := stableGreenMeasure_finite hm
  exact coordinateSquareFourier_not_contDiffAt
    (stableCoordinateConvolution_continuous ha _).measurable
    (stableConvolution_square_integrable ha hm) (stableConvolution_coordinate_six_infinite ha hm)

theorem stableConvolution_fourier_no_holomorphic_square {a m : ℝ}
    (ha : 0 < a) (hm : 0 < m) :
    ¬ ∃ b : ℂ → ℂ, AnalyticAt ℂ b 0 ∧
      (∀ᶠ h : ℝ in 𝓝 0, (b ((h:ℂ)^2)).re =
        (coordinateSquareFourier (stableCoordinateConvolution a (stableGreenMeasure m))
          (scalarAxis h)).re) := by
  letI := stableGreenMeasure_finite hm
  exact coordinateSquareFourier_no_holomorphic_square
    (stableCoordinateConvolution_continuous ha _).measurable
    (stableConvolution_square_integrable ha hm) (stableConvolution_coordinate_six_infinite ha hm)

end UV
