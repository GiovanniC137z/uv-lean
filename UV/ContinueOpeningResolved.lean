import UV.ContinueOpeningGaussianPosition
import UV.ContinueOpeningCoreMaximal
import UV.ContinueOpeningCoordinateMoment
import UV.ContinueOpeningPVMTransport

/-! A normalized spectral resolution of the physical oscillator position and
its inclusive on-cut number probabilities. -/

noncomputable section
namespace UV

theorem opening_gaussian_position_identification (U : OpeningFock ≃ₗᵢ[ℂ] OpeningGaussianCarrier)
    (hU : ∀ t, U (openingFockWave t) = openingGaussianWave t) (ω : ℝ) :
    sourceUnitaryRealMultiplier openingGaussianLaw U (openingPositionCoordinate ω) =
      OpeningPositionClosure ω :=
  opening_position_eq_closure_of_number_graph ω _
    (sourceUnitaryRealMultiplier_selfAdjoint _ U _ (opening_position_coordinate_measurable ω))
    (opening_position_unitary_number_graph U hU ω)

/-- The spectral measure and its maximal first moment are constructed for the
closure of the raising/lowering operator in the physical number space. -/
def openingCanonicalResolution (ω : ℝ) : SourceSpectralResolution (OpeningPositionClosure ω) :=
  let U := Classical.choose opening_position_unitary_exists
  (opening_gaussian_position_identification U (Classical.choose_spec opening_position_unitary_exists) ω) ▸
    (openingPulledResolution U (openingCoordinateResolution openingGaussianLaw _ (opening_position_coordinate_measurable ω)) :
      SourceSpectralResolution (sourceUnitaryRealMultiplier openingGaussianLaw U (openingPositionCoordinate ω)))

theorem opening_canonical_on_cut_poisson {ω ξ b S : ℝ} (hω : 0 < ω)
    (hphase : ξ^2/(2*ω) = b*S) (n : ℕ) :
    ‖inner ℂ (openingNumberState n) (openingPositionSpectralExponential
        (openingCanonicalResolution ω) ξ (openingNumberState 0))‖^2 =
      ProbabilityTheory.poissonPMFReal (b*S).toNNReal n :=
  openingPositionSpectralExponential_on_cut_poisson _ hω hphase n

end UV
