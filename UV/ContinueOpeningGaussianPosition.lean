import UV.ContinueOpeningNumberFourier
import UV.ContinueOpeningGaussianCarrier
import UV.ContinueOpeningGramTransport
import UV.UnboundedSourceTransport

/-! Identification of the physical oscillator on each number state with the
scaled coordinate in standard Gaussian space. -/

noncomputable section
open MeasureTheory Filter Set
namespace UV

theorem opening_position_unitary_exists :
    ∃ U : OpeningFock ≃ₗᵢ[ℂ] OpeningGaussianCarrier, ∀ t, U (openingFockWave t) = openingGaussianWave t :=
  opening_gram_transport _ _ (Submodule.dense_iff_topologicalClosure_eq_top.mpr opening_fock_wave_total)
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr opening_gaussian_wave_total)
    (fun s t => (opening_fock_wave_gram s t).trans (opening_gaussian_wave_gram s t).symm)

def openingPositionCoordinate (ω x : ℝ) := (Real.sqrt (2*ω))⁻¹ * x

theorem opening_position_coordinate_measurable (ω : ℝ) : Measurable (openingPositionCoordinate ω) :=
  measurable_const.mul measurable_id

theorem opening_position_unitary_number_graph (U : OpeningFock ≃ₗᵢ[ℂ] OpeningGaussianCarrier)
    (hU : ∀ t, U (openingFockWave t) = openingGaussianWave t) (ω : ℝ) (n : ℕ) :
    (openingNumberState n, openingPositionOnCore ω (openingPositionNumberState ω n)) ∈
      (sourceUnitaryRealMultiplier openingGaussianLaw U (openingPositionCoordinate ω)).graph := by
  let J := (Real.sqrt ((n+1:ℕ):ℝ):ℂ) • openingNumberState (n+1) +
         (Real.sqrt (n:ℝ):ℂ) • openingNumberState (n-1)
  have hJ := opening_gaussian_position_of_test_derivative (U (openingNumberState n)) (U J) (by
    intro t
    simp_rw [← hU, U.inner_map_map]
    exact opening_wave_number_derivative n t)
  let u := U (openingNumberState n)
  let v := U (openingPositionOnCore ω (openingPositionNumberState ω n))
  have hv : v = openingPositionScale ω • U J := by simp only [v, openingPositionOnCore_number, map_smul,J]
  have he : (fun x => (openingPositionCoordinate ω x:ℂ) * u x) =ᵐ[openingGaussianLaw] ⇑v := by
    rw [hv]
    filter_upwards [hJ, Lp.coeFn_smul (openingPositionScale ω) (U J)] with x hx hs
    change (x:ℂ) * u x = U J x at hx
    rw [hs]
    simp only [openingPositionCoordinate,Complex.ofReal_mul,Complex.ofReal_inv,Pi.smul_apply,smul_eq_mul,
      openingPositionScale,← hx,mul_assoc]
  apply (sourceUnitaryConjugate_graph_mem_iff U _ _).mpr
  let A := sourceL2Multiplier openingGaussianLaw (fun x => (openingPositionCoordinate ω x:ℂ))
  have hm : u ∈ A.domain := (memLp_congr_ae he).mpr (Lp.memLp v)
  apply A.mem_graph_iff.mpr
  exact ⟨⟨u,hm⟩,rfl,Lp.ext ((sourceL2Multiplier_coe openingGaussianLaw _ ⟨u,hm⟩).trans he)⟩

end UV
