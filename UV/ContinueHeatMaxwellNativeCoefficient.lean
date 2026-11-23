import UV.ContinueHeatMaxwellNativeJet
import UV.ContinueHeatMaxwellPolar

/-! The positive Maxwell soft coefficient is the genuine second
variation of the momentum integral of the complete two-mark kernel. -/

noncomputable section
namespace UV.HeatMaxwell
open UV.RelativeSoft UV.SectorPlane MeasureTheory
open scoped RealInnerProductSpace

local instance continueHeatMaxwellNativeCoefficientMeasurableSpace : MeasurableSpace EuclideanPlaneMomentum := borel _
local instance continueHeatMaxwellNativeCoefficientBorelSpace : BorelSpace EuclideanPlaneMomentum := ⟨rfl⟩

/-- At any mass and width the signed, spin-traced Euclidean coefficient
with the fixed-sector continuum measure equals the positive radial coefficient. -/
theorem heat_native_soft_coefficient {m a : ℝ} (hm : 0<m) (ha : 0<a) :
    (4/(2*Real.pi)^4) * (deriv (deriv (fun t => ∫ k, heatNativeResponse (m*a) k t)) 0 / 2) =
      heatTransverseSoftCoefficient m a := by
  have hma := mul_pos hm ha
  have hp (k : EuclideanPlaneMomentum) : deriv (deriv (heatNativeResponse (m*a) k)) 0=2*heatSectorQuadratic m a k :=
    heat_native_pointwise_second hma k
  have hI := (heat_native_second_integrable hma).div_const 2
  have he (k : EuclideanPlaneMomentum) : deriv (deriv (heatNativeResponse (m*a) k)) 0 / 2=heatSectorQuadratic m a k := by rw [hp];ring
  have I : Integrable (heatSectorQuadratic m a) := hI.congr (Filter.Eventually.of_forall he)
  rw [heat_native_response_integral_second hma,←integral_div]
  simp_rw [he]
  exact heat_sector_polar_coefficient m a I

theorem heat_native_soft_coefficient_pos {m a : ℝ} (hm : 0<m) (ha : 0<a) :
    0 < (4/(2*Real.pi)^4)*(deriv (deriv (fun t => ∫ k, heatNativeResponse (m*a) k t)) 0/2) := by
  rw [heat_native_soft_coefficient hm ha]
  exact heatTransverseSoftCoefficient_pos hm ha

end UV.HeatMaxwell
