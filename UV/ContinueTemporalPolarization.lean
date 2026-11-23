import UV.SectorPlaneGaugeData
import UV.ContinueTemporalFlux

/-! The spatially transverse Abelian polarization on one Euclidean
sector-plane chart. -/

noncomputable section

namespace UV.SectorPlane

open scoped RealInnerProductSpace BigOperators

def spatialCurvatureNormSq (p u : Spatial) : ℝ :=
  (∑ i : Fin 3, ∑ j : Fin 3, (p i*u j-p j*u i)^2)/2

theorem spatial_curvature_norm_sq (p u : Spatial) :
    spatialCurvatureNormSq p u = ‖p‖^2*‖u‖^2 - (inner ℝ p u)^2 := by
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  change (∑ i : Fin 3, ∑ j : Fin 3, (p i*u j-p j*u i)^2)/2 =
    (∑ i : Fin 3, ‖p i‖^2)*(∑ i : Fin 3, ‖u i‖^2) -
      (∑ i : Fin 3, u i * p i)^2
  simp only [Fin.sum_univ_three,Real.norm_eq_abs,sq_abs]
  ring

theorem transverse_normal_energy_density (n u : UnitVector Spatial)
    (hu : inner ℝ n.val u.val = 0) (k ω U dU a bₛ bₜ : ℝ) :
    a * ‖dU • u.val‖^2 + bₛ * spatialCurvatureNormSq (k • n.val) (U • u.val) +
      bₜ * ‖(ω*U) • u.val‖^2 =
      a*dU^2 + (bₛ*k^2 + bₜ*ω^2)*U^2 := by
  rw [spatial_curvature_norm_sq]
  simp only [norm_smul,Real.norm_eq_abs,u.property,n.property,mul_one,sq_abs,
    real_inner_smul_left,real_inner_smul_right,hu,mul_zero,zero_pow (by decide : 2 ≠ 0),sub_zero]
  ring

theorem Plane.transverse_normal_carrier_pole {E : Type*} [NormedAddCommGroup E]
    (diamond : Plane E) (ε : Evolution) (h : Height)
    (n : UnitVector Spatial) (k ω : ℝ) :
    diamond.poleDenominator ε h (shellSquare ω (k • n.val)) =
      algebraMap ℂ UV.Carrier.QuotientCarrier (ω^2-k^2 : ℝ) +
        algebraMap ℂ UV.Carrier.QuotientCarrier
          (Complex.I * ((diamond.eta ε * (h : ℝ) : ℝ) : ℂ)) * poleRoot := by
  rw [shellSquare,norm_smul,Real.norm_eq_abs,n.property,mul_one,sq_abs]
  exact diamond.pole_denominator_literal ε h _

end UV.SectorPlane
