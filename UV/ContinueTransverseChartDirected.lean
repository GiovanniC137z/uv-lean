import UV.ContinueTransverseChartMoving
import UV.ContinueTransverseChartPV
import UV.ScalarLineSide

/-! The moving two-normal test in the literal directed quotient. The
two fixed pole units and the positive common height remain unchanged. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory UV.Carrier
open scoped Topology

/-- Both factors are the original vectorial inverses on the same plane,
and the whole two-normal coefficient is transported into the quotient. -/
theorem Plane.transverse_normal_product_directed_moving_boundary {E : Type*} [NormedAddCommGroup E]
    (diamond : Plane E) (ε₁ ε₂ : Evolution) (K : TopologicalSpace.Compacts (ℝ × ℝ))
    {F : ℝ → (ℝ × ℝ) → ℂ} (hF : ContDiff ℝ 2 (Function.uncurry F))
    (hFs : ∀ t p, p ∉ K → F t p = 0) :
    Tendsto (fun h : Height => ∫ p, diamond.poleInverse ε₁ h p.1 *
      diamond.poleInverse ε₂ h p.2 * directed (F h p) ∂transverseNormalVolume) poleBoundaryHeights
      (𝓝 (directed (transverseNormalBoundary (diamond.eta ε₁) (diamond.eta ε₂) (F 0)))) := by
  have H := directed_shell_readout_continuous.continuousAt.tendsto.comp
    (diamond.transverse_normal_product_moving_boundary ε₁ ε₂ K hF hFs)
  refine H.congr fun h => ?_
  have hFC : Continuous (F h) :=
    hF.continuous.comp (continuous_const.prodMk continuous_id)
  have hFS : HasCompactSupport (F h) := HasCompactSupport.intro K.isCompact (hFs h)
  have hPC : Continuous (fun p : ℝ × ℝ => diamond.poleCoefficient ε₁ h p.1 *
      diamond.poleCoefficient ε₂ h p.2) :=
    ((diamond.pole_coefficient_continuous ε₁ h).comp continuous_fst).mul
      ((diamond.pole_coefficient_continuous ε₂ h).comp continuous_snd)
  have hi : Integrable (fun p : ℝ × ℝ => diamond.poleCoefficient ε₁ h p.1 *
      diamond.poleCoefficient ε₂ h p.2 * F h p) transverseNormalVolume :=
    (hPC.mul hFC).integrable_of_hasCompactSupport hFS.mul_left
  change directed (∫ p, diamond.poleCoefficient ε₁ h p.1 *
      diamond.poleCoefficient ε₂ h p.2 * F h p ∂transverseNormalVolume) = _
  rw [← directed_integral hi]
  apply integral_congr_ae
  refine Eventually.of_forall fun p => ?_
  dsimp only
  rw [directed_mul, directed_mul, diamond.pole_coefficient_eq_inv, diamond.pole_coefficient_eq_inv,
    diamond.pole_inverse_complex, diamond.pole_inverse_complex]
  rfl

end UV.SectorPlane
