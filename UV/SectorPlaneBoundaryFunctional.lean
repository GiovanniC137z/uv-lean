import UV.SectorPlaneTestSpace
import UV.ScalarKernelBoundary

/-! An order-two estimate on each fixed compact set for one-sided
four-momentum boundary values. The domain contains every C² test supported there. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped UV.SectorPlane Topology BoundedContinuousFunction

private theorem compact_test_integrable_mul (K : TopologicalSpace.Compacts MassiveMomentum)
    {W : MassiveMomentum → ℂ} (hW : IntegrableOn W (K : Set MassiveMomentum)) (f : CompactMomentumTest K) :
    IntegrableOn (fun q => f.value q * W q) (K : Set MassiveMomentum) :=
  hW.bdd_mul f.val.1.continuous.aestronglyMeasurable ⟨_, f.val.1.norm_coe_le_norm⟩

/-- The continuous linear functional of a locally integrable coefficient at fixed height. -/
theorem compact_momentum_integral_exists (K : TopologicalSpace.Compacts MassiveMomentum)
    (W : MassiveMomentum → ℂ) (hW : IntegrableOn W (K : Set MassiveMomentum)) :
    ∃ T : CompactMomentumTest K →L[ℂ] ℂ, ∀ f : CompactMomentumTest K, T f = ∫ q, f.value q * W q := by
  let L : CompactMomentumTest K →ₗ[ℂ] ℂ := {
    toFun := fun f => ∫ q in (K : Set MassiveMomentum), f.value q * W q
    map_add' := fun f g => by
      change (∫ q in (K : Set MassiveMomentum), (f.value q + g.value q) * W q) = _
      simp only [add_mul, integral_add (compact_test_integrable_mul K hW f) (compact_test_integrable_mul K hW g)]
    map_smul' := fun c f => by
      change (∫ q in (K : Set MassiveMomentum), c * f.value q * W q) = c * _
      simp only [mul_assoc, integral_const_mul] }
  have hb (f : CompactMomentumTest K) : ‖L f‖ ≤ (∫ q in (K : Set MassiveMomentum), ‖W q‖) * ‖f‖ := by
    change ‖∫ q in (K : Set MassiveMomentum), f.value q * W q‖ ≤ _
    calc
      _ ≤ ∫ q in (K : Set MassiveMomentum), ‖f.value q * W q‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ q in (K : Set MassiveMomentum), ‖f‖ * ‖W q‖ := by
        apply integral_mono (compact_test_integrable_mul K hW f).norm (hW.norm.const_mul _)
        intro q
        change ‖f.value q * W q‖ ≤ ‖f‖ * ‖W q‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right ((f.val.1.norm_coe_le_norm q).trans (le_max_left _ _)) (norm_nonneg _)
      _ = _ := by rw [integral_const_mul, mul_comm]
  refine ⟨L.mkContinuous _ hb, fun f => ?_⟩
  rw [LinearMap.mkContinuous_apply]
  change (∫ q in (K : Set MassiveMomentum), f.value q * W q) = _
  exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun q hq => by
    change f.val.1 q * W q = 0
    rw [f.property.1 q hq, zero_mul])

/-- Pointwise boundary convergence at all compact C² tests yields one continuous
linear functional, by uniform boundedness on the complete fixed-support test space. -/
theorem compact_momentum_boundary_functional (K : TopologicalSpace.Compacts MassiveMomentum)
    (W : Height → MassiveMomentum → ℂ) (hW : ∀ h, IntegrableOn (W h) (K : Set MassiveMomentum))
    (hV : ∀ f : CompactMomentumTest K, ∃ z : ℂ,
      Tendsto (fun h => ∫ q, f.value q * W h q) poleBoundaryHeights (𝓝 z)) :
    ∃ T : CompactMomentumTest K →L[ℂ] ℂ, ∀ f : CompactMomentumTest K,
      Tendsto (fun h => ∫ q, f.value q * W h q) poleBoundaryHeights (𝓝 (T f)) := by
  letI : poleBoundaryHeights.NeBot := pole_boundary_heights_neBot
  choose V hV using hV
  choose L hL using fun h => compact_momentum_integral_exists K (W h) (hW h)
  have H : Tendsto (fun h f => L h f) poleBoundaryHeights (𝓝 V) := by
    apply tendsto_pi_nhds.mpr
    exact fun f => (hV f).congr fun h => (hL h f).symm
  exact ⟨continuousLinearMapOfTendsto L H, hV⟩

/-- Two support choices containing the same test give exactly the same boundary. -/
theorem compact_momentum_boundary_agrees {K J : TopologicalSpace.Compacts MassiveMomentum}
    {f : CompactMomentumTest K} {g : CompactMomentumTest J} (hfg : f.value = g.value)
    {W : Height → MassiveMomentum → ℂ} {z v : ℂ}
    (hf : Tendsto (fun h => ∫ q, f.value q * W h q) poleBoundaryHeights (𝓝 z))
    (hg : Tendsto (fun h => ∫ q, g.value q * W h q) poleBoundaryHeights (𝓝 v)) : z = v := by
  letI : poleBoundaryHeights.NeBot := pole_boundary_heights_neBot
  rw [hfg] at hf
  exact tendsto_nhds_unique hf hg

theorem compact_momentum_boundary_order_two (K : TopologicalSpace.Compacts MassiveMomentum)
    (T : CompactMomentumTest K →L[ℂ] ℂ) (f : CompactMomentumTest K) :
    ‖T f‖ ≤ ‖T‖ * max ‖f.val.1‖ (max ‖f.val.2.1‖ ‖f.val.2.2‖) := T.le_opNorm f

end UV.SectorPlane
