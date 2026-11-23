import UV.ContinuePoleResidueLowerBound
import UV.ContinueRealPoleResidue

/-! Directional residues on the fixed carrier-frequency chart for a
possibly unbounded self-adjoint boundary generator. -/

noncomputable section
open Filter
open scoped Topology InnerProductSpace

namespace UV.SectorPlane

variable {S H : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For a real pole at p = −E₀ and a unit vector v in its possibly degenerate
kernel, the actual diagonal residue is real and lies between
(1 + ‖(B + p)⁻¹ T v‖²)⁻¹ and one. The lower endpoint is attained exactly
when v is an eigenvector of the residue with that weight. -/
theorem closing_unbounded_pole_residue_lower_bound {A : S →L[ℂ] S} {B : H →ₗ.[ℂ] H} {p : ℝ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (T : S →L[ℂ] H)
    (R₀ : ClosingUnboundedResolvent B (p : ℂ)) (Z : S →L[ℂ] S)
    (v : S) (hv : ‖v‖ = 1) (hk : closingRealPolePencil A T R₀ (p : ℂ) v = 0)
    (hu : ∀ᶠ z in 𝓝[≠] (p : ℂ), IsUnit (closingRealPolePencil A T R₀ z))
    (hZ : Tendsto (fun z : ℂ => (z - (p : ℂ)) • Ring.inverse (closingRealPolePencil A T R₀ z))
      (𝓝[≠] (p : ℂ)) (𝓝 Z)) :
    let r := closingSlotResidue T R₀.map v
    (⟪v, Z v⟫_ℂ).im = 0 ∧ r ≤ (⟪v, Z v⟫_ℂ).re ∧ (⟪v, Z v⟫_ℂ).re ≤ 1 ∧
      ((⟪v, Z v⟫_ℂ).re = r ↔ Z v = (r : ℂ) • v) := by
  obtain ⟨hs, _, _, hi⟩ := closing_unbounded_pole_measured_charge hA hB T R₀ 1 Z hu hZ
  exact closing_compressed_residue_direction T R₀.map (closing_real_pole_map_selfAdjoint hB R₀)
    _ Z (inverse_pole_projection_selfAdjoint _) hs (by simpa only [Complex.ofReal_one, one_smul] using hi)
    v hv (inverse_pole_projection_fixes hk)

end UV.SectorPlane
