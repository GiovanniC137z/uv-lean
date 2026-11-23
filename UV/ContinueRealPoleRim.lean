import UV.ContinueWilsonChargedRim
import UV.ContinueRealPoleResidue

/-! Matrix residues of the physical nonreal Schur inverse along the two
characters of the directed pole on a fixed sector plane. -/

noncomputable section
open Filter UV.Carrier
open scoped Topology InnerProductSpace
namespace UV.SectorPlane

variable {S H : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Type*} [NormedAddCommGroup E] {B : H →ₗ.[ℂ] H} {p : ℝ}

/-- A first-order slot residue at p = −E₀ is recovered in operator norm on
both characters. Each frequency in the approximating pair uses the actual
nonreal resolvent of the possibly unbounded boundary B. -/
theorem Plane.closing_physical_pole_residue (diamond : Plane E) (ε : Evolution)
    (A : S →L[ℂ] S) (T : S →L[ℂ] H) (hB : IsSelfAdjoint B)
    (R₀ : ClosingUnboundedResolvent B (p : ℂ)) (Z : S →L[ℂ] S)
    (hZ : Tendsto (fun z : ℂ => (z - (p : ℂ)) • Ring.inverse (closingRealPolePencil A T R₀ z))
      (𝓝[≠] (p : ℂ)) (𝓝 Z)) :
    Tendsto (fun h : Height =>
      let z := quotientCharacterEquiv (diamond.poleDenominator ε h p)
      let hn := diamond.pole_characters_nonreal ε p h
      ((z.1 - (p : ℂ)) • Ring.inverse
          (closingInverseSlot A T (closingNonrealResolvent B hB z.1 hn.1).map z.1),
       (z.2 - (p : ℂ)) • Ring.inverse
          (closingInverseSlot A T (closingNonrealResolvent B hB z.2 hn.2).map z.2)))
      poleBoundaryHeights (𝓝 (Z, Z)) := by
  apply diamond.pole_nonreal_character_limits ε p (G := fun z hz =>
    (z - (p : ℂ)) • Ring.inverse (closingInverseSlot A T (closingNonrealResolvent B hB z hz).map z)) hZ
  filter_upwards [closing_real_pole_pencil_nonreal A T hB R₀] with z h
  intro hz
  rw [h hz]

end UV.SectorPlane
