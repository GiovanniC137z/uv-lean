import UV.ContinueRealPoleRim
import UV.ContinueRealPoleAtom
import UV.ContinueCayleyBoundaryEquivalence
import UV.ScalarKernelBoundary

/-! Identification of the first-order slot residue with the spectral atom
of the same boundary channel, in every entry on the locked sector plane. -/

noncomputable section
open Filter MeasureTheory UV.Carrier
open scoped Topology InnerProductSpace
namespace UV.SectorPlane

variable {S H E ι : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [Fintype ι]

/-- Any matrix measure with the specified nonreal slot data has atom Z at
energy e if Z is the measured residue at p = −e. -/
theorem Plane.closing_residue_atom_entry (diamond : Plane E) (ε : Evolution) (e : ℝ)
    (b : OrthonormalBasis ι ℂ S) (M : Matrix ι ι (ComplexMeasure ℝ))
    (A : S →L[ℂ] S) (T : S →L[ℂ] H) (B : H →ₗ.[ℂ] H) (hB : IsSelfAdjoint B)
    (R₀ : ClosingUnboundedResolvent B ((-e : ℝ) : ℂ)) (Z : S →L[ℂ] S)
    (hZ : Tendsto (fun z : ℂ => (z - ((-e : ℝ) : ℂ)) • Ring.inverse (closingRealPolePencil A T R₀ z))
      (𝓝[≠] ((-e : ℝ) : ℂ)) (𝓝 Z))
    (hG : ∀ (z : ℂ) (hz : z.im ≠ 0) (i j : ι),
      closingMeasureEntryIntegral M (fun x : ℝ => (z + (x : ℂ))⁻¹) i j =
        ⟪b i, Ring.inverse (closingInverseSlot A T (closingNonrealResolvent B hB z hz).map z) (b j)⟫_ℂ)
    (i j : ι) : M i j {e} = ⟪b i, Z (b j)⟫_ℂ := by
  letI : poleBoundaryHeights.NeBot := pole_boundary_heights_neBot
  have hphysical := (diamond.closing_physical_pole_residue ε A T hB R₀ Z hZ).fst_nhds
  have hread : Continuous (fun C : S →L[ℂ] S => ⟪b i, C (b j)⟫_ℂ) := by fun_prop
  have hs := (hread.tendsto Z).comp hphysical
  have hspec := (diamond.closing_measured_pole_atom ε M e i j).fst_nhds
  apply tendsto_nhds_unique hspec
  apply hs.congr'
  filter_upwards with h
  let z := (quotientCharacterEquiv (diamond.poleDenominator ε h (-e))).1
  have hn : z.im ≠ 0 := (diamond.pole_characters_nonreal ε (-e) h).1
  change ⟪b i, ((z - ((-e : ℝ) : ℂ)) • Ring.inverse
      (closingInverseSlot A T (closingNonrealResolvent B hB z hn).map z)) (b j)⟫_ℂ =
    (z + (e : ℂ)) * closingMeasureEntryIntegral M (fun x : ℝ => (z + (x : ℂ))⁻¹) i j
  rw [hG z hn i j]
  simp [inner_smul_right]

/-- One positive normalized measure represents the entire finite-slot
response, both moment matrices and every isolated first-order pole.
On the given sector plane the measure is chosen before the energy e. -/
theorem closing_boundary_matrix_measure_with_atoms [DecidableEq ι] [FiniteDimensional ℂ S]
    (diamond : Plane E) (ε : Evolution) (b : OrthonormalBasis ι ℂ S) (A : S →L[ℂ] S) (hA : IsSelfAdjoint A)
    (T : S →L[ℂ] H) (B : H →ₗ.[ℂ] H) (hB : IsSelfAdjoint B) :
    ∃ M : Matrix ι ι (ComplexMeasure ℝ), ClosingPositiveMatrixMeasure M ∧ ClosingNormalizedMatrixMeasure M ∧
      Integrable (fun x : ℝ => x^2) (closingTraceLaw M) ∧
      (∀ (z : ℂ) (hz : z.im ≠ 0) (i j : ι),
        closingMeasureEntryIntegral M (fun x : ℝ => (z + (x : ℂ))⁻¹) i j =
          ⟪b i, Ring.inverse (closingInverseSlot A T (closingNonrealResolvent B hB z hz).map z) (b j)⟫_ℂ) ∧
      (∀ i j : ι, closingMeasureEntryIntegral M (fun x : ℝ => (x : ℂ)) i j = ⟪b i, A (b j)⟫_ℂ) ∧
      (∀ i j : ι, closingMeasureEntryIntegral M (fun x : ℝ => (x : ℂ)^2) i j =
        ⟪b i, (A * A + T.adjoint.comp T) (b j)⟫_ℂ) ∧
      (∀ (e : ℝ) (R₀ : ClosingUnboundedResolvent B ((-e : ℝ) : ℂ))
        (Z : S →L[ℂ] S), Tendsto (fun z : ℂ => (z - ((-e : ℝ) : ℂ)) • Ring.inverse
          (closingRealPolePencil A T R₀ z)) (𝓝[≠] ((-e : ℝ) : ℂ)) (𝓝 Z) →
          ∀ i j : ι, M i j {e} = ⟪b i, Z (b j)⟫_ℂ) := by
  obtain ⟨M, hpos, hnorm, h₂, hG, hfirst, hsecond⟩ := closing_boundary_matrix_measure b A hA T B hB
  refine ⟨M, hpos, hnorm, h₂, hG, hfirst, hsecond, ?_⟩
  intro e R₀ Z hZ
  exact diamond.closing_residue_atom_entry ε e b M A T B hB R₀ Z hZ hG

end UV.SectorPlane
