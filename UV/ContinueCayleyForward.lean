import UV.ContinueCayleyForwardMoments
import UV.ContinueCayleyMatrixEnergy

/-! Forward spectral-measure construction for finite isometric slots
in the domain of an arbitrary self-adjoint signed-energy operator. -/

noncomputable section
namespace UV.SectorPlane
open MeasureTheory Matrix
open scoped InnerProductSpace

variable {ι S H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup S] [InnerProductSpace ℂ S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- From the Hamiltonian and its domain-slot inclusion alone one obtains
a positive, countably additive, identity-normalized matrix law on signed real
energies. Its first two moment matrices and every nonreal Cauchy-resolvent
entry are those of this same Hamiltonian and the specified isometric slots. -/
theorem closing_cayley_forward (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K)
    (J : S →ₗᵢ[ℂ] H) (b : OrthonormalBasis ι ℂ S) (hJ : ∀ v, J v∈K.domain) :
    let x := fun i => (⟨J (b i),hJ (b i)⟩ : K.domain)
    ∃ M : Matrix ι ι (ComplexMeasure ℝ), ClosingPositiveMatrixMeasure M ∧ ClosingNormalizedMatrixMeasure M ∧
      Integrable (fun E : ℝ => E^2) (closingTraceLaw M) ∧
      (∀ (z : ℂ) (hz : z.im≠0) (i j : ι), closingMeasureEntryIntegral M (fun E : ℝ => (z+(E:ℂ))⁻¹) i j =
          ⟪J (b i),(closingNonrealResolvent K hK z hz).map (J (b j))⟫_ℂ) ∧
      (∀ i j : ι, closingMeasureEntryIntegral M (fun E : ℝ => (E:ℂ)) i j = ⟪J (b i),K (x j)⟫_ℂ) ∧
      (∀ i j : ι, closingMeasureEntryIntegral M (fun E : ℝ => (E:ℂ)^2) i j = ⟪K (x i),K (x j)⟫_ℂ) := by
  dsimp only
  let x := fun i => (⟨J (b i),hJ (b i)⟩ : K.domain)
  let M := closingDomainMatrixMeasure K hK x
  have ho : Orthonormal ℂ (fun i => (x i:H)) := by
    apply orthonormal_iff_ite.mpr
    exact fun i j => (J.inner_map_map (b i) (b j)).trans (orthonormal_iff_ite.mp b.orthonormal i j)
  have hM : ClosingPositiveMatrixMeasure M := closing_domain_matrix_positive K hK x
  have hq (v : ι→ℂ) (s : Set ℝ) (hs : MeasurableSet s) :
      closingFiniteForm (fun i j => M i j s) v=((closingDomainSlotLaw K hK (∑ i,v i • x i)).real s:ℂ) :=
    closing_domain_matrix_quadratic K hK x v s hs
  obtain ⟨hn,h₂,hR⟩ := closing_forward_family K hK x ho M hM hq
  exact ⟨M,hM,hn,h₂,hR,closing_forward_family_moments K hK x M hM h₂ hq⟩

end UV.SectorPlane
