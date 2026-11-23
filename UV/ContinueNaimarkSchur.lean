import UV.ContinueNaimarkDomain
import UV.ContinueSourceReviewSchurWard
import UV.ContinueSourceReviewSchurMultiplier

/-! The general measure-to-Schur direction of the positive boundary
realization, with the physical orthogonal boundary and nonreal complex
carrier frequencies. -/

noncomputable section
open MeasureTheory Matrix Set ContinuousLinearMap Filter
open scoped InnerProductSpace
namespace UV.SectorPlane

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S] [FiniteDimensional ℂ S]

/-- The integral of a complex scalar weight against a matrix entry, using
the proven common Radon–Nikodym density of that very entry. -/
def closingMeasureEntryIntegral (M : Matrix ι ι (ComplexMeasure ℝ)) (f : ℝ → ℂ) (i j : ι) : ℂ :=
  ∫ x, f x * closingMatrixDensity M x i j ∂closingControlMeasure M

/-- The recovered Hilbert-space energy has exactly the first and second
moment entries, including complex off-diagonal terms. Its resolvent
on a slot gives the Cauchy transform at every nonreal frequency. -/
theorem closing_naimark_schur_realization (M : Matrix ι ι (ComplexMeasure ℝ)) (hM : ClosingPositiveMatrixMeasure M)
    (hn : ClosingNormalizedMatrixMeasure M) (b : OrthonormalBasis ι ℂ S)
    (h₂ : Integrable (fun x : ℝ => x^2) (closingTraceLaw M)) :
    let J := closingNaimarkLift M hM hn b
    let K := closingNaimarkEnergy M
    ∃ U : ClosingUnboundedBlocks K J,
      (∀ (z : ℂ) (hz : z.im ≠ 0) (i j : ι),
        let R := (closingNonrealResolvent U.boundaryRestriction U.restriction_selfAdjoint z hz).map
        ⟪b i, Ring.inverse (closingInverseSlot U.A U.physicalColumn R z) (b j)⟫_ℂ =
          closingMeasureEntryIntegral M (fun x => (z + (x : ℂ))⁻¹) i j) ∧
      (∀ i j : ι, ⟪b i, U.A (b j)⟫_ℂ =
        closingMeasureEntryIntegral M (fun x => (x : ℂ)) i j) ∧
      (∀ i j : ι, ⟪b i, (U.A*U.A + U.physicalColumn.adjoint.comp U.physicalColumn) (b j)⟫_ℂ =
        closingMeasureEntryIntegral M (fun x => (x : ℂ)^2) i j) := by
  let J := closingNaimarkLift M hM hn b
  let K := closingNaimarkEnergy M
  have hK := closing_naimark_energy_selfAdjoint M
  have hJ := closing_naimark_slot_domain M hM hn b h₂
  let U := closingUnboundedBlocks K hK J hJ
  let μ := closingNaimarkMeasure M
  let L := closingUnboundedColumn K J hJ
  have hc (i : ι) : J (b i) = closingNaimarkColumn M hM i := closing_naimark_lift_basis M hM hn b i
  have hL (i : ι) : (L (b i) : ι × ℝ → ℂ) =ᵐ[μ] (fun p => (p.2 : ℂ) * closingColumnValue M i p) := by
    have hl := sourceL2Multiplier_coe μ (fun x : ι × ℝ => (x.2 : ℂ)) ⟨J (b i), hJ _⟩
    change (L (b i) : ι × ℝ → ℂ) =ᵐ[μ] (fun p => (p.2 : ℂ) * (J (b i)) p) at hl
    rw [hc] at hl
    filter_upwards [hl,closing_naimark_column_ae M hM i] with p h₁ h₂
    exact h₁.trans (congrArg ((p.2 : ℂ) * ·) h₂)
  obtain ⟨hA,hT⟩ := U.energy_moments hJ
  refine ⟨U, ?_, ?_, ?_⟩
  · intro z hz i j
    dsimp only
    let RK := closingNonrealResolvent K hK z hz
    rw [← closing_orthogonal_boundary_schur U z hz RK]
    change ⟪b i, J.toContinuousLinearMap.adjoint (RK.map (J (b j)))⟫_ℂ = _
    rw [adjoint_inner_right]
    change ⟪J (b i), RK.map (J (b j))⟫_ℂ = _
    rw [hc i, hc j]
    apply closing_column_weight_pairing
    filter_upwards [closing_multiplier_resolvent_ae μ Prod.snd z hz RK (closingNaimarkColumn M hM j),
      closing_naimark_column_ae M hM j] with p h₁ h₂
    exact h₁.trans (congrArg ((z+(p.2 : ℂ))⁻¹ * ·) h₂)
  · intro i j
    rw [hA, ContinuousLinearMap.comp_apply, adjoint_inner_right]
    change ⟪J (b i), L (b j)⟫_ℂ = _
    rw [hc i]
    exact closing_column_weight_pairing M hM i j _ _ (hL j)
  · intro i j
    rw [←hT, ContinuousLinearMap.comp_apply, adjoint_inner_right]
    have he := closing_weighted_columns_pairing M hM i j (fun x => (x : ℂ))
      (fun x => (x : ℂ)) _ _ (hL i) (hL j)
    simpa only [Complex.star_def,Complex.conj_ofReal,←pow_two,closingMeasureEntryIntegral] using he

end UV.SectorPlane
