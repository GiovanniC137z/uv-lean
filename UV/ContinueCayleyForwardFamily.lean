import UV.ContinueCayleyForwardPairing
import UV.ContinueCayleySlot

/-! The normalized matrix law, trace moment and full complex resolvent
follow from its setwise quadratic laws for finite domain slots. -/

noncomputable section
namespace UV.SectorPlane
open MeasureTheory Set Filter Matrix
open scoped InnerProductSpace ComplexConjugate ENNReal

variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem closing_forward_family (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (x : ι→K.domain)
    (horth : Orthonormal ℂ (fun i => (x i:H))) (M : Matrix ι ι (ComplexMeasure ℝ))
    (hM : ClosingPositiveMatrixMeasure M)
    (hquad : ∀ y : ι→ℂ, ∀ s, MeasurableSet s → closingFiniteForm (fun i j => M i j s) y =
      ((closingDomainSlotLaw K hK (∑ i,y i • x i)).real s:ℂ)) :
    ClosingNormalizedMatrixMeasure M ∧ Integrable (fun t : ℝ => t^2) (closingTraceLaw M) ∧
    ∀ z : ℂ, ∀ hz : z.im≠0, ∀ i j, closingMeasureEntryIntegral M (fun t : ℝ => (z+(t:ℂ))⁻¹) i j =
        ⟪(x i:H),(closingNonrealResolvent K hK z hz).map (x j:H)⟫_ℂ := by
  have hsum (y : ι→ℂ) : (↑(∑ i,y i • x i) : H)=∑ i,y i • (x i:H) := by simp
  have hN : ClosingNormalizedMatrixMeasure M := by
    change (fun i j => M i j univ)=(1 : Matrix ι ι ℂ)
    apply closing_finite_form_ext
    intro y
    rw [hquad y univ MeasurableSet.univ,closing_domain_slot_mass,hsum]
    have hid := closing_finite_form_gram (fun i => (x i:H)) (1 : H →L[ℂ] H) y
    simp only [ContinuousLinearMap.one_apply,inner_self_eq_norm_sq_to_K,orthonormal_iff_ite.mp horth] at hid
    simpa only [Complex.ofReal_pow,Matrix.one_apply,closingFiniteForm] using hid.symm
  refine ⟨hN,?_,?_⟩
  · apply integrable_finset_sum_measure.mpr
    intro j _
    have hd : closingDiagonalLaw M j=closingDomainSlotLaw K hK (x j) := by
      ext s hs
      have h := hquad (Pi.single j 1) s hs
      simp [closingFiniteForm,Pi.single_apply] at h
      rw [closing_diagonal_law_apply M hM j hs,h,Complex.ofReal_re,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [hd]
    exact closing_domain_slot_second_moment K hK _
  · intro z hz
    let f := fun t : ℝ => (z+(t:ℂ))⁻¹
    let R := (closingNonrealResolvent K hK z hz).map
    have hm : StronglyMeasurable f := (Measurable.inv ((measurable_const).add Complex.measurable_ofReal)).stronglyMeasurable
    have hb (t : ℝ) : ‖f t‖≤|z.im|⁻¹ := by
      rw [show f t=(z+(t:ℂ))⁻¹ from rfl,norm_inv]
      apply inv_anti₀ (abs_pos.mpr hz)
      simpa only [Complex.add_im,Complex.ofReal_im,add_zero] using Complex.abs_im_le_norm (z+(t:ℂ))
    have hi (i j : ι) : Integrable (fun t => f t*closingMatrixDensity M t i j) (closingControlMeasure M) := by
      have hd := closing_density_entry_integrable M i j
      apply (hd.norm.const_mul (|z.im|⁻¹)).mono' (hm.aestronglyMeasurable.mul hd.aestronglyMeasurable)
      exact Eventually.of_forall fun t => (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right (hb t) (norm_nonneg _))
    have H : closingMeasureEntryIntegral M f=(fun i j => ⟪(x i:H),R (x j:H)⟫_ℂ) := by
      apply closing_finite_form_ext
      intro y
      rw [closing_forward_form_test M hM _ y (hquad y) f hi,closing_domain_slot_cauchy K hK _ z hz,hsum,
        closing_finite_form_gram]
    exact fun i j => congrFun (congrFun H i) j

end UV.SectorPlane
