import UV.ContinueCrossUniquenessCompact
import UV.VerifySpectrumCrossMeasure
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-! Uniqueness of the ordinary signed cross spectrum under the same
reference-weighted total-variation hypothesis as its existence criterion. -/

noncomputable section

namespace UV.RevisionSpectrum

open Filter MeasureTheory Set
open scoped ENNReal

private abbrev CrossSpectralInterval := Set.Icc (0 : ℝ) 1

private def crossCompactCoordinate (y s : ℝ) : CrossSpectralInterval :=
  ⟨max 0 (min 1 (y / (y + s))), ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩

private theorem cross_compact_coordinate_measurable (y : ℝ) :
    Measurable (crossCompactCoordinate y) := by
  apply Measurable.subtype_mk
  exact measurable_const.max (measurable_const.min
    (measurable_const.div (measurable_const.add measurable_id)))

private theorem cross_compact_coordinate_eq {y s : ℝ} (hy : 0 < y) (hs : 0 ≤ s) :
    (crossCompactCoordinate y s : ℝ) = y / (y + s) := by
  change max 0 (min 1 (y / (y + s))) = y / (y + s)
  rw [min_eq_right ((div_le_one (by positivity)).2 (by linarith)),
    max_eq_right (by positivity)]

private def crossReferenceWeight (y s : ℝ) : ℝ≥0∞ := ENNReal.ofReal (stieltjesWeight y s)

private theorem cross_reference_weight_measurable (y : ℝ) : Measurable (crossReferenceWeight y) :=
  ((measurable_const.add measurable_id).inv : Measurable (stieltjesWeight y)).ennreal_ofReal

private theorem cross_weighted_compact_resolvent (μ : Measure ℝ) {y h : ℝ}
    (hy : 0 < y) (hh : 0 < h) (hs : ∀ᵐ s ∂μ, 0 ≤ s) :
    (∫ t : CrossSpectralInterval, (1 + h * (t : ℝ))⁻¹
      ∂((μ.withDensity (crossReferenceWeight y)).map (crossCompactCoordinate y))) =
      diagonalStieltjes μ (y + y * h) := by
  have hm : Measurable (fun t : CrossSpectralInterval => (1 + h * (t : ℝ))⁻¹) :=
    (measurable_const.add (measurable_const.mul measurable_subtype_coe)).inv
  rw [integral_map (cross_compact_coordinate_measurable y).aemeasurable hm.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (cross_reference_weight_measurable y)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hs] with s hs'
  simp only [crossReferenceWeight, ENNReal.toReal_ofReal (stieltjesWeight_pos hy hs').le,
    smul_eq_mul, cross_compact_coordinate_eq hy hs']
  have hy' : 0 < y + s := by positivity
  have hden : 0 < 1 + h * (y / (y + s)) := by positivity
  have hz : 0 < y + y * h + s := by positivity
  unfold stieltjesWeight
  field_simp [hy'.ne', hden.ne', hz.ne']
  ring

private theorem cross_compact_coordinate_recover (μ : Measure ℝ) {y : ℝ}
    (hy : 0 < y) (hs : ∀ᵐ s ∂μ, 0 ≤ s) :
    (μ.map (crossCompactCoordinate y)).map (fun t : CrossSpectralInterval => y / (t : ℝ) - y) = μ := by
  have hm : Measurable (fun t : CrossSpectralInterval => y / (t : ℝ) - y) :=
    (measurable_const.div measurable_subtype_coe).sub measurable_const
  rw [Measure.map_map hm (cross_compact_coordinate_measurable y)]
  conv_rhs => rw [← Measure.map_id (μ := μ)]
  apply Measure.map_congr
  filter_upwards [hs] with s hs'
  simp only [Function.comp_apply, id_eq, cross_compact_coordinate_eq hy hs']
  rw [div_div_eq_mul_div, mul_comm y, mul_div_cancel_right₀ _ hy.ne', add_sub_cancel_left]

private theorem cross_reference_weight_recover (μ : Measure ℝ) {y : ℝ}
    (hy : 0 < y) (hs : ∀ᵐ s ∂μ, 0 ≤ s) :
    (μ.withDensity (crossReferenceWeight y)).withDensity (fun s => (crossReferenceWeight y s)⁻¹) = μ :=
  withDensity_inv_same₀ (cross_reference_weight_measurable y).aemeasurable
    (hs.mono fun _ hs' => (ENNReal.ofReal_pos.mpr (stieltjesWeight_pos hy hs')).ne')
    (Eventually.of_forall fun _ => ENNReal.ofReal_ne_top)

/-- A positive spectral measure with one finite reference weight is
determined by its Stieltjes values on the positive Euclidean axis. -/
theorem diagonal_stieltjes_measure_ext {μ ν : Measure ℝ} {y : ℝ} (hy : 0 < y)
    (hμ : ∀ᵐ s ∂μ, 0 ≤ s) (hν : ∀ᵐ s ∂ν, 0 ≤ s)
    (hiμ : Integrable (stieltjesWeight y) μ) (hiν : Integrable (stieltjesWeight y) ν)
    (he : ∀ x : ℝ, 0 < x → diagonalStieltjes μ x = diagonalStieltjes ν x) : μ = ν := by
  letI : IsFiniteMeasure (μ.withDensity (crossReferenceWeight y)) :=
    isFiniteMeasure_withDensity_ofReal hiμ.2
  letI : IsFiniteMeasure (ν.withDensity (crossReferenceWeight y)) :=
    isFiniteMeasure_withDensity_ofReal hiν.2
  have hcompact : (μ.withDensity (crossReferenceWeight y)).map (crossCompactCoordinate y) =
      (ν.withDensity (crossReferenceWeight y)).map (crossCompactCoordinate y) := by
    apply compact_spectral_measure_eq_of_resolvent
    intro h hh
    rw [cross_weighted_compact_resolvent μ hy hh hμ, cross_weighted_compact_resolvent ν hy hh hν]
    exact he _ (by positivity)
  have hd := congrArg (Measure.map (fun t : CrossSpectralInterval => y / (t : ℝ) - y)) hcompact
  rw [cross_compact_coordinate_recover _ hy ((withDensity_absolutelyContinuous _ _).ae_le hμ),
    cross_compact_coordinate_recover _ hy ((withDensity_absolutelyContinuous _ _).ae_le hν)] at hd
  have h := congrArg (fun ν => ν.withDensity (fun s => (crossReferenceWeight y s)⁻¹)) hd
  simpa only [cross_reference_weight_recover μ hy hμ, cross_reference_weight_recover ν hy hν] using h

/-- Equality of ordinary signed Stieltjes transforms implies equality of
the two Jordan parts, even when their unweighted masses are infinite. -/
theorem signed_stieltjes_jordan_ext {μpos μneg νpos νneg : Measure ℝ} {y : ℝ}
    (hy : 0 < y) (hμJ : μpos ⟂ₘ μneg) (hνJ : νpos ⟂ₘ νneg)
    (hμp : ∀ᵐ s ∂μpos, 0 ≤ s) (hμn : ∀ᵐ s ∂μneg, 0 ≤ s)
    (hνp : ∀ᵐ s ∂νpos, 0 ≤ s) (hνn : ∀ᵐ s ∂νneg, 0 ≤ s)
    (hiμp : Integrable (stieltjesWeight y) μpos) (hiμn : Integrable (stieltjesWeight y) μneg)
    (hiνp : Integrable (stieltjesWeight y) νpos) (hiνn : Integrable (stieltjesWeight y) νneg)
    (he : ∀ x : ℝ, 0 < x → diagonalStieltjes μpos x - diagonalStieltjes μneg x =
      diagonalStieltjes νpos x - diagonalStieltjes νneg x) :
    μpos = νpos ∧ μneg = νneg := by
  have hsum : μpos + νneg = νpos + μneg := by
    apply diagonal_stieltjes_measure_ext hy (ae_add_measure_iff.2 ⟨hμp, hνn⟩)
      (ae_add_measure_iff.2 ⟨hνp, hμn⟩) (hiμp.add_measure hiνn) (hiνp.add_measure hiμn)
    intro x hx
    unfold diagonalStieltjes at he ⊢
    rw [integral_add_measure (diagonal_stieltjes_weighted_integrable hμp hx hy hiμp)
      (diagonal_stieltjes_weighted_integrable hνn hx hy hiνn),
      integral_add_measure (diagonal_stieltjes_weighted_integrable hνp hx hy hiνp)
        (diagonal_stieltjes_weighted_integrable hμn hx hy hiμn)]
    linarith [he x hx]
  let w := crossReferenceWeight y
  letI : IsFiniteMeasure (μpos.withDensity w) := isFiniteMeasure_withDensity_ofReal hiμp.2
  letI : IsFiniteMeasure (μneg.withDensity w) := isFiniteMeasure_withDensity_ofReal hiμn.2
  letI : IsFiniteMeasure (νpos.withDensity w) := isFiniteMeasure_withDensity_ofReal hiνp.2
  letI : IsFiniteMeasure (νneg.withDensity w) := isFiniteMeasure_withDensity_ofReal hiνn.2
  let J : JordanDecomposition ℝ := ⟨μpos.withDensity w, μneg.withDensity w,
    hμJ.mono_ac (withDensity_absolutelyContinuous _ _) (withDensity_absolutelyContinuous _ _)⟩
  let K : JordanDecomposition ℝ := ⟨νpos.withDensity w, νneg.withDensity w,
    hνJ.mono_ac (withDensity_absolutelyContinuous _ _) (withDensity_absolutelyContinuous _ _)⟩
  have hWeighted := congrArg (fun μ : Measure ℝ => μ.withDensity w) hsum
  simp only [withDensity_add_measure] at hWeighted
  have hJK : J = K := JordanDecomposition.toSignedMeasure_injective (by
    change (μpos.withDensity w).toSignedMeasure - (μneg.withDensity w).toSignedMeasure =
      (νpos.withDensity w).toSignedMeasure - (νneg.withDensity w).toSignedMeasure
    apply VectorMeasure.ext
    intro s hs
    rw [Measure.toSignedMeasure_sub_apply hs, Measure.toSignedMeasure_sub_apply hs]
    have h := congrArg (fun ν : Measure ℝ => ν.real s) hWeighted
    dsimp only at h
    rw [measureReal_add_apply, measureReal_add_apply] at h
    linarith)
  constructor
  · have hp := congrArg JordanDecomposition.posPart hJK
    change μpos.withDensity w = νpos.withDensity w at hp
    have h := congrArg (fun ν : Measure ℝ => ν.withDensity (fun s => (crossReferenceWeight y s)⁻¹)) hp
    simpa only [w, cross_reference_weight_recover μpos hy hμp,
      cross_reference_weight_recover νpos hy hνp] using h
  · have hn := congrArg JordanDecomposition.negPart hJK
    change μneg.withDensity w = νneg.withDensity w at hn
    have h := congrArg (fun ν : Measure ℝ => ν.withDensity (fun s => (crossReferenceWeight y s)⁻¹)) hn
    simpa only [w, cross_reference_weight_recover μneg hy hμn,
      cross_reference_weight_recover νneg hy hνn] using h

/-- Every ordinary weighted signed representation of the cross family
has the exact continuum and atom constructed in the classification. -/
theorem verify_cross_signed_spectral_unique {νpos νneg : Measure ℝ} {a M m₂ y : ℝ}
    (ha : 0 < a) (hm₂ : 0 ≤ m₂) (hy : 0 < y) (hJ : νpos ⟂ₘ νneg)
    (hpos : ∀ᵐ s ∂νpos, 0 ≤ s) (hneg : ∀ᵐ s ∂νneg, 0 ≤ s)
    (hipos : Integrable (stieltjesWeight y) νpos) (hineg : Integrable (stieltjesWeight y) νneg)
    (he : ∀ x : ℝ, 0 < x → diagonalStieltjes νpos x - diagonalStieltjes νneg x =
      verifyCrossCovariance a M m₂ x) :
    νpos = verifyCrossPositive a M m₂ ∧ νneg = verifyCrossNegative a M m₂ := by
  have hadm := (verify_cross_signed_necessity_and_atom a M hm₂ hy hpos hneg hipos hineg he).1
  obtain ⟨hp, hn⟩ := verify_cross_jordan_support (a := a) (M := M) hm₂
  obtain ⟨hip, hin, _⟩ := verify_cross_jordan_representation ha hm₂ hy hadm
  apply signed_stieltjes_jordan_ext hy hJ (verify_cross_jordan_mutuallySingular a M m₂)
    hpos hneg hp hn hipos hineg hip hin
  exact fun x hx => (he x hx).trans (verify_cross_jordan_representation ha hm₂ hx hadm).2.2.symm

end UV.RevisionSpectrum
