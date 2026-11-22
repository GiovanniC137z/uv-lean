import UV.FurtherBoundaryDensity
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-! The converse Sobolev test, with the ordinary density determined by its
values on measurable sets. -/

noncomputable section

open MeasureTheory Complex Set
open scoped FourierTransform SchwartzMap ENNReal

namespace UV.ContinuationBoundary

variable {E : Type*} [MeasureSpace E]

private theorem signed_density_test (s : SignedMeasure E) {f : E → ℝ}
    (hfm : Measurable f) (hf : Integrable f)
    (hs : ∀ A, MeasurableSet A → s A = ∫ x in A, f x)
    {ψ : E → ℂ} (hψ : Measurable ψ) {C : ℝ} (hC : ∀ x, ‖ψ x‖ ≤ C) :
    (∫ x, ψ x ∂s.toJordanDecomposition.posPart) -
      (∫ x, ψ x ∂s.toJordanDecomposition.negPart) = ∫ x, ψ x * (f x : ℂ) := by
  have hfnm : Measurable (fun x => -f x) := hfm.neg
  let p := (volume : Measure E).withDensity (fun x => ENNReal.ofReal (f x))
  let q := (volume : Measure E).withDensity (fun x => ENNReal.ofReal (-f x))
  letI : IsFiniteMeasure p := isFiniteMeasure_withDensity_ofReal hf.2
  letI : IsFiniteMeasure q := isFiniteMeasure_withDensity_ofReal hf.neg.2
  have hsing : p ⟂ₘ q := by
    let A := {x | f x ≤ 0}
    have hA : MeasurableSet A := measurableSet_le hfm measurable_const
    refine ⟨A, hA, ?_, ?_⟩
    · simp only [p, withDensity_apply_eq_zero hfm.ennreal_ofReal]
      have he : {x | ENNReal.ofReal (f x) ≠ 0} ∩ A = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hx, hxA⟩
        exact hx (ENNReal.ofReal_eq_zero.mpr hxA)
      rw [he, measure_empty]
    · simp only [q, withDensity_apply_eq_zero hfnm.ennreal_ofReal]
      have he : {x | ENNReal.ofReal (-f x) ≠ 0} ∩ Aᶜ = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hx, hxA⟩
        exact hx (ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr (le_of_not_ge hxA)))
      rw [he, measure_empty]
  let j : JordanDecomposition E := ⟨p, q, hsing⟩
  have hsd : s = (volume : Measure E).withDensityᵥ f := by
    ext A hA
    rw [withDensityᵥ_apply hf hA, hs A hA]
  have hj : s.toJordanDecomposition = j := by
    apply SignedMeasure.toJordanDecomposition_eq
    rw [hsd, withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hf]
    rfl
  rw [hj]
  change (∫ x, ψ x ∂p) - (∫ x, ψ x ∂q) = _
  simp only [p, q, integral_withDensity_eq_integral_toReal_smul hfm.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) ψ,
    integral_withDensity_eq_integral_toReal_smul hfnm.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) ψ]
  simp only [ENNReal.toReal_ofReal', Complex.real_smul]
  have hfpos : Integrable (fun x => max (f x) 0) := by
    change Integrable (f ⊔ 0)
    exact hf.sup (integrable_zero E ℝ volume)
  have hfneg : Integrable (fun x => max (-f x) 0) := by
    change Integrable (-f ⊔ 0)
    exact hf.neg.sup (integrable_zero E ℝ volume)
  have hmul {g : E → ℝ} (hg : Integrable g) : Integrable (fun x => (g x : ℂ) * ψ x) :=
    hg.ofReal.mul_bdd hψ.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  rw [← integral_sub (hmul hfpos) (hmul hfneg)]
  apply integral_congr_ae
  filter_upwards with x
  rw [← sub_mul, ← Complex.ofReal_sub, max_zero_sub_eq_self, mul_comm]

theorem overlap_distribution_of_density {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (ν : ComplexMeasure F) (h : Lp (α := F) ℂ 2 volume)
    (hd : IsOverlapDensity ν h) :
    complexOverlapDistribution ν = (h : 𝓢'(F, ℂ)) := by
  ext ψ
  have hm : Measurable (h : F → ℂ) := (Lp.stronglyMeasurable h).measurable
  have hRe : ∀ A, MeasurableSet A → ν.re A = ∫ x in A, (h x).re := by
    intro A hA
    change (ν A).re = _
    rw [hd.2 A hA]
    simpa only [RCLike.re_eq_complex_re] using (integral_re (μ := volume.restrict A) hd.1.integrableOn).symm
  have hIm : ∀ A, MeasurableSet A → ν.im A = ∫ x in A, (h x).im := by
    intro A hA
    change (ν A).im = _
    rw [hd.2 A hA]
    simpa only [RCLike.im_eq_complex_im] using (integral_im (μ := volume.restrict A) hd.1.integrableOn).symm
  let C := SchwartzMap.seminorm ℝ 0 0 ψ
  have hC (x : F) : ‖ψ x‖ ≤ C := by
    simpa [C] using ψ.le_seminorm ℝ 0 0 x
  have hψ := ψ.continuous.measurable
  change (∫ x, ψ x ∂ν.re.toJordanDecomposition.posPart) -
    (∫ x, ψ x ∂ν.re.toJordanDecomposition.negPart) + Complex.I *
      ((∫ x, ψ x ∂ν.im.toJordanDecomposition.posPart) -
      (∫ x, ψ x ∂ν.im.toJordanDecomposition.negPart)) = _
  rw [signed_density_test ν.re (Complex.continuous_re.measurable.comp hm) hd.1.re hRe hψ hC,
    signed_density_test ν.im (Complex.continuous_im.measurable.comp hm) hd.1.im hIm hψ hC, Lp.toTemperedDistribution_apply]
  have hmul {g : F → ℝ} (hg : Integrable g) :
      Integrable (fun x => ψ x * (g x : ℂ)) :=
    hg.ofReal.bdd_mul hψ.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  simp only [Function.comp_apply]
  have hre : Integrable (fun x => (h x).re) := hd.1.re
  have him : Integrable (fun x => (h x).im) := hd.1.im
  rw [← integral_const_mul, ← integral_add (hmul hre)
    ((hmul him).const_mul Complex.I)]
  apply integral_congr_ae
  filter_upwards with x
  rw [smul_eq_mul, mul_comm Complex.I, mul_assoc, ← mul_add, Complex.re_add_im]

/-- Exact Sobolev criterion on a genuine density, including the converse. -/
theorem overlap_finite_iff_density {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (ν : ComplexMeasure F) (N : ℕ) :
    overlapEnergy N ν ≠ ∞ ↔
      ∃ h g : Lp (α := F) ℂ 2 volume, IsOverlapDensity ν h ∧
        overlapBesselPotential N (h : 𝓢'(F, ℂ)) = (g : 𝓢'(F, ℂ)) := by
  constructor
  · intro hfin
    obtain ⟨h, g, hh, hg, _⟩ := overlap_density_and_norm_of_finite_energy ν N hfin
    exact ⟨h, g, hh, hg⟩
  · rintro ⟨h, g, hh, hg⟩
    exact (overlap_finite_iff_bessel_potential ν N).mpr
      ⟨h, g, overlap_distribution_of_density ν h hh, hg⟩

theorem overlap_energy_eq_density_bessel_norm {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (ν : ComplexMeasure F) (N : ℕ) (h g : Lp (α := F) ℂ 2 volume)
    (hd : IsOverlapDensity ν h)
    (hg : overlapBesselPotential N (h : 𝓢'(F, ℂ)) = (g : 𝓢'(F, ℂ))) :
    overlapEnergy N ν = ENNReal.ofReal (‖g‖ ^ 2) :=
  overlap_bessel_norm_exact ν N g (by rw [overlap_distribution_of_density ν h hd]; exact hg)

end UV.ContinuationBoundary
