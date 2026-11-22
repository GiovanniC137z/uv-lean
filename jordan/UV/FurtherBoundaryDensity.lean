import UV.FurtherBoundaryFourier

/-! A weak L² comparison of overlap distributions is a genuine
Lebesgue density of the complex overlap measure. -/

noncomputable section
open MeasureTheory Set Real Complex
open scoped FourierTransform SchwartzMap ENNReal InnerProductSpace

namespace UV.ContinuationBoundary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def IsOverlapDensity (ν : ComplexMeasure E) (h : E → ℂ) : Prop :=
  Integrable h ∧ ∀ s, MeasurableSet s → ν s = ∫ x in s, h x

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem locally_integrable_rn_smul {μ dominating : Measure E} [SigmaFinite μ] [SigmaFinite dominating]
    (hac : μ ≪ dominating) {h : E → ℂ} (hlocal : LocallyIntegrable h μ) :
    LocallyIntegrable (fun x => (μ.rnDeriv dominating x).toReal • h x) dominating := by
  intro x
  obtain ⟨U, hU, hx, hsub⟩ := mem_nhds_iff.mp (Classical.choose_spec (hlocal x)).1
  have hf : IntegrableOn h U μ :=
    (Classical.choose_spec (hlocal x)).2.mono_set hU
  refine ⟨U, hx.mem_nhds hsub, ?_⟩
  rw [← integrable_indicator_iff hx.measurableSet]
  have hi := (integrable_rnDeriv_smul_iff hac).mpr (hf.integrable_indicator hx.measurableSet)
  apply hi.congr
  filter_upwards with y
  by_cases hy : y ∈ U <;> simp [hy]

omit [BorelSpace E] in
private theorem real_rn_integrable {μ dominating : Measure E} [IsFiniteMeasure μ] [SigmaFinite dominating]
    (hac : μ ≪ dominating) : Integrable (fun x => (μ.rnDeriv dominating x).toReal) dominating := by
  simpa using (integrable_toReal_rnDeriv_mul_iff (f := fun _ => (1 : ℝ)) hac).mpr
    (integrable_const _)

omit [BorelSpace E] in
private theorem real_rn_complex_integrable {μ dominating : Measure E} [IsFiniteMeasure μ] [SigmaFinite dominating]
    (hac : μ ≪ dominating) :
    Integrable (fun x => ((μ.rnDeriv dominating x).toReal : ℂ)) dominating := by
  exact (real_rn_integrable hac).ofReal

theorem overlap_density_of_distribution_eq (ν : ComplexMeasure E)
    (h : Lp (α := E) ℂ 2 volume)
    (hh : complexOverlapDistribution ν = (h : 𝓢'(E, ℂ))) :
    IsOverlapDensity ν h := by
  let p := ν.re.toJordanDecomposition.posPart
  let q := ν.re.toJordanDecomposition.negPart
  let r := ν.im.toJordanDecomposition.posPart
  let s := ν.im.toJordanDecomposition.negPart
  let dominating := ((((volume : Measure E) + p) + q) + r) + s
  letI : SigmaFinite (volume : Measure E) := inferInstance
  letI : SigmaFinite p := inferInstanceAs (SigmaFinite ν.re.toJordanDecomposition.posPart)
  letI : SigmaFinite q := inferInstanceAs (SigmaFinite ν.re.toJordanDecomposition.negPart)
  letI : SigmaFinite r := inferInstanceAs (SigmaFinite ν.im.toJordanDecomposition.posPart)
  letI : SigmaFinite s := inferInstanceAs (SigmaFinite ν.im.toJordanDecomposition.negPart)
  letI : SigmaFinite dominating := Add.sigmaFinite _ _
  have hav : volume ≪ dominating := Measure.absolutelyContinuous_of_le
    ((((Measure.le_add_right le_rfl).trans (Measure.le_add_right le_rfl)).trans
      (Measure.le_add_right le_rfl)).trans (Measure.le_add_right le_rfl))
  have hap : p ≪ dominating := Measure.absolutelyContinuous_of_le
    ((((Measure.le_add_left le_rfl).trans (Measure.le_add_right le_rfl)).trans
      (Measure.le_add_right le_rfl)).trans (Measure.le_add_right le_rfl))
  have haq : q ≪ dominating := Measure.absolutelyContinuous_of_le
    (((Measure.le_add_left le_rfl).trans (Measure.le_add_right le_rfl)).trans (Measure.le_add_right le_rfl))
  have har : r ≪ dominating := Measure.absolutelyContinuous_of_le
    ((Measure.le_add_left le_rfl).trans (Measure.le_add_right le_rfl))
  have has : s ≪ dominating := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  let H := fun x => ((p.rnDeriv dominating x).toReal : ℂ) - (q.rnDeriv dominating x).toReal +
    Complex.I * (((r.rnDeriv dominating x).toReal : ℂ) - (s.rnDeriv dominating x).toReal)
  let J := fun x => (((volume : Measure E).rnDeriv dominating x).toReal) • h x
  have hiH : Integrable H dominating :=
    ((real_rn_complex_integrable hap).sub (real_rn_complex_integrable haq)).add
      (((real_rn_complex_integrable har).sub (real_rn_complex_integrable has)).const_mul _)
  have hlocJ : LocallyIntegrable J dominating :=
    locally_integrable_rn_smul hav ((Lp.memLp h).locallyIntegrable (by norm_num))
  have hden : H =ᵐ[dominating] J := by
    apply ae_eq_of_integral_contDiff_smul_eq hiH.locallyIntegrable hlocJ
    intro φ hφ hφc
    let ψ : 𝓢(E, ℂ) := (hφc.comp_left Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hφ)
    have hpsi (x : E) : ψ x = (φ x : ℂ) := rfl
    have hp : (∫ x, φ x • ((p.rnDeriv dominating x).toReal : ℂ) ∂dominating) = ∫ x, ψ x ∂p := by
      simpa only [Complex.real_smul, hpsi, mul_comm] using
        integral_rnDeriv_smul (f := (ψ : E → ℂ)) hap
    have hq : (∫ x, φ x • ((q.rnDeriv dominating x).toReal : ℂ) ∂dominating) = ∫ x, ψ x ∂q := by
      simpa only [Complex.real_smul, hpsi, mul_comm] using
        integral_rnDeriv_smul (f := (ψ : E → ℂ)) haq
    have hr : (∫ x, φ x • ((r.rnDeriv dominating x).toReal : ℂ) ∂dominating) = ∫ x, ψ x ∂r := by
      simpa only [Complex.real_smul, hpsi, mul_comm] using
        integral_rnDeriv_smul (f := (ψ : E → ℂ)) har
    have hs : (∫ x, φ x • ((s.rnDeriv dominating x).toReal : ℂ) ∂dominating) = ∫ x, ψ x ∂s := by
      simpa only [Complex.real_smul, hpsi, mul_comm] using
        integral_rnDeriv_smul (f := (ψ : E → ℂ)) has
    have hi {μ : Measure E} [IsFiniteMeasure μ] (ha : μ ≪ dominating) :
        Integrable (fun x => φ x • ((μ.rnDeriv dominating x).toReal : ℂ)) dominating := by
      have hi := (integrable_rnDeriv_smul_iff (f := (ψ : E → ℂ)) ha).mpr (ψ.integrable (μ := μ))
      apply hi.congr
      filter_upwards with x
      rw [hpsi, Complex.real_smul, Complex.real_smul, mul_comm]
    have hhψ := congrArg (fun T : 𝓢'(E, ℂ) => T ψ) hh
    change (p.toTemperedDistribution - q.toTemperedDistribution +
      Complex.I • (r.toTemperedDistribution - s.toTemperedDistribution)) ψ = _ at hhψ
    simp only [add_apply, sub_apply, smul_apply, Measure.toTemperedDistribution_apply,
      Lp.toTemperedDistribution_apply, smul_eq_mul] at hhψ
    change (∫ x, φ x • H x ∂dominating) = ∫ x, φ x • J x ∂dominating
    have hJ : (∫ x, φ x • J x ∂dominating) = ∫ x, ψ x * h x := by
      simpa only [J, hpsi, Complex.real_smul, mul_left_comm] using
        integral_rnDeriv_smul (f := fun x => ψ x * h x) hav
    rw [hJ, ← hhψ]
    simp only [H, smul_add, smul_sub, Complex.real_smul]
    simp_rw [← mul_assoc, mul_comm ((↑(φ _) : ℂ)) Complex.I, mul_assoc, mul_sub]
    let P := fun x => φ x • ((p.rnDeriv dominating x).toReal : ℂ)
    let Q := fun x => φ x • ((q.rnDeriv dominating x).toReal : ℂ)
    let R := fun x => Complex.I * (φ x • ((r.rnDeriv dominating x).toReal : ℂ))
    let S := fun x => Complex.I * (φ x • ((s.rnDeriv dominating x).toReal : ℂ))
    change (∫ x, ((P - Q) + (R - S)) x ∂dominating) = _
    rw [integral_add' ((hi hap).sub (hi haq)) (((hi har).const_mul Complex.I).sub ((hi has).const_mul Complex.I)),
      integral_sub' (hi hap) (hi haq),
      integral_sub' ((hi har).const_mul Complex.I) ((hi has).const_mul Complex.I)]
    simp only [integral_const_mul]
    change (∫ x, φ x • ((p.rnDeriv dominating x).toReal : ℂ) ∂dominating) -
      (∫ x, φ x • ((q.rnDeriv dominating x).toReal : ℂ) ∂dominating) +
      (Complex.I * (∫ x, φ x • ((r.rnDeriv dominating x).toReal : ℂ) ∂dominating) -
       Complex.I * (∫ x, φ x • ((s.rnDeriv dominating x).toReal : ℂ) ∂dominating)) = _
    rw [hp, hq, hr, hs]
  refine ⟨(integrable_rnDeriv_smul_iff hav).mp (hiH.congr hden), ?_⟩
  intro A hA
  rw [← setIntegral_rnDeriv_smul hav hA]
  have hi : (∫ x in A, J x ∂dominating) = ∫ x in A, H x ∂dominating :=
    integral_congr_ae (ae_restrict_of_ae hden.symm)
  rw [hi]
  have he {μ : Measure E} [IsFiniteMeasure μ] (ha : μ ≪ dominating) :
      (∫ x in A, ((μ.rnDeriv dominating x).toReal : ℂ) ∂dominating) = (μ.real A : ℂ) := by
    rw [integral_complex_ofReal]
    congr 1
    simpa [measureReal_def, hA] using setIntegral_toReal_rnDeriv_mul' ha (fun _ => (1 : ℝ)) A
  change ν A = ∫ x in A, H x ∂dominating
  simp only [H]
  have h₁ := (real_rn_complex_integrable hap).restrict (s := A)
  have h₂ := (real_rn_complex_integrable haq).restrict (s := A)
  have h₃ := (real_rn_complex_integrable har).restrict (s := A)
  have h₄ := (real_rn_complex_integrable has).restrict (s := A)
  let P := fun x => ((p.rnDeriv dominating x).toReal : ℂ)
  let Q := fun x => ((q.rnDeriv dominating x).toReal : ℂ)
  let R := fun x => ((r.rnDeriv dominating x).toReal : ℂ)
  let S := fun x => ((s.rnDeriv dominating x).toReal : ℂ)
  change _ = ∫ x in A, ((P - Q) + (fun y => Complex.I * (R - S) y)) x ∂dominating
  rw [integral_add' (h₁.sub h₂) ((h₃.sub h₄).const_mul Complex.I),
    integral_sub' h₁ h₂, integral_const_mul, integral_sub' h₃ h₄, he hap, he haq, he har, he has]
  have hre : (ν A).re = p.real A - q.real A := by
    change ν.re A = _
    rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition ν.re]
    exact Measure.toSignedMeasure_sub_apply hA
  have him : (ν A).im = r.real A - s.real A := by
    change ν.im A = _
    rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition ν.im]
    exact Measure.toSignedMeasure_sub_apply hA
  apply Complex.ext <;> simp [hre, him, Complex.mul_re, Complex.mul_im]

/-- Finite weighted phase energy produces an actual Sobolev density and
identifies its exact Bessel norm. -/
theorem overlap_density_and_norm_of_finite_energy (ν : ComplexMeasure E) (N : ℕ)
    (hfin : overlapEnergy N ν ≠ ∞) :
    ∃ h g : Lp (α := E) ℂ 2 volume,
      IsOverlapDensity ν h ∧
      overlapBesselPotential N (h : 𝓢'(E, ℂ)) = (g : 𝓢'(E, ℂ)) ∧
      overlapEnergy N ν = ENNReal.ofReal (‖g‖ ^ 2) := by
  obtain ⟨h, g, hh, hg⟩ := (overlap_finite_iff_bessel_potential ν N).mp hfin
  refine ⟨h, g, overlap_density_of_distribution_eq ν h hh, hg, ?_⟩
  exact overlap_bessel_norm_exact ν N g (hh.symm ▸ hg)

end UV.ContinuationBoundary
