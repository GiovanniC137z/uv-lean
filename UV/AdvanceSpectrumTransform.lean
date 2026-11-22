import UV.AdvanceSpectrumPurePole

/-! The bounded Jordan integrals and the common-density Stieltjes
transform give the same ordinary cross spectral integral. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace UV.RevisionSpectrum

private theorem signed_weighted_integral_as_density {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SigmaFinite μ] (ν : SignedMeasure α)
    (hν : ν ≪ᵥ μ.toENNRealVectorMeasure) (f : α → ℝ) (hf : Measurable f)
    (hI : Integrable (fun s => f s*ν.rnDeriv μ s) μ) :
    (∫ s, f s ∂ν.toJordanDecomposition.posPart) -
      (∫ s, f s ∂ν.toJordanDecomposition.negPart) = ∫ s, f s*ν.rnDeriv μ s ∂μ := by
  let g := ν.rnDeriv μ
  have hmeas : Measurable g := SignedMeasure.measurable_rnDeriv _ _
  have hJ := SignedMeasure.toJordanDecomposition_eq_of_eq_add_withDensity
    (s := ν) (t := 0) hmeas (SignedMeasure.integrable_rnDeriv _ _)
    VectorMeasure.MutuallySingular.zero_left
    (by simpa only [zero_add] using (SignedMeasure.withDensityᵥ_rnDeriv_eq ν μ hν).symm)
  rw [hJ]
  simp only [SignedMeasure.toJordanDecomposition_zero, JordanDecomposition.zero_posPart,
    JordanDecomposition.zero_negPart, zero_add]
  rw [integral_withDensity_eq_integral_toReal_smul (hmeas.ennreal_ofReal)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul (hmeas.neg.ennreal_ofReal)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  have hi (sgn : ℝ) (hs : |sgn| ≤ 1) :
      Integrable (fun s => max (sgn*g s) 0 * f s) μ := by
    refine hI.mono (((hmeas.const_mul sgn).max measurable_const).mul hf).aestronglyMeasurable ?_
    filter_upwards with s
    simp only [norm_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (le_max_right (sgn*g s) (0:ℝ)), mul_comm |f s|]
    change max (sgn*g s) 0 * |f s| ≤ |g s| * |f s|
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    apply max_le
    · exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hs)
    · exact abs_nonneg _
  rw [← integral_sub]
  · apply integral_congr_ae (ae_of_all _ fun s => ?_)
    change max (g s) 0 * f s - max (-(g s)) 0 * f s = f s*g s
    by_cases h : 0 ≤ g s
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
      ring
    · have h' := le_of_not_ge h
      rw [max_eq_right h', max_eq_left (neg_nonneg.mpr h')]
      ring
  · simpa only [one_mul] using hi 1 (by norm_num)
  · simpa only [neg_one_mul] using hi (-1) (by norm_num)

private theorem finite_complex_integral_as_density {μ : Measure ℝ} [SigmaFinite μ]
    (ν : ComplexMeasure ℝ) (hν : ν ≪ᵥ μ.toENNRealVectorMeasure)
    (f : ℝ → ℝ) (hf : Measurable f)
    (hI : Integrable (fun s => (f s : ℂ)*ν.rnDeriv μ s) μ) :
    finiteCrossIntegral ν f = ∫ s, (f s : ℂ)*ν.rnDeriv μ s ∂μ := by
  have hac := (ComplexMeasure.absolutelyContinuous_ennreal_iff ν μ.toENNRealVectorMeasure).1 hν
  have hRe : Integrable (fun s => f s*ν.re.rnDeriv μ s) μ := by
    simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, ComplexMeasure.rnDeriv] using Complex.reCLM.integrable_comp hI
  have hIm : Integrable (fun s => f s*ν.im.rnDeriv μ s) μ := by
    simpa only [Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, ComplexMeasure.rnDeriv] using Complex.imCLM.integrable_comp hI
  apply Complex.ext
  · have he := Complex.reCLM.integral_comp_comm hI
    simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, ComplexMeasure.rnDeriv] at he
    change (∫ s, f s*ν.re.rnDeriv μ s ∂μ) = (∫ s, (f s : ℂ)*ν.rnDeriv μ s ∂μ).re at he
    rw [← he]
    simp only [finiteCrossIntegral, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    exact signed_weighted_integral_as_density ν.re hac.1 f hf hRe
  · have he := Complex.imCLM.integral_comp_comm hI
    simp only [Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, ComplexMeasure.rnDeriv] at he
    change (∫ s, f s*ν.im.rnDeriv μ s ∂μ) = (∫ s, (f s : ℂ)*ν.rnDeriv μ s ∂μ).im at he
    rw [← he]
    simp only [finiteCrossIntegral, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      Complex.I_re, Complex.ofReal_re, zero_mul, mul_one, add_zero, zero_add]
    exact signed_weighted_integral_as_density ν.im hac.2 f hf hIm

variable {E : Type*} [Norm E] {diamond : UV.SectorPlane.Plane E}

theorem SetwiseSpectralCompletion.crossSample_as_integral
    (C : SetwiseSpectralCompletion diamond) {x y : ℝ} (hx : 0<x) (hy : 0<y)
    (hi₁ : Integrable (stieltjesWeight y) C.first)
    (hi₂ : Integrable (stieltjesWeight y) C.second) (n : ℕ) :
    C.crossSample x n =
      ∫ s in spectralWindow n, (stieltjesWeight x s : ℂ)*C.crossDensity s ∂C.trace := by
  letI := C.localTrace_finite n
  have h := finite_setwise_cross_absolutelyContinuous (C.cross n) (C.setwise_positive n)
  have hμ : C.localTrace n = C.first.restrict (spectralWindow n) +
      C.second.restrict (spectralWindow n) := Measure.restrict_add _ _ _
  change C.cross n ≪ᵥ (C.first.restrict (spectralWindow n) +
    C.second.restrict (spectralWindow n)).toENNRealVectorMeasure at h
  rw [← hμ] at h
  have hI : Integrable (fun s => (stieltjesWeight x s : ℂ)*C.crossDensity s) (C.localTrace n) :=
    (C.crossStieltjes_integrable hx hy hi₁ hi₂).integrableOn
  have heq : (fun s => (stieltjesWeight x s : ℂ)*C.crossDensity s) =ᵐ[C.localTrace n]
      fun s => (stieltjesWeight x s : ℂ)*(C.cross n).rnDeriv (C.localTrace n) s :=
    (C.crossDensity_eq_local n).mono fun s hs => by dsimp only; rw [hs]; rfl
  show finiteCrossIntegral (C.cross n) (stieltjesWeight x) = _
  rw [finite_complex_integral_as_density _ h _ (by unfold stieltjesWeight; fun_prop) (hI.congr heq)]
  exact integral_congr_ae heq.symm

theorem SetwiseSpectralCompletion.crossSample_tendsto
    (C : SetwiseSpectralCompletion diamond) {x y : ℝ} (hx : 0<x) (hy : 0<y)
    (hi₁ : Integrable (stieltjesWeight y) C.first)
    (hi₂ : Integrable (stieltjesWeight y) C.second) :
    Tendsto (C.crossSample x) atTop (𝓝 (C.crossStieltjes x)) := by
  change Tendsto (fun n => C.crossSample x n) atTop (𝓝 (C.crossStieltjes x))
  simp_rw [C.crossSample_as_integral hx hy hi₁ hi₂]
  have hI := C.crossStieltjes_integrable hx hy hi₁ hi₂
  have ht := tendsto_setIntegral_of_monotone (μ := C.trace)
    (s := spectralWindow) (fun _ => measurableSet_Icc) spectralWindow_mono hI.integrableOn
  have heq : (⋃ n, spectralWindow n) = Ici 0 := by
    ext s
    simp only [mem_iUnion, spectralWindow, mem_Icc, mem_Ici]
    exact ⟨fun ⟨_,hs,_⟩ => hs,fun h => ⟨⌈s⌉₊,h,Nat.le_ceil s⟩⟩
  have hrestrict : C.trace.restrict (Ici 0) = C.trace :=
    Measure.restrict_eq_self_of_ae_mem C.trace_nonnegative
  rw [heq, hrestrict] at ht
  exact ht

theorem setwise_completed_bubble_from_transform {C : SetwiseSpectralCompletion diamond}
    (a M m : ℝ) {y : ℝ} (hy : 0<y)
    (hi₁ : Integrable (stieltjesWeight y) C.first)
    (hi₂ : Integrable (stieltjesWeight y) C.second)
    (hcross : C.crossStieltjes y =
      ((Real.exp (-a*(Real.sqrt (y+M^2)-M))/(y+m^2) : ℝ) : ℂ))
    (p : UV.ScalarMomentum) :
    ¬ Integrable (fun q : UV.ScalarMomentum =>
      diagonalStieltjes C.first (‖q‖^2)*diagonalStieltjes C.second (‖q+p‖^2)) := by
  have ht := C.crossSample_tendsto hy hy hi₁ hi₂
  rw [hcross] at ht
  exact setwise_completed_bubble_nonintegrable C a M m hy hi₁ hi₂ ht p


theorem SetwiseSpectralCompletion.crossVariation_support (C : SetwiseSpectralCompletion diamond) :
    ∀ᵐ s ∂C.crossVariation, 0 ≤ s :=
  (withDensity_absolutelyContinuous C.trace _).ae_le C.trace_nonnegative

end UV.RevisionSpectrum
