import UV.AdvanceSpectrumLocallyFinite

/-! The norm of the derived complex density gives the actual variation
measure on the bounded spectral restrictions. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace UV.RevisionSpectrum

variable {α : Type*} [MeasurableSpace α]

private theorem linear_complex_le (u v : ℝ) (z : ℂ) :
    u*z.re+v*z.im ≤ Real.sqrt (u^2+v^2)*‖z‖ := by
  have hp : 0 ≤ Real.sqrt (u^2+v^2)*‖z‖ := by positivity
  by_cases hz : 0 ≤ u*z.re+v*z.im
  · apply (sq_le_sq₀ hz hp).mp
    rw [mul_pow, Real.sq_sqrt (by positivity), Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg (u*z.im-v*z.re)]
  · exact (le_of_not_ge hz).trans hp

private theorem norm_density_le_of_setIntegral {μ : Measure α} {c : α → ℂ} {d : α → ℝ}
    (hc : Integrable c μ) (hd : Integrable d μ)
    (hdom : ∀ B, MeasurableSet B → ‖∫ s in B, c s ∂μ‖ ≤ ∫ s in B, d s ∂μ) :
    (fun s => ‖c s‖) ≤ᵐ[μ] d := by
  have hre : Integrable (fun s => (c s).re) μ := Complex.reCLM.integrable_comp hc
  have him : Integrable (fun s => (c s).im) μ := Complex.imCLM.integrable_comp hc
  have hl (u v : ℝ) : ∀ᵐ s ∂μ,
      u*(c s).re+v*(c s).im ≤ Real.sqrt (u^2+v^2)*d s := by
    apply ae_le_of_forall_setIntegral_le ((hre.const_mul _).add (him.const_mul _))
      (hd.const_mul _)
    intro B hB _
    simp only [Pi.add_apply, integral_add (hre.const_mul _).integrableOn
      (him.const_mul _).integrableOn, integral_const_mul]
    have hRe := Complex.reCLM.integral_comp_comm (μ := μ.restrict B) hc.integrableOn
    have hIm := Complex.imCLM.integral_comp_comm (μ := μ.restrict B) hc.integrableOn
    change (∫ s in B, (c s).re ∂μ) = (∫ s in B, c s ∂μ).re at hRe
    change (∫ s in B, (c s).im ∂μ) = (∫ s in B, c s ∂μ).im at hIm
    rw [hRe,hIm]
    exact (linear_complex_le u v _).trans
      (mul_le_mul_of_nonneg_left (hdom B hB) (Real.sqrt_nonneg _))
  have hrat : ∀ᵐ s ∂μ, ∀ u v : ℚ, (u:ℝ)*(c s).re+(v:ℝ)*(c s).im ≤
      Real.sqrt ((u:ℝ)^2+(v:ℝ)^2)*d s :=
    ae_all_iff.2 fun u => ae_all_iff.2 fun v => hl u v
  have hd₀ := ae_nonneg_of_forall_setIntegral_nonneg hd
    (fun B hB _ => (norm_nonneg _).trans (hdom B hB))
  filter_upwards [hrat,hd₀] with s hs hs₀
  have hall := DenseRange.induction_on₂ (Rat.denseRange_cast (𝕜 := ℝ))
    (p := fun u v => u*(c s).re+v*(c s).im ≤ Real.sqrt (u^2+v^2)*d s)
    (isClosed_le (by fun_prop) (by fun_prop)) hs (c s).re (c s).im
  by_cases hz : ‖c s‖ = 0
  · simpa only [hz] using hs₀
  have hsq : (c s).re ^ 2 + (c s).im ^ 2 = ‖c s‖^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have he : Real.sqrt ((c s).re ^ 2 + (c s).im ^ 2) = ‖c s‖ := by
    rw [hsq, Real.sqrt_sq (norm_nonneg _)]
  rw [he, ← pow_two, ← pow_two, hsq, pow_two] at hall
  exact (mul_le_mul_iff_right₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))).1 hall

private theorem norm_density_measure_real {μ : Measure α} {c : α → ℂ}
    (hc : Integrable c μ) {B : Set α} (hB : MeasurableSet B) :
    (μ.withDensity (fun s => ‖c s‖ₑ)).real B = ∫ s in B, ‖c s‖ ∂μ := by
  rw [measureReal_def, withDensity_apply _ hB]
  exact (integral_norm_eq_lintegral_enorm hc.integrableOn.aestronglyMeasurable).symm

private theorem norm_density_measure_finite {μ : Measure α} {c : α → ℂ}
    (hc : Integrable c μ) :
    IsFiniteMeasure (μ.withDensity (fun s => ‖c s‖ₑ)) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact hc.2

/-- The norm-density measure is least among the finite measures dominating
the norm of the complex measure on every Borel set. -/
theorem finite_norm_density_least {μ σ : Measure α} [IsFiniteMeasure μ]
    [IsFiniteMeasure σ] {c : α → ℂ} (hc : Integrable c μ)
    (hdom : ∀ B, MeasurableSet B → ‖∫ s in B, c s ∂μ‖ ≤ σ.real B) :
    μ.withDensity (fun s => ‖c s‖ₑ) ≤ σ := by
  let τ := μ+σ
  let a := fun s => (μ.rnDeriv τ s).toReal
  let d := fun s => (σ.rnDeriv τ s).toReal
  have hac : μ ≪ τ := (Measure.le_add_right le_rfl).absolutelyContinuous
  have hσ : σ ≪ τ := (Measure.le_add_left le_rfl).absolutelyContinuous
  have hd : Integrable d τ := Measure.integrable_toReal_rnDeriv
  have hφ : Integrable (fun s => a s • c s) τ := (integrable_rnDeriv_smul_iff hac).2 hc
  have hlocal (B : Set α) (hB : MeasurableSet B) :
      ‖∫ s in B, a s • c s ∂τ‖ ≤ ∫ s in B, d s ∂τ := by
    rw [Measure.setIntegral_toReal_rnDeriv hσ B, setIntegral_rnDeriv_smul hac hB]
    exact hdom B hB
  have hAE := norm_density_le_of_setIntegral hφ hd hlocal
  letI := norm_density_measure_finite hc
  refine Measure.le_iff.2 fun B hB => ?_
  have hI : (∫ s in B, ‖c s‖ ∂μ) ≤ σ.real B := by
    rw [← Measure.setIntegral_toReal_rnDeriv hσ B, ← setIntegral_rnDeriv_smul hac hB]
    have he (s : α) : a s • ‖c s‖ = ‖a s • c s‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ a s)]
      rfl
    change (∫ s in B, a s • ‖c s‖ ∂τ) ≤ ∫ s in B, d s ∂τ
    simp only [he]
    exact setIntegral_mono_ae hφ.norm.integrableOn hd.integrableOn hAE
  have hh : (μ.withDensity (fun s => ‖c s‖ₑ)).real B ≤ σ.real B :=
    (norm_density_measure_real hc hB).trans_le hI
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 hh

variable {E : Type*} [Norm E] {diamond : UV.SectorPlane.Plane E}

/-- The absolute variation of the complex cross measure. Its least-measure
property on every bounded spectral restriction is proved below. -/
def SetwiseSpectralCompletion.crossVariation (C : SetwiseSpectralCompletion diamond) : Measure ℝ :=
  C.trace.withDensity (fun s => ‖C.crossDensity s‖ₑ)

theorem SetwiseSpectralCompletion.crossVariation_local_spec
    (C : SetwiseSpectralCompletion diamond) (n : ℕ) :
    let V := C.crossVariation.restrict (spectralWindow n)
    IsFiniteMeasure V ∧
    (∀ B, MeasurableSet B → ‖C.cross n B‖ ≤ V.real B) ∧
    ∀ σ : Measure ℝ, IsFiniteMeasure σ →
      (∀ B, MeasurableSet B → ‖C.cross n B‖ ≤ σ.real B) → V ≤ σ := by
  dsimp only
  letI := C.localTrace_finite n
  have hc := (C.localCrossDensity_integrable n).congr (C.crossDensity_eq_local n).symm
  rw [SetwiseSpectralCompletion.crossVariation, restrict_withDensity (show MeasurableSet (spectralWindow n) from measurableSet_Icc)]
  change IsFiniteMeasure ((C.localTrace n).withDensity (fun s => ‖C.crossDensity s‖ₑ)) ∧ _
  refine ⟨norm_density_measure_finite hc, ?_, ?_⟩
  · intro B hB
    change ‖C.cross n B‖ ≤ ((C.localTrace n).withDensity (fun s => ‖C.crossDensity s‖ₑ)).real B
    rw [norm_density_measure_real hc hB, ← C.crossDensity_integral_local n hB]
    exact norm_integral_le_integral_norm _
  · intro σ hσ hdom
    letI := hσ
    apply finite_norm_density_least hc
    intro B hB
    rw [C.crossDensity_integral_local n hB]
    exact hdom B hB

theorem SetwiseSpectralCompletion.variationStieltjes_eq
    (C : SetwiseSpectralCompletion diamond) (x : ℝ) :
    diagonalStieltjes C.crossVariation x =
      stieltjes C.trace id (fun s => ‖C.crossDensity s‖) x := by
  unfold diagonalStieltjes SetwiseSpectralCompletion.crossVariation stieltjes
  rw [integral_withDensity_eq_integral_toReal_smul
    C.crossDensity_measurable.enorm (ae_of_all _ fun _ => enorm_lt_top)]
  apply integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only [toReal_enorm, smul_eq_mul, id_eq, mul_comm]

/-- The exact budget bounds for the actual least variation measure of the
locally finite setwise-positive cross entry, with independent diagonals. -/
theorem SetwiseSpectralCompletion.variation_budget
    (C : SetwiseSpectralCompletion diamond) {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hi₁ : Integrable (stieltjesWeight y) C.first)
    (hi₂ : Integrable (stieltjesWeight y) C.second) :
    Integrable (stieltjesWeight x) C.crossVariation ∧
    (diagonalStieltjes C.crossVariation x)^2 ≤
      diagonalStieltjes C.first x * diagonalStieltjes C.second x ∧
    2 * diagonalStieltjes C.crossVariation x ≤
      diagonalStieltjes C.first x + diagonalStieltjes C.second x := by
  have h := C.stieltjes_budget hx hy hi₁ hi₂
  rw [C.variationStieltjes_eq]
  refine ⟨?_, h.2⟩
  unfold SetwiseSpectralCompletion.crossVariation
  rw [integrable_withDensity_iff_integrable_smul'
    C.crossDensity_measurable.enorm (ae_of_all _ fun _ => enorm_lt_top)]
  simpa only [toReal_enorm, smul_eq_mul, mul_comm] using h.1

end UV.RevisionSpectrum
