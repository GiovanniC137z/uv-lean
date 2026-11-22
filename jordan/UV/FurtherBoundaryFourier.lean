import Mathlib.Analysis.Distribution.Sobolev
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-! Fourier moments of finite overlap measures on a Euclidean momentum
plane. The variable of the unitary Fourier transform is k/(2π), so the
physical momentum measure (2π)^(-D) d^D k is ordinary volume here. -/

noncomputable section
open MeasureTheory Real Complex FourierTransform
open scoped FourierTransform SchwartzMap ENNReal InnerProductSpace

namespace UV.ContinuationBoundary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Phase of a finite positive measure, with physical momentum 2πq. -/
def positivePhase (μ : Measure E) (q : E) : ℂ :=
  ∫ x, (Real.fourierChar ⟪x, q⟫_ℝ : ℂ) ∂μ

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem positivePhase_eq_charFun (μ : Measure E) (q : E) :
    positivePhase μ q = charFun μ ((2 * Real.pi) • q) := by
  unfold positivePhase charFun
  apply integral_congr_ae
  filter_upwards with x
  rw [Real.fourierChar_apply, inner_smul_right]

private theorem positive_phase_test (μ : Measure E) [IsFiniteMeasure μ]
    (ψ : 𝓢(E, ℂ)) :
    (𝓕⁻ (μ.toTemperedDistribution : 𝓢'(E, ℂ))) ψ =
      ∫ q, (ψ q) * positivePhase μ q := by
  have hf : Integrable (fun _ : E => (1 : ℂ)) μ := integrable_const _
  have hc : Continuous (fun p : E × E => (-innerₗ E) p.1 p.2) := by
    change Continuous fun p : E × E => -⟪p.1, p.2⟫_ℝ
    exact continuous_inner.neg
  have hflip : (-innerₗ E).flip = -innerₗ E := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change (-⟪y, x⟫_ℝ) = -⟪x, y⟫_ℝ
    rw [real_inner_comm y x]
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := -innerₗ E)
    Real.continuous_fourierChar hc hf (ψ.integrable (μ := volume))
  rw [hflip] at h
  have hpos (q : E) : VectorFourier.fourierIntegral Real.fourierChar μ (-innerₗ E)
      (fun _ : E => (1 : ℂ)) q = positivePhase μ q := by
    simp [VectorFourier.fourierIntegral, positivePhase, Circle.smul_def, smul_eq_mul]
  rw [TemperedDistribution.fourierInv_apply]
  rw [Measure.toTemperedDistribution_apply μ (𝓕⁻ ψ)]
  simp only [hpos, smul_eq_mul, one_mul] at h
  simpa [VectorFourier.fourierIntegral, smul_eq_mul, mul_comm,
    SchwartzMap.fourierInv_coe, Real.fourierInv_eq] using h.symm

/-- Four Jordan parts give the finite complex overlap measure. -/
def complexOverlapDistribution (ν : ComplexMeasure E) : 𝓢'(E, ℂ) :=
    ν.re.toJordanDecomposition.posPart.toTemperedDistribution -
      ν.re.toJordanDecomposition.negPart.toTemperedDistribution +
    Complex.I • (ν.im.toJordanDecomposition.posPart.toTemperedDistribution -
      ν.im.toJordanDecomposition.negPart.toTemperedDistribution)

def complexOverlapPhase (ν : ComplexMeasure E) (q : E) : ℂ :=
    positivePhase ν.re.toJordanDecomposition.posPart q -
      positivePhase ν.re.toJordanDecomposition.negPart q +
    Complex.I * (positivePhase ν.im.toJordanDecomposition.posPart q -
      positivePhase ν.im.toJordanDecomposition.negPart q)

private theorem phase_measurable (μ : Measure E) [IsFiniteMeasure μ] : Measurable (positivePhase μ) := by
  change Measurable (fun q => positivePhase μ q)
  simp_rw [positivePhase_eq_charFun]
  exact (stronglyMeasurable_charFun (μ := μ)).measurable.comp
    (continuous_const_smul (2 * Real.pi : ℝ)).measurable

omit [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem phase_bound (μ : Measure E) (q : E) :
    ‖positivePhase μ q‖ ≤ μ.real Set.univ := by
  rw [positivePhase_eq_charFun]
  exact norm_charFun_le _

private theorem phase_test_integrable (μ : Measure E) [IsFiniteMeasure μ]
    (ψ : 𝓢(E, ℂ)) : Integrable (fun q => ψ q * positivePhase μ q) := by
  apply (ψ.integrable.norm.const_mul (μ.real Set.univ)).mono'
  · exact (ψ.continuous.measurable.mul (phase_measurable μ)).aestronglyMeasurable
  · filter_upwards with q
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (phase_bound μ q) (norm_nonneg _)

theorem complex_overlap_phase_test (ν : ComplexMeasure E) (ψ : 𝓢(E, ℂ)) :
    (𝓕⁻ (complexOverlapDistribution ν)) ψ = ∫ q, (ψ q) * complexOverlapPhase ν q := by
  let p := ν.re.toJordanDecomposition.posPart
  let q := ν.re.toJordanDecomposition.negPart
  let r := ν.im.toJordanDecomposition.posPart
  let s := ν.im.toJordanDecomposition.negPart
  change (𝓕⁻ (p.toTemperedDistribution - q.toTemperedDistribution +
      Complex.I • (r.toTemperedDistribution - s.toTemperedDistribution))) ψ =
        ∫ x, ψ x * (positivePhase p x - positivePhase q x +
          Complex.I * (positivePhase r x - positivePhase s x))
  have hsub (a b : 𝓢'(E, ℂ)) : 𝓕⁻ (a - b) = (𝓕⁻ a) - (𝓕⁻ b) :=
    map_sub (fourierInvCLM ℂ 𝓢'(E, ℂ)) a b
  simp only [fourierInv_add, hsub, fourierInv_smul, add_apply, sub_apply, smul_apply, positive_phase_test]
  simp only [mul_add, mul_sub, ← mul_assoc]
  simp_rw [mul_comm (ψ _) Complex.I, mul_assoc]
  let P := fun x => ψ x * positivePhase p x
  let Q := fun x => ψ x * positivePhase q x
  let R := fun x => ψ x * positivePhase r x
  let S := fun x => ψ x * positivePhase s x
  change _ = ∫ x, ((P - Q) + ((fun y => Complex.I * R y) - (fun y => Complex.I * S y))) x
  rw [integral_add' ((phase_test_integrable p ψ).sub (phase_test_integrable q ψ))
    (((phase_test_integrable r ψ).const_mul Complex.I).sub ((phase_test_integrable s ψ).const_mul Complex.I)),
    integral_sub' (phase_test_integrable p ψ) (phase_test_integrable q ψ),
    integral_sub' ((phase_test_integrable r ψ).const_mul Complex.I) ((phase_test_integrable s ψ).const_mul Complex.I)]
  simp [integral_const_mul, smul_eq_mul, mul_sub]

private theorem continuous_positivePhase (μ : Measure E) [IsFiniteMeasure μ] :
    Continuous (positivePhase μ) := by
  change Continuous (fun q => positivePhase μ q)
  simp_rw [positivePhase_eq_charFun]
  exact (continuous_charFun (μ := μ)).comp (continuous_const_smul _)

theorem continuous_complexOverlapPhase (ν : ComplexMeasure E) :
    Continuous (complexOverlapPhase ν) := by
  unfold complexOverlapPhase
  exact ((continuous_positivePhase _).sub (continuous_positivePhase _)).add
    (((continuous_positivePhase _).sub (continuous_positivePhase _)).const_mul _)

/-- Exact multiplier for physical wave number 2πq in the unitary
frequency coordinates. Its square is the manuscript weight. -/
def overlapMultiplier (N : ℕ) (q : E) : ℂ :=
  ((1 + ‖(2 * Real.pi) • q‖ ^ 2) ^ ((N : ℝ) / 2) : ℝ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem overlapMultiplier_temperate (N : ℕ) :
    (overlapMultiplier (E := E) N).HasTemperateGrowth := by
  apply Complex.ofRealCLM.hasTemperateGrowth.comp
  exact (Function.hasTemperateGrowth_one_add_norm_sq_rpow E ((N : ℝ) / 2)).comp
    ((2 * Real.pi) • ContinuousLinearMap.id ℝ E).hasTemperateGrowth

def weightedOverlapPhase (N : ℕ) (ν : ComplexMeasure E) (q : E) : ℂ :=
  overlapMultiplier N q * complexOverlapPhase ν q

private theorem weighted_phase_continuous (N : ℕ) (ν : ComplexMeasure E) :
    Continuous (weightedOverlapPhase N ν) :=
  (overlapMultiplier_temperate N).1.continuous.mul (continuous_complexOverlapPhase ν)

def overlapEnergy (N : ℕ) (ν : ComplexMeasure E) : ℝ≥0∞ :=
  ∫⁻ q, ENNReal.ofReal ((1 + ‖(2 * Real.pi) • q‖ ^ 2) ^ N * ‖complexOverlapPhase ν q‖ ^ 2)

theorem overlap_energy_eq_weighted_square (N : ℕ) (ν : ComplexMeasure E) :
    overlapEnergy N ν = ∫⁻ q, ENNReal.ofReal (‖weightedOverlapPhase N ν q‖ ^ 2) := by
  unfold overlapEnergy
  apply lintegral_congr
  intro q
  simp only [weightedOverlapPhase, overlapMultiplier, norm_mul, mul_pow, Complex.norm_real]
  let a := 1 + ‖(2 * Real.pi) • q‖ ^ 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have he : (a ^ ((N : ℝ) / 2)) ^ (2 : ℕ) = a ^ N := by
    rw [← Real.rpow_two, ← Real.rpow_mul ha,
      div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_natCast]
  change _ = ENNReal.ofReal (‖((a ^ ((N : ℝ) / 2)) : ℝ)‖ ^ 2 * _)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg ha _), he]

private theorem overlapEnergy_finite_iff (N : ℕ) (ν : ComplexMeasure E) :
    overlapEnergy N ν ≠ ∞ ↔ MemLp (weightedOverlapPhase N ν) 2 volume := by
  rw [overlap_energy_eq_weighted_square,
    memLp_two_iff_integrable_sq_norm (weighted_phase_continuous N ν).aestronglyMeasurable]
  exact lintegral_ofReal_ne_top_iff_integrable
    ((weighted_phase_continuous N ν).norm.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)

/-- The Bessel-potential operation (1-Δ)^(N/2) in the physical momentum
convention of the source. The sign in the intermediate Fourier transform is
positive. The symbol is even, so the ordinary negative convention produces
the same Bessel operator. -/
def overlapBesselPotential (N : ℕ) (T : 𝓢'(E, ℂ)) : 𝓢'(E, ℂ) :=
  𝓕 (TemperedDistribution.smulLeftCLM ℂ (overlapMultiplier N) (𝓕⁻ T))

private theorem weighted_overlap_phase_test (ν : ComplexMeasure E) (N : ℕ) (ψ : 𝓢(E, ℂ)) :
    (𝓕⁻ (overlapBesselPotential N (complexOverlapDistribution ν))) ψ =
      ∫ q, ψ q * weightedOverlapPhase N ν q := by
  rw [overlapBesselPotential, fourierInv_fourier_eq, TemperedDistribution.smulLeftCLM_apply_apply,
    complex_overlap_phase_test]
  simp only [SchwartzMap.smulLeftCLM_apply_apply (overlapMultiplier_temperate N), smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with q
  unfold weightedOverlapPhase
  ring

private theorem fourier_lp_norm_square (f : Lp (α := E) ℂ 2 volume) :
    ENNReal.ofReal (‖f‖ ^ 2) = ∫⁻ q, ENNReal.ofReal (‖f q‖ ^ 2) := by
  rw [Lp.norm_def, ← ENNReal.toReal_pow, ENNReal.ofReal_toReal (ENNReal.pow_ne_top (Lp.eLpNorm_ne_top f)),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem overlap_energy_bessel_iff (ν : ComplexMeasure E) (N : ℕ) :
    overlapEnergy N ν ≠ ∞ ↔ ∃ g : Lp (α := E) ℂ 2 volume,
      overlapBesselPotential N (complexOverlapDistribution ν) = (g : 𝓢'(E, ℂ)) ∧
        overlapEnergy N ν = ENNReal.ofReal (‖g‖ ^ 2) := by
  constructor
  · intro hf
    have hLp := (overlapEnergy_finite_iff N ν).mp hf
    let f := hLp.toLp (weightedOverlapPhase N ν)
    refine ⟨𝓕 f, ?_, ?_⟩
    · rw [← Lp.fourier_toTemperedDistribution_eq]
      apply (fourierEquiv ℂ 𝓢'(E, ℂ)).symm.injective
      ext ψ
      rw [fourierEquiv_symm_apply, fourierEquiv_symm_apply, weighted_overlap_phase_test, fourierInv_fourier_eq,
        Lp.toTemperedDistribution_apply]
      apply integral_congr_ae
      filter_upwards [hLp.coeFn_toLp] with q hq
      rw [smul_eq_mul, hq]
    · rw [Lp.norm_fourier_eq, fourier_lp_norm_square, overlap_energy_eq_weighted_square]
      apply lintegral_congr_ae
      filter_upwards [hLp.coeFn_toLp] with q hq
      rw [hq]
  · rintro ⟨g, _, hg⟩
    exact hg.trans_ne ENNReal.ofReal_ne_top


/-- There is no extra numerical hypothesis on a Sobolev witness. The
identity of Bessel potentials itself forces the precise squared norm. -/
theorem overlap_bessel_norm_exact (ν : ComplexMeasure E) (N : ℕ)
    (g : Lp (α := E) ℂ 2 volume)
    (hg : overlapBesselPotential N (complexOverlapDistribution ν) = (g : 𝓢'(E, ℂ))) :
    overlapEnergy N ν = ENNReal.ofReal (‖g‖ ^ 2) := by
  let f : Lp (α := E) ℂ 2 volume := 𝓕⁻ g
  have hdist : 𝓕⁻ (overlapBesselPotential N (complexOverlapDistribution ν)) = (f : 𝓢'(E, ℂ)) := by
    rw [hg, Lp.fourierInv_toTemperedDistribution_eq]
  have hlocal₁ : LocallyIntegrable (weightedOverlapPhase N ν) volume :=
    (weighted_phase_continuous N ν).locallyIntegrable
  have hlocal₂ : LocallyIntegrable (f : E → ℂ) volume := (Lp.memLp f).locallyIntegrable (by norm_num)
  have hAE : weightedOverlapPhase N ν =ᵐ[volume] f := by
    apply ae_eq_of_integral_contDiff_smul_eq hlocal₁ hlocal₂
    intro φ hφ hφc
    let ψ : 𝓢(E, ℂ) := (hφc.comp_left Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hφ)
    have hh := congrArg (fun T : 𝓢'(E, ℂ) => T ψ) hdist
    rw [weighted_overlap_phase_test, Lp.toTemperedDistribution_apply] at hh
    change (∫ q, (φ q : ℂ) * weightedOverlapPhase N ν q) =
      (∫ q, (φ q : ℂ) * f q) at hh
    simpa only [Complex.real_smul] using hh
  rw [overlap_energy_eq_weighted_square, ← (Lp.fourierTransformₗᵢ E ℂ).symm.norm_map g,
    fourier_lp_norm_square]
  change (∫⁻ q, ENNReal.ofReal (‖weightedOverlapPhase N ν q‖ ^ 2)) =
    ∫⁻ q, ENNReal.ofReal (‖f q‖ ^ 2)
  apply lintegral_congr_ae
  filter_upwards [hAE] with q hq
  rw [hq]

theorem overlap_finite_iff_bessel_potential (ν : ComplexMeasure E) (N : ℕ) :
    overlapEnergy N ν ≠ ∞ ↔ ∃ h g : Lp (α := E) ℂ 2 volume,
      complexOverlapDistribution ν = (h : 𝓢'(E, ℂ)) ∧
        overlapBesselPotential N (h : 𝓢'(E, ℂ)) = (g : 𝓢'(E, ℂ)) := by
  constructor
  · intro hf
    have hle : overlapEnergy 0 ν ≤ overlapEnergy N ν := by
      unfold overlapEnergy
      apply lintegral_mono
      intro q
      apply ENNReal.ofReal_le_ofReal
      rw [pow_zero, one_mul]
      exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ (le_add_of_nonneg_right (sq_nonneg _)))
    obtain ⟨h, hh, _⟩ := (overlap_energy_bessel_iff ν 0).mp (ne_top_of_le_ne_top hf hle)
    have hz : overlapMultiplier (E := E) 0 = fun _ => (1 : ℂ) := by
      funext q
      simp [overlapMultiplier]
    rw [overlapBesselPotential, hz, TemperedDistribution.smulLeftCLM_const, one_smul,
      fourier_fourierInv_eq] at hh
    obtain ⟨g, hg, _⟩ := (overlap_energy_bessel_iff ν N).mp hf
    exact ⟨h, g, hh, hh ▸ hg⟩
  · rintro ⟨h, g, hh, hg⟩
    rw [← hh] at hg
    rw [overlap_bessel_norm_exact ν N g hg]
    exact ENNReal.ofReal_ne_top


end UV.ContinuationBoundary
