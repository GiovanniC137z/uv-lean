import UV.ContinueSewnFlagResolution
import UV.ContinueSewnFlagDisplacementAtoms

/-! The Gaussian readout as a literal unit vector in the original
complex L² space, and its finite positive displacement law. -/

noncomputable section
open MeasureTheory Real Filter
open scoped ENNReal InnerProductSpace RealInnerProductSpace Topology ComplexConjugate
namespace UV.SewnFlags

private theorem oneScaleDensity_continuous (ℓ : ℝ) : Continuous (oneScaleDisplacementDensity ℓ) := by
  unfold oneScaleDisplacementDensity
  fun_prop

private theorem oneScaleDensity_nonneg (ℓ : ℝ) (d : ScalarMomentum) : 0 ≤ oneScaleDisplacementDensity ℓ d := by
  unfold oneScaleDisplacementDensity
  positivity

private theorem oneScaleDensity_integrable {ℓ : ℝ} (hℓ : 0 < ℓ) : Integrable (oneScaleDisplacementDensity ℓ) := by
  have ha : 0 < (2*ℓ^2)⁻¹ := by positivity
  have he : oneScaleDisplacementDensity ℓ = fun d => ((2*π*ℓ^2)^2)⁻¹ * exp (-(2*ℓ^2)⁻¹*‖d‖^2) := by
    funext d
    rw [oneScaleDensity_eq hℓ]
    congr 2
    ring
  rw [he]
  exact (scalar_gaussian_integrable ha).const_mul _

def oneScaleDisplacementLaw (ℓ : ℝ) : Measure ScalarMomentum :=
  volume.withDensity (fun d => ENNReal.ofReal (oneScaleDisplacementDensity ℓ d))

theorem oneScaleDisplacementLaw_probability {ℓ : ℝ} (hℓ : 0 < ℓ) :
    IsProbabilityMeasure (oneScaleDisplacementLaw ℓ) := by
  refine ⟨?_⟩
  unfold oneScaleDisplacementLaw
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (oneScaleDensity_integrable hℓ)
      (ae_of_all _ (oneScaleDensity_nonneg ℓ)),oneScaleDisplacementDensity_integral hℓ,ENNReal.ofReal_one]

private theorem oneScalePointer_as_complex_nonneg_norm (ℓ : ℝ) (d x : ScalarMomentum) :
    ‖(oneScalePointer ℓ d x:ℂ)‖ = oneScalePointer ℓ d x := by
  rw [Complex.norm_real,Real.norm_of_nonneg (oneScalePointer_nonneg ℓ d x)]

private theorem oneScalePointer_memLp {ℓ : ℝ} (hℓ : 0 < ℓ) (d : ScalarMomentum) :
    MemLp (fun x => (oneScalePointer ℓ d x:ℂ)) 2 (volume : Measure ScalarMomentum) := by
  have hm : Continuous (fun x => (oneScalePointer ℓ d x:ℂ)) := by
    unfold oneScalePointer
    fun_prop
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  simp_rw [oneScalePointer_as_complex_nonneg_norm,oneScalePointer_sq,sub_eq_add_neg]
  exact ((measurePreserving_add_right (volume : Measure ScalarMomentum) (-d)).integrable_comp_emb
    (Homeomorph.addRight (-d)).measurableEmbedding).2 (oneScaleDensity_integrable hℓ)

def oneScalePointerVector {ℓ : ℝ} (hℓ : 0 < ℓ) (d : ScalarMomentum) :
    Lp ℂ 2 (volume : Measure ScalarMomentum) :=
  (oneScalePointer_memLp hℓ d).toLp (fun x => (oneScalePointer ℓ d x:ℂ))

theorem oneScalePointerVector_inner {ℓ : ℝ} (hℓ : 0 < ℓ) (d e : ScalarMomentum) :
    ⟪oneScalePointerVector hℓ d,oneScalePointerVector hℓ e⟫_ℂ = ↑(exp (-‖d-e‖^2/(8*ℓ^2))) := by
  rw [L2.inner_def]
  have hde : (∫ x, ⟪oneScalePointerVector hℓ d x,oneScalePointerVector hℓ e x⟫_ℂ) =
      ∫ x, ((oneScalePointer ℓ d x*oneScalePointer ℓ e x:ℝ):ℂ) := by
    apply integral_congr_ae
    filter_upwards [(oneScalePointer_memLp hℓ d).coeFn_toLp,(oneScalePointer_memLp hℓ e).coeFn_toLp] with x hd he
    change (oneScalePointerVector hℓ d) x = (oneScalePointer ℓ d x:ℂ) at hd
    change (oneScalePointerVector hℓ e) x = (oneScalePointer ℓ e x:ℂ) at he
    simp only [hd,he,RCLike.inner_apply,Complex.conj_ofReal,Complex.ofReal_mul,mul_comm]
  rw [hde,integral_complex_ofReal,oneScalePointer_overlap hℓ]

theorem oneScalePointerVector_norm {ℓ : ℝ} (hℓ : 0 < ℓ) (d : ScalarMomentum) :
    ‖oneScalePointerVector hℓ d‖ = 1 := by
  calc
    _ = sqrt (‖oneScalePointerVector hℓ d‖^2) := (sqrt_sq (norm_nonneg _)).symm
    _ = _ := by rw [norm_sq_eq_re_inner (𝕜 := ℂ),oneScalePointerVector_inner hℓ]; simp

theorem oneScalePointerVector_continuous {ℓ : ℝ} (hℓ : 0 < ℓ) : Continuous (oneScalePointerVector hℓ) := by
  apply continuous_iff_continuousAt.mpr
  intro d
  let f := fun e : ScalarMomentum => sqrt (1 - 2*exp (-‖e-d‖^2/(8*ℓ^2)) + 1)
  have hf : Continuous f := by unfold f; fun_prop
  have hfd : f d = 0 := by norm_num [f]
  have he (e : ScalarMomentum) : ‖oneScalePointerVector hℓ e-oneScalePointerVector hℓ d‖ = f e := by
    rw [← sqrt_sq (norm_nonneg (oneScalePointerVector hℓ e-oneScalePointerVector hℓ d)),
      norm_sub_sq (𝕜 := ℂ),oneScalePointerVector_norm hℓ,oneScalePointerVector_norm hℓ,
      oneScalePointerVector_inner hℓ]
    change sqrt (1^2 - 2*((exp (-‖e-d‖^2/(8*ℓ^2)):ℝ):ℂ).re+1^2) = f e
    simp only [f,Complex.ofReal_re,one_pow]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp_rw [he]
  simpa only [hfd] using (hf.continuousAt (x := d)).tendsto

private theorem oneScaleReadout_memLp {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ScalarMomentum) :
    MemLp (oneScaleMarkedAmplitude ℓ k) 2 (volume : Measure ScalarMomentum) := by
  have hc : Continuous (oneScaleMarkedAmplitude ℓ k) := by
    have he := funext (oneScaleMarkedAmplitude_exact hℓ k)
    rw [he]
    dsimp only
    unfold stableFourierPhase
    fun_prop
  exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    (oneScaleMarkedAmplitude_inclusive hℓ k).1

def oneScaleReadoutVector {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ScalarMomentum) :
    Lp ℂ 2 (volume : Measure ScalarMomentum) :=
  (oneScaleReadout_memLp hℓ k).toLp (oneScaleMarkedAmplitude ℓ k)

/-- The coordinate reading integral is the actual Bochner superposition
in the complex L² space of all final readings. -/
theorem oneScaleMarkedHilbert_eq_readout {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ScalarMomentum) :
    markedAmplitude (oneScaleDisplacementLaw ℓ) (oneScalePointerVector hℓ) k = oneScaleReadoutVector hℓ k := by
  let μ := oneScaleDisplacementLaw ℓ
  letI : IsProbabilityMeasure μ := oneScaleDisplacementLaw_probability hℓ
  let A := markedAmplitude μ (oneScalePointerVector hℓ) k
  let V := oneScaleReadoutVector hℓ k
  have hA : Integrable (fun d => stableFourierPhase d k • oneScalePointerVector hℓ d) μ :=
    marked_phase_integrable μ _ (oneScalePointerVector_continuous hℓ).stronglyMeasurable
      (fun d => (oneScalePointerVector_norm hℓ d).le) k
  have hPair (v : Lp ℂ 2 (volume : Measure ScalarMomentum)) : ⟪v,A⟫_ℂ = ⟪v,V⟫_ℂ := by
    have hvm := Lp.aestronglyMeasurable v
    let f := hvm.mk v
    have hf : StronglyMeasurable f := hvm.stronglyMeasurable_mk
    have hvf : (v : ScalarMomentum → ℂ) =ᵐ[volume] f := hvm.ae_eq_mk
    have hIv : Integrable (fun x => ‖f x‖^2) := by
      exact ((memLp_two_iff_integrable_sq_norm hvm).mp (Lp.memLp v)).congr
        (hvf.mono fun x hx => congrArg (fun u : ℂ => ‖u‖^2) hx)
    have hIψ (d : ScalarMomentum) : Integrable (fun x => (oneScalePointer ℓ d x)^2) := by
      have h := (memLp_two_iff_integrable_sq_norm (oneScalePointer_memLp hℓ d).aestronglyMeasurable).mp
        (oneScalePointer_memLp hℓ d)
      simpa only [oneScalePointer_as_complex_nonneg_norm] using h
    let P := ScalarMomentum × ScalarMomentum
    let G := fun p : P => conj (f p.2) * stableFourierPhase p.1 k * (oneScalePointer ℓ p.1 p.2:ℂ)
    have hφ : Continuous (fun p : P => stableFourierPhase p.1 k) := by
      unfold P stableFourierPhase
      fun_prop
    have hψ : Continuous (fun p : P => (oneScalePointer ℓ p.1 p.2:ℂ)) := by
      unfold P oneScalePointer
      fun_prop
    have hGm : StronglyMeasurable G :=
      ((Complex.continuous_conj.comp_stronglyMeasurable (hf.comp_measurable measurable_snd)).mul
        hφ.measurable.stronglyMeasurable).mul hψ.measurable.stronglyMeasurable
    let Q := fun (d x : ScalarMomentum) => (‖f x‖^2+(oneScalePointer ℓ d x)^2)/2
    have hQ (d : ScalarMomentum) : Integrable (Q d) := (hIv.add (hIψ d)).div_const 2
    have hBound (d x : ScalarMomentum) : ‖G (d,x)‖ ≤ Q d x := by
      dsimp only [G,Q]
      rw [norm_mul,norm_mul,stableFourierPhase_norm,mul_one,Complex.norm_conj,
        oneScalePointer_as_complex_nonneg_norm]
      nlinarith [sq_nonneg (‖f x‖-oneScalePointer ℓ d x)]
    have hIG (d : ScalarMomentum) : Integrable (fun x => G (d,x)) :=
      (hQ d).mono' (hGm.comp_measurable measurable_prodMk_left).aestronglyMeasurable
        (ae_of_all _ (hBound d))
    have hG : Integrable G (μ.prod volume) := by
      refine (integrable_prod_iff hGm.aestronglyMeasurable).mpr ⟨ae_of_all _ hIG,?_⟩
      have hNorm : StronglyMeasurable (fun d => ∫ x, ‖G (d,x)‖) := hGm.norm.integral_prod_right'
      apply Integrable.of_bound hNorm.aestronglyMeasurable (((∫ x, ‖f x‖^2)+1)/2)
      filter_upwards with d
      rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg (G (d,x)))]
      refine (integral_mono (hIG d).norm (hQ d) (hBound d)).trans_eq ?_
      unfold Q
      rw [integral_div,integral_add hIv (hIψ d),oneScalePointer_normalized hℓ d]
    have hL (d : ScalarMomentum) : (∫ x, G (d,x)) = stableFourierPhase d k * ⟪v,oneScalePointerVector hℓ d⟫_ℂ := by
      rw [L2.inner_def,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hvf,(oneScalePointer_memLp hℓ d).coeFn_toLp] with x hx hy
      change (oneScalePointerVector hℓ d) x = (oneScalePointer ℓ d x:ℂ) at hy
      dsimp only [G]
      rw [hx,hy,RCLike.inner_apply]
      ring
    have hR (x : ScalarMomentum) : (∫ d, G (d,x) ∂μ) = conj (f x)*oneScaleMarkedAmplitude ℓ k x := by
      have hm : Measurable (fun d => ENNReal.ofReal (oneScaleDisplacementDensity ℓ d)) :=
        (oneScaleDensity_continuous ℓ).measurable.ennreal_ofReal
      unfold μ oneScaleDisplacementLaw oneScaleMarkedAmplitude
      rw [integral_withDensity_eq_integral_toReal_smul hm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
        ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with d
      dsimp only [G]
      rw [ENNReal.toReal_ofReal (oneScaleDensity_nonneg ℓ d),Complex.real_smul]
      ring
    calc
      _ = ∫ d, stableFourierPhase d k * ⟪v,oneScalePointerVector hℓ d⟫_ℂ ∂μ := by
        unfold A markedAmplitude
        rw [← integral_inner hA v]
        simp_rw [inner_smul_right]
      _ = ∫ d, ∫ x, G (d,x) ∂volume ∂μ := by simp_rw [hL]
      _ = ∫ x, ∫ d, G (d,x) ∂μ ∂volume := integral_integral_swap (f := fun d x => G (d,x)) hG
      _ = _ := by
        simp_rw [hR]
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hvf,(oneScaleReadout_memLp hℓ k).coeFn_toLp] with x hx hy
        change V x = oneScaleMarkedAmplitude ℓ k x at hy
        rw [hx,hy,RCLike.inner_apply]
        ring
  have hz : ⟪A-V,A-V⟫_ℂ = 0 := by rw [inner_sub_right,hPair (A-V),sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

theorem oneScaleMarkedHilbert_inclusive {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ScalarMomentum) :
    ‖markedAmplitude (oneScaleDisplacementLaw ℓ) (oneScalePointerVector hℓ) k‖^2 =
      (2/3:ℝ)^2*exp (-(2*ℓ^2/3)*‖k‖^2) := by
  rw [oneScaleMarkedHilbert_eq_readout hℓ k,norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def]
  have hSelf (x : ScalarMomentum) :
      ⟪oneScaleReadoutVector hℓ k x,oneScaleReadoutVector hℓ k x⟫_ℂ = ↑(‖oneScaleReadoutVector hℓ k x‖^2) := by
    rw [inner_self_eq_norm_sq_to_K]
    exact (Complex.ofReal_pow _ _).symm
  simp_rw [hSelf]
  rw [integral_complex_ofReal]
  change (∫ x, ‖oneScaleReadoutVector hℓ k x‖^2) = _
  have he : (∫ x, ‖oneScaleReadoutVector hℓ k x‖^2) = ∫ x, ‖oneScaleMarkedAmplitude ℓ k x‖^2 :=
    integral_congr_ae ((oneScaleReadout_memLp hℓ k).coeFn_toLp.mono fun x hx =>
      congrArg (fun z : ℂ => ‖z‖^2) hx)
  rw [he,(oneScaleMarkedAmplitude_inclusive hℓ k).2]

end UV.SewnFlags
