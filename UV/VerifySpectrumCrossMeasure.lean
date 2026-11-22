import UV.VerifySpectrumCrossNecessity

/-! The admitted cross transform is represented by actual locally finite
Jordan measures. The atom carries unit spectral normalization separately
from the Lebesgue continuum. -/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

namespace UV.RevisionSpectrum

theorem verify_cross_continuum_measurable (a M m₂ : ℝ) :
    Measurable (verifyCrossContinuum a M m₂) := by
  have hd : Measurable (crossDensity a M m₂) := by
    unfold crossDensity
    exact Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const
  unfold verifyCrossContinuum
  have ht : MeasurableSet {s : ℝ | s=m₂ ∧ M^2<m₂} :=
    (measurableSet_singleton m₂).inter (MeasurableSet.const _)
  exact Measurable.ite ht measurable_const hd

def verifyCrossPositive (a M m₂ : ℝ) : Measure ℝ :=
  ENNReal.ofReal (verifyCrossResidue a M m₂) • Measure.dirac m₂ +
    (volume.restrict (Ioi (M^2))).withDensity
      (fun s => ENNReal.ofReal (verifyCrossContinuum a M m₂ s))

def verifyCrossNegative (a M m₂ : ℝ) : Measure ℝ :=
  ENNReal.ofReal (-(verifyCrossResidue a M m₂)) • Measure.dirac m₂ +
    (volume.restrict (Ioi (M^2))).withDensity
      (fun s => ENNReal.ofReal (-(verifyCrossContinuum a M m₂ s)))

theorem verify_cross_jordan_mutuallySingular (a M m₂ : ℝ) :
    verifyCrossPositive a M m₂ ⟂ₘ verifyCrossNegative a M m₂ := by
  let ρ := volume.restrict (Ioi (M^2))
  let r := verifyCrossResidue a M m₂
  let h := verifyCrossContinuum a M m₂
  have hbase : Measure.dirac m₂ ⟂ₘ ρ :=
    (mutuallySingular_dirac m₂ volume).mono_ac
      (Measure.AbsolutelyContinuous.rfl) Measure.absolutelyContinuous_restrict
  have hAA : ENNReal.ofReal r • Measure.dirac m₂ ⟂ₘ
      ENNReal.ofReal (-r) • Measure.dirac m₂ := by
    rcases le_total r 0 with hr | hr
    · simp [ENNReal.ofReal_eq_zero.mpr hr]
    · simp [ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr hr)]
  have hAD : ENNReal.ofReal r • Measure.dirac m₂ ⟂ₘ
      ρ.withDensity (fun s => ENNReal.ofReal (-h s)) :=
    hbase.mono_ac Measure.smul_absolutelyContinuous (withDensity_absolutelyContinuous _ _)
  have hDA : ρ.withDensity (fun s => ENNReal.ofReal (h s)) ⟂ₘ
      ENNReal.ofReal (-r) • Measure.dirac m₂ :=
    hbase.symm.mono_ac (withDensity_absolutelyContinuous _ _) Measure.smul_absolutelyContinuous
  have hDD : ρ.withDensity (fun s => ENNReal.ofReal (h s)) ⟂ₘ
      ρ.withDensity (fun s => ENNReal.ofReal (-h s)) :=
    withDensity_ofReal_mutuallySingular (verify_cross_continuum_measurable a M m₂)
  exact (hAA.add_right hAD).add_left (hDA.add_right hDD)

theorem verify_cross_jordan_support {a M m₂ : ℝ} (hm₂ : 0≤m₂) :
    (∀ᵐ s ∂verifyCrossPositive a M m₂,0≤s) ∧
    (∀ᵐ s ∂verifyCrossNegative a M m₂,0≤s) := by
  let ρ : Measure ℝ := volume.restrict (Ioi (M^2))
  have hd : ∀ᵐ s ∂Measure.dirac m₂,0≤s := by
    apply (ae_dirac_iff (measurableSet_le measurable_const measurable_id)).2
    exact hm₂
  have hρ : ∀ᵐ s ∂ρ,0≤s :=
    (ae_restrict_mem measurableSet_Ioi).mono fun s hs => (sq_nonneg M).trans (mem_Ioi.mp hs).le
  unfold verifyCrossPositive verifyCrossNegative
  exact ⟨ae_add_measure_iff.2 ⟨Measure.smul_absolutelyContinuous.ae_le hd,
        (withDensity_absolutelyContinuous _ _).ae_le hρ⟩,
    ae_add_measure_iff.2 ⟨Measure.smul_absolutelyContinuous.ae_le hd,
        (withDensity_absolutelyContinuous _ _).ae_le hρ⟩⟩

private theorem verify_integrable_ordinary_cross_jordan {a M m₂ x : ℝ} (ha : 0<a)
    (hm₂ : 0≤m₂) (hx : 0<x)
    (hadm : m₂≤M^2 ∨ Real.sin (a*Real.sqrt (m₂-M^2))=0) :
    let ρ : Measure ℝ := volume.restrict (Ioi (M^2))
    let h := verifyCrossContinuum a M m₂
    Integrable (fun s => max (h s) 0 * stieltjesWeight x s) ρ ∧
    Integrable (fun s => max (-h s) 0 * stieltjesWeight x s) ρ := by
  dsimp only
  have hI := (verify_cross_stieltjes ha hm₂ hx hadm).1
  have hI' : IntegrableOn (fun s => verifyCrossContinuum a M m₂ s * stieltjesWeight x s)
      (Ioi (M^2)) := by
    simpa only [stieltjesWeight, div_eq_mul_inv] using hI
  have hZ : Integrable (fun _ : ℝ => (0:ℝ)) (volume.restrict (Ioi (M^2))) := integrable_zero _ _ _
  constructor
  · apply (hI'.sup hZ).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hpos := (stieltjesWeight_pos hx ((sq_nonneg M).trans (mem_Ioi.mp hs).le)).le
    change max (verifyCrossContinuum a M m₂ s * stieltjesWeight x s) 0 =
      max (verifyCrossContinuum a M m₂ s) 0 * stieltjesWeight x s
    rw [max_mul_of_nonneg _ _ hpos, zero_mul]
  · apply (hI'.neg.sup hZ).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hpos := (stieltjesWeight_pos hx ((sq_nonneg M).trans (mem_Ioi.mp hs).le)).le
    change max (-(verifyCrossContinuum a M m₂ s * stieltjesWeight x s)) 0 =
      max (-(verifyCrossContinuum a M m₂ s)) 0 * stieltjesWeight x s
    rw [← neg_mul, max_mul_of_nonneg _ _ hpos, zero_mul]

/-- The signed measure exactly represents the damped cross covariance and
has finite weighted total variation at every positive spectral argument. -/
theorem verify_cross_jordan_representation {a M m₂ x : ℝ} (ha : 0<a)
    (hm₂ : 0≤m₂) (hx : 0<x)
    (hadm : m₂≤M^2 ∨ Real.sin (a*Real.sqrt (m₂-M^2))=0) :
    Integrable (stieltjesWeight x) (verifyCrossPositive a M m₂) ∧
    Integrable (stieltjesWeight x) (verifyCrossNegative a M m₂) ∧
    diagonalStieltjes (verifyCrossPositive a M m₂) x -
      diagonalStieltjes (verifyCrossNegative a M m₂) x =
        verifyCrossCovariance a M m₂ x := by
  let ρ : Measure ℝ := volume.restrict (Ioi (M^2))
  let h := verifyCrossContinuum a M m₂
  let r := verifyCrossResidue a M m₂
  let w := stieltjesWeight x
  have hd : Measurable h := verify_cross_continuum_measurable a M m₂
  obtain ⟨hiP,hiN⟩ := verify_integrable_ordinary_cross_jordan ha hm₂ hx hadm
  have haD : Integrable w (Measure.dirac m₂) := integrable_dirac enorm_lt_top
  have haP := haD.smul_measure (c := ENNReal.ofReal r) ENNReal.ofReal_ne_top
  have haN := haD.smul_measure (c := ENNReal.ofReal (-r)) ENNReal.ofReal_ne_top
  have hIPos : Integrable w (ρ.withDensity (fun s => ENNReal.ofReal (h s))) := by
    rw [integrable_withDensity_iff_integrable_smul' hd.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simpa only [ENNReal.toReal_ofReal', smul_eq_mul] using hiP
  have hINeg : Integrable w (ρ.withDensity (fun s => ENNReal.ofReal (-h s))) := by
    rw [integrable_withDensity_iff_integrable_smul' hd.neg.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simpa only [ENNReal.toReal_ofReal', smul_eq_mul] using hiN
  refine ⟨haP.add_measure hIPos,haN.add_measure hINeg,?_⟩
  change (∫ s, w s ∂(ENNReal.ofReal r • Measure.dirac m₂ +
    ρ.withDensity fun s => ENNReal.ofReal (h s))) -
    (∫ s, w s ∂(ENNReal.ofReal (-r) • Measure.dirac m₂ +
      ρ.withDensity fun s => ENNReal.ofReal (-h s))) = _
  rw [integral_add_measure haP hIPos, integral_add_measure haN hINeg]
  rw [integral_smul_measure, integral_smul_measure, integral_dirac]
  rw [integral_withDensity_eq_integral_toReal_smul hd.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul hd.neg.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  have hmax (s : ℝ) : max s 0-max (-s) 0=s := by
    rcases le_total s 0 with hs | hs
    · rw [max_eq_right hs,max_eq_left (neg_nonneg.mpr hs)]
      ring
    · rw [max_eq_left hs,max_eq_right (neg_nonpos.mpr hs)]
      ring
  have hA : max r 0*w m₂-max (-r) 0*w m₂=r*w m₂ := by
    rw [← sub_mul,hmax]
  have hD : (∫ s, max (h s) 0*w s ∂ρ)-(∫ s, max (-h s) 0*w s ∂ρ) =
      ∫ s, h s*w s ∂ρ := by
    rw [← integral_sub hiP hiN]
    apply integral_congr_ae
    filter_upwards with s
    rw [← sub_mul,hmax]
  rw [add_sub_add_comm,hA,hD]
  exact (verify_cross_stieltjes ha hm₂ hx hadm).2

theorem verify_weighted_positive_spectrum_locallyFinite {ν : Measure ℝ} {x : ℝ}
    (hx : 0<x) (hν : ∀ᵐ s ∂ν,0≤s) (hi : Integrable (stieltjesWeight x) ν) :
    IsLocallyFiniteMeasure ν := by
  refine ⟨fun t => ⟨ball t 1, ball_mem_nhds t zero_lt_one,?_⟩⟩
  let C := (x+|t|+1)⁻¹
  have hc : 0<C := by dsimp [C]; positivity
  have hI : IntegrableOn (fun _ : ℝ => C) (ball t 1) ν := by
    apply hi.integrableOn.mono' aestronglyMeasurable_const
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hν] with s hs hs₀
    have hst : s≤|t|+1 := by
      have hdist := mem_ball.mp hs
      rw [Real.dist_eq] at hdist
      linarith [(abs_lt.mp hdist).2, le_abs_self t]
    rw [Real.norm_of_nonneg hc.le]
    exact inv_anti₀ (by positivity : 0<x+s) (by linarith)
  exact ((integrableOn_const_iff).1 hI).resolve_left (enorm_ne_zero.mpr hc.ne')

/-- Existence of an ordinary weighted signed spectral measure exactly
under the source's resonance criterion. The two supplied finite weights
are those of the Jordan parts at one arbitrary positive reference. -/
theorem verify_cross_signed_spectral_exists_iff {a M m₂ y : ℝ} (ha : 0<a) (hm₂ : 0≤m₂)
    (hy : 0<y) :
    (∃ νpos νneg : Measure ℝ, νpos ⟂ₘ νneg ∧
      IsLocallyFiniteMeasure νpos ∧ IsLocallyFiniteMeasure νneg ∧
      (∀ᵐ s ∂νpos,0≤s) ∧ (∀ᵐ s ∂νneg,0≤s) ∧
      Integrable (stieltjesWeight y) νpos ∧ Integrable (stieltjesWeight y) νneg ∧
      ∀ x : ℝ, 0<x → diagonalStieltjes νpos x-diagonalStieltjes νneg x =
        verifyCrossCovariance a M m₂ x) ↔
    (m₂≤M^2 ∨ Real.sin (a*Real.sqrt (m₂-M^2))=0) := by
  constructor
  · rintro ⟨νpos,νneg,_,_,_,hspos,hsneg,hipos,hineg,hEq⟩
    exact (verify_cross_signed_necessity_and_atom a M hm₂ hy hspos hsneg hipos hineg hEq).1
  · intro hres
    obtain ⟨hp,hn⟩ := verify_cross_jordan_support (a:=a) (M:=M) hm₂
    obtain ⟨hiP,hiN,_⟩ := verify_cross_jordan_representation ha hm₂ hy hres
    exact ⟨verifyCrossPositive a M m₂,verifyCrossNegative a M m₂,
      verify_cross_jordan_mutuallySingular a M m₂,
      verify_weighted_positive_spectrum_locallyFinite hy hp hiP,
      verify_weighted_positive_spectrum_locallyFinite hy hn hiN,
      hp,hn,hiP,hiN,fun _ hx => (verify_cross_jordan_representation ha hm₂ hx hres).2.2⟩

end UV.RevisionSpectrum
