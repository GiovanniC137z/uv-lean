import UV.ScalarLaplace
import UV.FeynmanTime
import UV.Frullani

/-! The common scalar subtraction, its positive proper-time representation,
the compact-uniform logarithmic zero-depth limit and the actual endpoint
slope. Source: thm:OQED-subtracted-zero-depth. The separate unsubtracted
finite-part assertion is proved in ScalarFinitePart. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace UV

def scalarProperSubtraction (m w : ℝ) (p : ScalarTwoTime) : ℝ :=
  scalarProperDensity m p * (1 - Real.exp (-scalarProperLambda p * w))

@[measurability, fun_prop] theorem scalarProperSubtraction_measurable (m w : ℝ) :
    Measurable (scalarProperSubtraction m w) := by
  unfold scalarProperSubtraction
  fun_prop

theorem scalarSubtractedBubble_proper {a M m : ℝ} (ha : 0 < a) (hm : 0 < m)
    (P : ScalarMomentum) :
    scalarSubtractedBubble a M m P =
      ∫ p, scalarProperSubtraction m (‖P‖ ^ 2) p ∂scalarProperBase (oqedHeatMeasure a M) := by
  letI := oqedScalarLaplaceMeasure_finite (M := M) ha hm
  have he : Integrable (fun ell : ℝ => Real.exp (-ell * ‖P‖ ^ 2))
      (oqedScalarLaplaceMeasure a M m) := by
    apply (integrable_const (μ := oqedScalarLaplaceMeasure a M m) (1 : ℝ)).mono'
      (by fun_prop)
    filter_upwards [oqedScalarLaplaceMeasure_positive ha m] with ell hell
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖P‖])
  unfold scalarSubtractedBubble
  rw [scalarBubble_positive_laplace ha hm 0, scalarBubble_positive_laplace ha hm P]
  simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, Real.exp_zero]
  rw [← integral_sub (integrable_const (1 : ℝ)) he]
  exact scalarLaplaceMeasure_integral (oqedHeatMeasure a M) m (by fun_prop)

theorem scalarProperSubtraction_nonneg {m w : ℝ} {p : ScalarTwoTime}
    (hw : 0 ≤ w) (h₁ : 0 < scalarProperWidth p.1) (h₂ : 0 < scalarProperWidth p.2) :
    0 ≤ scalarProperSubtraction m w p := by
  apply mul_nonneg (scalarProperDensity_nonneg m p)
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr
    (by nlinarith [mul_nonneg (scalarProperLambda_pos h₁ h₂).le hw]))

theorem scalarProperSubtraction_upper {m w : ℝ} {p : ScalarTwoTime}
    (hw : 0 ≤ w) (hτ₁ : 0 ≤ p.1.1) (hα₁ : 0 < p.1.2)
    (hτ₂ : 0 ≤ p.2.1) (hα₂ : 0 < p.2.2) :
    scalarProperSubtraction m w p ≤
      (w / (64 * Real.pi ^ 2)) *
        (Real.exp (-(m ^ 2) * (p.1.2 + p.2.2)) / (p.1.2 + p.2.2)) := by
  let W := scalarProperWidth p.1 + scalarProperWidth p.2
  let S := p.1.2 + p.2.2
  have hS : 0 < S := add_pos hα₁ hα₂
  have hSW : S ≤ W := by dsimp [S, W, scalarProperWidth]; linarith
  have hW : 0 < W := hS.trans_le hSW
  have hlin : 1 - Real.exp (-scalarProperLambda p * w) ≤ scalarProperLambda p * w := by
    linarith [Real.add_one_le_exp (-scalarProperLambda p * w)]
  have hlam : scalarProperLambda p ≤ W / 4 := scalarProperLambda_upper hW
  calc
    scalarProperSubtraction m w p ≤ scalarProperDensity m p * (W / 4 * w) :=
      mul_le_mul_of_nonneg_left (hlin.trans (mul_le_mul_of_nonneg_right hlam hw))
        (scalarProperDensity_nonneg m p)
    _ = w / (64 * Real.pi ^ 2) * (Real.exp (-(m ^ 2) * S) / W) := by
      dsimp [scalarProperDensity, W, S]
      field_simp
      ring
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (Real.exp_pos _).le hS hSW) (by positivity)

def scalarHeatTilt (a M : ℝ) (p : ScalarTwoTime) : ℝ :=
  Real.exp (2 * (a * M) - (a * M) ^ 2 * (p.1.1 + p.2.1))

def scalarLineScale (a : ℝ) (t : ScalarLineTime) : ScalarLineTime := (a ^ 2 * t.1, t.2)

def scalarPairScale (a : ℝ) (p : ScalarTwoTime) : ScalarTwoTime :=
  (scalarLineScale a p.1, scalarLineScale a p.2)

@[measurability, fun_prop] theorem scalarHeatTilt_measurable (a M : ℝ) :
    Measurable (scalarHeatTilt a M) := by unfold scalarHeatTilt; fun_prop

@[measurability, fun_prop] theorem scalarLineScale_measurable (a : ℝ) :
    Measurable (scalarLineScale a) := by unfold scalarLineScale; fun_prop

@[measurability, fun_prop] theorem scalarPairScale_measurable (a : ℝ) :
    Measurable (scalarPairScale a) := by unfold scalarPairScale; fun_prop

theorem oqedMeasure_fixed_tilt (μ : ℝ) :
    oqedMeasure μ = (oqedMeasure 0).withDensity
      (fun t => ENNReal.ofReal (Real.exp (μ - μ ^ 2 * t))) := by
  unfold oqedMeasure
  rw [← withDensity_mul _ (oqedDensity_measurable 0).ennreal_ofReal (by fun_prop)]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (oqedDensity_nonneg 0 t ht.le)]
  congr 1
  have h := oqedDensity_exponential_endpoint μ t
  have he : Real.exp (μ - μ ^ 2 * t) = Real.exp μ / Real.exp (μ ^ 2 * t) := Real.exp_sub _ _
  rw [he]
  have hn := ne_of_gt (Real.exp_pos (μ ^ 2 * t))
  field_simp
  nlinarith [h]

theorem scalarProperBase_fixed_tilt (μ : ℝ) :
    scalarProperBase (oqedMeasure μ) = (scalarProperBase (oqedMeasure 0)).withDensity
      (fun p => ENNReal.ofReal (Real.exp (2 * μ - μ ^ 2 * (p.1.1 + p.2.1)))) := by
  rw [oqedMeasure_fixed_tilt]
  unfold scalarProperBase scalarProperLineBase
  simp_rw [prod_withDensity_left (by fun_prop :
    Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (μ - μ ^ 2 * t))))]
  rw [prod_withDensity (by fun_prop) (by fun_prop)]
  apply withDensity_congr_ae
  filter_upwards with p
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

theorem scalarProperBase_scale (a : ℝ) (ρ : Measure ℝ) [IsFiniteMeasure ρ] :
    scalarProperBase (Measure.map (fun t : ℝ => a ^ 2 * t) ρ) =
      Measure.map (scalarPairScale a) (scalarProperBase ρ) := by
  have hline : scalarProperLineBase (Measure.map (fun t : ℝ => a ^ 2 * t) ρ) =
      Measure.map (scalarLineScale a) (scalarProperLineBase ρ) := by
    unfold scalarProperLineBase
    conv_lhs => rhs; rw [← Measure.map_id (μ := volume.restrict (Ioi 0))]
    exact Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)
  unfold scalarProperBase
  rw [hline]
  exact Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)

theorem scalarProperBase_heat_fixed (a M : ℝ) :
    scalarProperBase (oqedHeatMeasure a M) =
      Measure.map (scalarPairScale a) ((scalarProperBase (oqedMeasure 0)).withDensity
        (fun p => ENNReal.ofReal (scalarHeatTilt a M p))) := by
  rw [oqedHeatMeasure, scalarProperBase_scale, scalarProperBase_fixed_tilt]
  rfl

theorem scalarSubtractedBubble_fixed {a M m : ℝ} (ha : 0 < a) (hm : 0 < m)
    (P : ScalarMomentum) :
    scalarSubtractedBubble a M m P =
      ∫ p, scalarHeatTilt a M p *
        scalarProperSubtraction m (‖P‖ ^ 2) (scalarPairScale a p)
        ∂scalarProperBase (oqedMeasure 0) := by
  rw [scalarSubtractedBubble_proper ha hm, scalarProperBase_heat_fixed,
    integral_map (by fun_prop) (by fun_prop),
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, scalarHeatTilt]

def scalarAlphaPair (p : ScalarTwoTime) : ℝ × ℝ := (p.1.2, p.2.2)

theorem scalarProperBase_alpha_marginal (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    Measure.map scalarAlphaPair (scalarProperBase ρ) =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))) := by
  unfold scalarAlphaPair scalarProperBase scalarProperLineBase
  rw [show (fun p : (ℝ × ℝ) × ℝ × ℝ => (p.1.2, p.2.2)) = Prod.map Prod.snd Prod.snd from rfl,
    ← Measure.map_prod_map _ _ measurable_snd measurable_snd]
  simp only [Measure.map_snd_prod, measure_univ, one_smul]

def scalarDepthIntegrand (a M m w : ℝ) (p : ScalarTwoTime) : ℝ :=
  scalarHeatTilt a M p * scalarProperSubtraction m w (scalarPairScale a p)

def scalarDepthExtension (a M m w : ℝ) : ℝ :=
  ∫ p, scalarDepthIntegrand a M m w p ∂scalarProperBase (oqedMeasure 0)

@[measurability, fun_prop] theorem scalarDepthIntegrand_measurable (a M m w : ℝ) :
    Measurable (scalarDepthIntegrand a M m w) := by
  unfold scalarDepthIntegrand
  fun_prop

theorem scalarDepthExtension_eq_subtraction {a M m : ℝ} (ha : 0 < a) (hm : 0 < m)
    (P : ScalarMomentum) :
    scalarDepthExtension a M m (‖P‖ ^ 2) = scalarSubtractedBubble a M m P :=
  (scalarSubtractedBubble_fixed ha hm P).symm

theorem scalarProperBase_zero_positive :
    ∀ᵐ p ∂scalarProperBase (oqedMeasure 0),
      (0 < p.1.1 ∧ 0 < p.1.2) ∧ (0 < p.2.1 ∧ 0 < p.2.2) := by
  apply scalarProperBase_positive
  · exact measure_mono_null (Iio_subset_Iic_self) (oqedMeasure_nonnegative_support 0)
  · exact oqedMeasure_no_atom 0 0

theorem scalarDepthIntegrand_nonneg {a M m w : ℝ} {p : ScalarTwoTime}
    (hw : 0 ≤ w) (hp : (0 < p.1.1 ∧ 0 < p.1.2) ∧ (0 < p.2.1 ∧ 0 < p.2.2)) :
    0 ≤ scalarDepthIntegrand a M m w p := by
  have ht1 := hp.1.1
  have ha1 := hp.1.2
  have ht2 := hp.2.1
  have ha2 := hp.2.2
  apply mul_nonneg (Real.exp_pos _).le
  apply scalarProperSubtraction_nonneg hw
  · change 0 < a ^ 2 * p.1.1 + p.1.2
    positivity
  · change 0 < a ^ 2 * p.2.1 + p.2.2
    positivity

abbrev ScalarDepthParameters := ℝ × ℝ × ℝ × ℝ

def scalarDepthBox (Mmax mmin mmax Wmax : ℝ) : Set ScalarDepthParameters :=
  (Icc 0 1) ×ˢ (Icc 0 Mmax) ×ˢ (Icc mmin mmax) ×ˢ (Icc 0 Wmax)

theorem scalarDepthBox_compact (Mmax mmin mmax Wmax : ℝ) :
    IsCompact (scalarDepthBox Mmax mmin mmax Wmax) :=
  isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))

theorem scalarDepthIntegrand_continuous {p : ScalarTwoTime}
    (hp : (0 < p.1.1 ∧ 0 < p.1.2) ∧ (0 < p.2.1 ∧ 0 < p.2.2)) :
    Continuous (fun z : ScalarDepthParameters => scalarDepthIntegrand z.1 z.2.1 z.2.2.1 z.2.2.2 p) := by
  have ht1 := hp.1.1
  have ha1 := hp.1.2
  have ht2 := hp.2.1
  have ha2 := hp.2.2
  have hd (z : ScalarDepthParameters) :
      (z.1 ^ 2 * p.1.1 + p.1.2) + (z.1 ^ 2 * p.2.1 + p.2.2) ≠ 0 := by
    apply ne_of_gt
    positivity
  unfold scalarDepthIntegrand scalarHeatTilt scalarProperSubtraction scalarProperDensity
    scalarProperLambda scalarProperWidth scalarPairScale scalarLineScale
  dsimp only
  fun_prop (disch := aesop)

theorem scalarDepthIntegrand_box_bound {Mmax mmin mmax Wmax : ℝ}
    (hmmin : 0 < mmin) {z : ScalarDepthParameters}
    (hz : z ∈ scalarDepthBox Mmax mmin mmax Wmax) {p : ScalarTwoTime}
    (hp : (0 < p.1.1 ∧ 0 < p.1.2) ∧ (0 < p.2.1 ∧ 0 < p.2.2)) :
    ‖scalarDepthIntegrand z.1 z.2.1 z.2.2.1 z.2.2.2 p‖ ≤
      (Real.exp (2 * Mmax) * (Wmax / (64 * Real.pi ^ 2))) *
        (Real.exp (-(mmin ^ 2) * (p.1.2 + p.2.2)) / (p.1.2 + p.2.2)) := by
  have ht1 := hp.1.1
  have ha1 := hp.1.2
  have ht2 := hp.2.1
  have ha2 := hp.2.2
  obtain ⟨ha, hM, hm, hw⟩ := hz
  have hW : 0 ≤ Wmax := hw.1.trans hw.2
  have hS : 0 < p.1.2 + p.2.2 := add_pos hp.1.2 hp.2.2
  have htilt : scalarHeatTilt z.1 z.2.1 p ≤ Real.exp (2 * Mmax) := by
    apply Real.exp_le_exp.mpr
    have haM : z.1 * z.2.1 ≤ Mmax :=
      (mul_le_mul_of_nonneg_right ha.2 hM.1).trans (by simpa using hM.2)
    have hs : 0 ≤ (z.1 * z.2.1) ^ 2 * (p.1.1 + p.2.1) := by positivity
    linarith
  have hsub := scalarProperSubtraction_upper (m := z.2.2.1) hw.1
    (p := scalarPairScale z.1 p) (mul_nonneg (sq_nonneg _) hp.1.1.le) hp.1.2
    (mul_nonneg (sq_nonneg _) hp.2.1.le) hp.2.2
  change scalarProperSubtraction z.2.2.1 z.2.2.2 (scalarPairScale z.1 p) ≤
    z.2.2.2 / (64 * Real.pi ^ 2) *
      (Real.exp (-(z.2.2.1 ^ 2) * (p.1.2 + p.2.2)) / (p.1.2 + p.2.2)) at hsub
  have hexp : Real.exp (-(z.2.2.1 ^ 2) * (p.1.2 + p.2.2)) ≤
      Real.exp (-(mmin ^ 2) * (p.1.2 + p.2.2)) := by
    apply Real.exp_le_exp.mpr
    have hsquares := pow_le_pow_left₀ hmmin.le hm.1 2
    nlinarith
  rw [Real.norm_of_nonneg (scalarDepthIntegrand_nonneg hw.1 hp)]
  calc
    _ ≤ Real.exp (2 * Mmax) *
        (z.2.2.2 / (64 * Real.pi ^ 2) *
          (Real.exp (-(z.2.2.1 ^ 2) * (p.1.2 + p.2.2)) / (p.1.2 + p.2.2))) :=
      mul_le_mul htilt hsub (scalarProperSubtraction_nonneg hw.1 (by
        change 0 < z.1 ^ 2 * p.1.1 + p.1.2; positivity) (by
        change 0 < z.1 ^ 2 * p.2.1 + p.2.2; positivity)) (Real.exp_pos _).le
    _ ≤ _ := by
      have hc : z.2.2.2 / (64 * Real.pi ^ 2) ≤ Wmax / (64 * Real.pi ^ 2) :=
        div_le_div_of_nonneg_right hw.2 (by positivity)
      have he : Real.exp (-(z.2.2.1 ^ 2) * (p.1.2 + p.2.2)) / (p.1.2 + p.2.2) ≤
          Real.exp (-(mmin ^ 2) * (p.1.2 + p.2.2)) / (p.1.2 + p.2.2) :=
        div_le_div_of_nonneg_right hexp hS.le
      calc
        _ ≤ Real.exp (2 * Mmax) *
            (Wmax / (64 * Real.pi ^ 2) *
              (Real.exp (-(mmin ^ 2) * (p.1.2 + p.2.2)) / (p.1.2 + p.2.2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hc he (by positivity) (by positivity))
            (Real.exp_pos _).le
        _ = _ := by ring

theorem scalarProperBase_envelope_integrable (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {m : ℝ} (hm : 0 < m) :
    Integrable (fun p : ScalarTwoTime => feynmanTimeEnvelope m (scalarAlphaPair p))
      (scalarProperBase ρ) := by
  apply (integrable_map_measure (feynman_time_envelope_measurable m).aestronglyMeasurable
    (by unfold scalarAlphaPair; fun_prop)).mp
  rw [scalarProperBase_alpha_marginal]
  exact feynman_time_envelope_integrable hm

theorem scalarProperBase_envelope_integral (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {m : ℝ} (hm : 0 < m) :
    (∫ p : ScalarTwoTime, feynmanTimeEnvelope m (scalarAlphaPair p)
      ∂scalarProperBase ρ) = 1 / m ^ 2 := by
  rw [← integral_map (by unfold scalarAlphaPair; fun_prop)
    (feynman_time_envelope_measurable m).aestronglyMeasurable,
    scalarProperBase_alpha_marginal]
  exact feynman_time_envelope_integral hm

theorem scalarDepthExtension_continuousOn {Mmax mmin mmax Wmax : ℝ} (hmmin : 0 < mmin) :
    ContinuousOn (fun z : ScalarDepthParameters => scalarDepthExtension z.1 z.2.1 z.2.2.1 z.2.2.2)
      (scalarDepthBox Mmax mmin mmax Wmax) := by
  letI := oqedMeasure_zero_probability
  apply continuousOn_of_dominated
    (bound := fun p : ScalarTwoTime =>
      (Real.exp (2 * Mmax) * (Wmax / (64 * Real.pi ^ 2))) *
        feynmanTimeEnvelope mmin (scalarAlphaPair p))
  · intro z _
    exact (scalarDepthIntegrand_measurable _ _ _ _).aestronglyMeasurable
  · intro z hz
    filter_upwards [scalarProperBase_zero_positive] with p hp
    exact scalarDepthIntegrand_box_bound hmmin hz hp
  · exact (scalarProperBase_envelope_integrable (oqedMeasure 0) hmmin).const_mul _
  · filter_upwards [scalarProperBase_zero_positive] with p hp
    exact (scalarDepthIntegrand_continuous hp).continuousOn

/-- A single modulus controls the zero-depth limit for all parameters in the
source's compact rectangular ranges. -/
theorem scalarDepthExtension_uniform_zero {Mmax mmin mmax Wmax : ℝ} (hmmin : 0 < mmin)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a ∈ Icc (0 : ℝ) 1, a < δ →
      ∀ M ∈ Icc (0 : ℝ) Mmax, ∀ m ∈ Icc mmin mmax, ∀ w ∈ Icc (0 : ℝ) Wmax,
        |scalarDepthExtension a M m w - scalarDepthExtension 0 M m w| < ε := by
  have hu := (scalarDepthBox_compact Mmax mmin mmax Wmax).uniformContinuousOn_of_continuous
    (scalarDepthExtension_continuousOn hmmin)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨δ, hδ, fun a ha had M hM m hm w hw => ?_⟩
  have hd : dist (a, M, m, w) (0, M, m, w) < δ := by
    simpa only [Prod.dist_eq, dist_self, max_self, Real.dist_eq, sub_zero,
      abs_of_nonneg ha.1, max_eq_left ha.1] using had
  exact hmod (a, M, m, w) ⟨ha, hM, hm, hw⟩ (0, M, m, w)
    ⟨⟨le_rfl, zero_le_one⟩, hM, hm, hw⟩ hd

theorem scalarSubtractedBubble_uniform_zero {Mmax mmin mmax Wmax : ℝ} (hmmin : 0 < mmin)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a ∈ Ioc (0 : ℝ) 1, a < δ →
      ∀ M ∈ Icc (0 : ℝ) Mmax, ∀ m ∈ Icc mmin mmax,
      ∀ P : ScalarMomentum, ‖P‖ ^ 2 ≤ Wmax →
        |scalarSubtractedBubble a M m P - scalarDepthExtension 0 M m (‖P‖ ^ 2)| < ε := by
  obtain ⟨δ, hδ, hmod⟩ := scalarDepthExtension_uniform_zero (Mmax := Mmax)
    (mmax := mmax) (Wmax := Wmax) hmmin hε
  refine ⟨δ, hδ, fun a ha had M hM m hm P hP => ?_⟩
  have hh := hmod a ⟨ha.1.le, ha.2⟩ had M hM m hm (‖P‖ ^ 2) ⟨sq_nonneg _, hP⟩
  rwa [scalarDepthExtension_eq_subtraction ha.1 (hmmin.trans_le hm.1)] at hh

theorem scalarSubtractedBubble_tendsto_zero {M m : ℝ} (hM : 0 ≤ M) (hm : 0 < m)
    (P : ScalarMomentum) :
    Tendsto (fun a : ℝ => scalarSubtractedBubble a M m P) (𝓝[>] 0)
      (𝓝 (scalarDepthExtension 0 M m (‖P‖ ^ 2))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := scalarSubtractedBubble_uniform_zero
    (Mmax := M) (mmin := m) (mmax := m) (Wmax := ‖P‖ ^ 2) hm hε
  have hn : ∀ᶠ a : ℝ in 𝓝[>] 0, a ∈ Ioc (0 : ℝ) 1 ∧ a < δ := by
    filter_upwards [self_mem_nhdsWithin,
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0))
        (Iio_mem_nhds (show (0 : ℝ) < min 1 δ from lt_min zero_lt_one hδ))] with a ha hb
    exact ⟨⟨ha, (lt_min_iff.mp hb).1.le⟩, (lt_min_iff.mp hb).2⟩
  filter_upwards [hn] with a ha
  exact hmod a ha.1 ha.2 M ⟨hM, le_rfl⟩ m ⟨le_rfl, le_rfl⟩ P le_rfl

theorem scalarSubtractedBubble_uniform_bound {a M m : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M) (hm : 0 < m) (P : ScalarMomentum) :
    0 ≤ scalarSubtractedBubble a M m P ∧
      scalarSubtractedBubble a M m P ≤ ‖P‖ ^ 2 / (64 * Real.pi ^ 2 * m ^ 2) := by
  refine ⟨scalarSubtractedBubble_nonneg ha hM hm P, ?_⟩
  let ρ := oqedHeatMeasure a M
  letI : IsProbabilityMeasure ρ := oqedHeatMeasure_probability ha.le hM
  let K := ‖P‖ ^ 2 / (64 * Real.pi ^ 2)
  have hbound : ∀ᵐ p ∂scalarProperBase ρ,
      ‖scalarProperSubtraction m (‖P‖ ^ 2) p‖ ≤ K * feynmanTimeEnvelope m (scalarAlphaPair p) := by
    filter_upwards [scalarProperBase_positive ρ (oqedHeatMeasure_no_negative ha M)
      (oqedHeatMeasure_no_atom_zero ha M)] with p hp
    rw [Real.norm_of_nonneg (scalarProperSubtraction_nonneg (sq_nonneg _) (by
      unfold scalarProperWidth; linarith [hp.1.1, hp.1.2]) (by
      unfold scalarProperWidth; linarith [hp.2.1, hp.2.2]))]
    exact scalarProperSubtraction_upper (sq_nonneg _) hp.1.1.le hp.1.2 hp.2.1.le hp.2.2
  have henv := (scalarProperBase_envelope_integrable ρ hm).const_mul K
  have hi : Integrable (scalarProperSubtraction m (‖P‖ ^ 2)) (scalarProperBase ρ) :=
    henv.mono' (scalarProperSubtraction_measurable _ _).aestronglyMeasurable hbound
  rw [scalarSubtractedBubble_proper ha hm]
  calc
    _ ≤ ∫ p, K * feynmanTimeEnvelope m (scalarAlphaPair p) ∂scalarProperBase ρ :=
      integral_mono_ae hi henv (hbound.mono fun p hp => (le_abs_self _).trans hp)
    _ = _ := by
      rw [integral_const_mul, scalarProperBase_envelope_integral ρ hm]
      dsimp [K]
      ring

def scalarZeroSubtraction (m w : ℝ) (t : ℝ × ℝ) : ℝ :=
  scalarProperSubtraction m w ((0, t.1), (0, t.2))

@[measurability, fun_prop] theorem scalarZeroSubtraction_measurable (m w : ℝ) :
    Measurable (scalarZeroSubtraction m w) := by
  unfold scalarZeroSubtraction
  fun_prop

theorem scalarZeroSubtraction_nonneg {m w α β : ℝ} (hw : 0 ≤ w) (hα : 0 < α) (hβ : 0 < β) :
    0 ≤ scalarZeroSubtraction m w (α, β) := by
  apply scalarProperSubtraction_nonneg hw <;> simpa [scalarProperWidth]

theorem scalarZeroSubtraction_integrable {m w : ℝ} (hm : 0 < m) (hw : 0 ≤ w) :
    Integrable (scalarZeroSubtraction m w)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  apply ((feynman_time_envelope_integrable hm).const_mul (w / (64 * Real.pi ^ 2))).mono'
    (scalarZeroSubtraction_measurable _ _).aestronglyMeasurable
  filter_upwards [(Measure.quasiMeasurePreserving_fst).ae (ae_restrict_mem measurableSet_Ioi),
    (Measure.quasiMeasurePreserving_snd).ae (ae_restrict_mem measurableSet_Ioi)] with t ht₁ ht₂
  rw [Real.norm_of_nonneg (scalarZeroSubtraction_nonneg hw ht₁ ht₂)]
  exact scalarProperSubtraction_upper hw le_rfl ht₁ le_rfl ht₂

theorem scalarDepthExtension_zero_proper (M m w : ℝ) :
    scalarDepthExtension 0 M m w =
      ∫ t, scalarZeroSubtraction m w t
        ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))) := by
  letI := oqedMeasure_zero_probability
  unfold scalarDepthExtension
  have he : (fun p : ScalarTwoTime => scalarDepthIntegrand 0 M m w p) =
      (fun p => scalarZeroSubtraction m w (scalarAlphaPair p)) := by
    funext p
    simp [scalarDepthIntegrand, scalarHeatTilt, scalarPairScale, scalarLineScale,
      scalarZeroSubtraction, scalarAlphaPair]
  rw [he, ← integral_map (by unfold scalarAlphaPair; fun_prop)
    (scalarZeroSubtraction_measurable m w).aestronglyMeasurable,
    scalarProperBase_alpha_marginal]

theorem scalarZeroSubtraction_rescaled (m w : ℝ) {S x : ℝ} (hS : 0 < S) :
    S * scalarZeroSubtraction m w (S * x, S * (1 - x)) =
      (1 / (16 * Real.pi ^ 2)) * frullaniIntegrand (m ^ 2) (x * (1 - x) * w) S := by
  have hsum : S * x + S * (1 - x) = S := by ring
  have hlam : (S * x * (S * (1 - x)) / S) * w = (x * (1 - x) * w) * S := by
    field_simp
  unfold scalarZeroSubtraction scalarProperSubtraction scalarProperDensity
    scalarProperLambda scalarProperWidth frullaniIntegrand
  dsimp only
  simp only [zero_add, hsum]
  rw [show -(S * x * (S * (1 - x)) / S) * w = -(x * (1 - x) * w) * S by
    nlinarith [hlam]]
  field_simp

def scalarFeynmanSubtraction (m w : ℝ) : ℝ :=
  (1 / (16 * Real.pi ^ 2)) *
    ∫ x in Ioo (0 : ℝ) 1, Real.log (1 + x * (1 - x) * w / m ^ 2)

theorem scalarFeynmanSubtraction_interval (m w : ℝ) :
    scalarFeynmanSubtraction m w = (1 / (16 * Real.pi ^ 2)) *
      ∫ x in (0 : ℝ)..1, Real.log (1 + x * (1 - x) * w / m ^ 2) := by
  rw [scalarFeynmanSubtraction, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]

theorem scalarDepthExtension_zero_log {m w : ℝ} (hm : 0 < m) (hw : 0 ≤ w) (M : ℝ) :
    scalarDepthExtension 0 M m w = scalarFeynmanSubtraction m w := by
  rw [scalarDepthExtension_zero_proper, positive_feynman_time_real _
    (scalarZeroSubtraction_measurable m w) (fun _ hα _ hβ => scalarZeroSubtraction_nonneg hw hα hβ)]
  have he : (fun p : ℝ × ℝ => p.1 * scalarZeroSubtraction m w (p.1 * p.2, p.1 * (1 - p.2)))
      =ᵐ[(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1))]
      (fun p => (1 / (16 * Real.pi ^ 2)) *
        frullaniIntegrand (m ^ 2) (p.2 * (1 - p.2) * w) p.1) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst).ae (ae_restrict_mem measurableSet_Ioi)] with p hp
    exact scalarZeroSubtraction_rescaled m w hp
  have hi := (positive_feynman_time_integrable_iff _ (scalarZeroSubtraction_measurable m w)).mp
    (scalarZeroSubtraction_integrable hm hw)
  rw [integral_prod_symm _ hi]
  unfold scalarFeynmanSubtraction
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hc : 0 ≤ x * (1 - x) * w := mul_nonneg (mul_nonneg hx.1.le (by linarith [hx.2])) hw
  have he' : (fun S : ℝ => S * scalarZeroSubtraction m w (S * x, S * (1 - x))) =ᵐ[
      volume.restrict (Ioi (0 : ℝ))]
      (fun S => (1 / (16 * Real.pi ^ 2)) * frullaniIntegrand (m ^ 2) (x * (1 - x) * w) S) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with S hS
    exact scalarZeroSubtraction_rescaled m w hS
  rw [integral_congr_ae he', integral_const_mul, frullani_integral (sq_pos_of_pos hm) hc]

/-- The literal bubble, with the common subtraction formed at positive
depth, has the logarithmic Feynman-parameter limit. -/
theorem scalarSubtractedBubble_zero_depth {M m : ℝ} (hM : 0 ≤ M) (hm : 0 < m)
    (P : ScalarMomentum) :
    Tendsto (fun a : ℝ => scalarSubtractedBubble a M m P) (𝓝[>] 0)
      (𝓝 (scalarFeynmanSubtraction m (‖P‖ ^ 2))) := by
  rw [← scalarDepthExtension_zero_log hm (sq_nonneg _) M]
  exact scalarSubtractedBubble_tendsto_zero hM hm P

theorem scalarSubtractedBubble_uniform_zero_depth {Mmax mmin mmax Wmax : ℝ}
    (hmmin : 0 < mmin) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a ∈ Ioc (0 : ℝ) 1, a < δ →
      ∀ M ∈ Icc (0 : ℝ) Mmax, ∀ m ∈ Icc mmin mmax,
      ∀ P : ScalarMomentum, ‖P‖ ^ 2 ≤ Wmax →
        |scalarSubtractedBubble a M m P - scalarFeynmanSubtraction m (‖P‖ ^ 2)| < ε := by
  obtain ⟨δ, hδ, hmod⟩ := scalarSubtractedBubble_uniform_zero (Mmax := Mmax)
    (mmax := mmax) (Wmax := Wmax) hmmin hε
  refine ⟨δ, hδ, fun a ha had M hM m hm P hP => ?_⟩
  have hh := hmod a ha had M hM m hm P hP
  rwa [scalarDepthExtension_zero_log (hmmin.trans_le hm.1) (sq_nonneg _) M] at hh

def scalarProperFirstMoment (m : ℝ) (p : ScalarTwoTime) : ℝ :=
  scalarProperDensity m p * scalarProperLambda p

@[measurability, fun_prop] theorem scalarProperFirstMoment_measurable (m : ℝ) :
    Measurable (scalarProperFirstMoment m) := by unfold scalarProperFirstMoment; fun_prop

theorem scalarProperFirstMoment_nonneg {m : ℝ} {p : ScalarTwoTime}
    (h₁ : 0 < scalarProperWidth p.1) (h₂ : 0 < scalarProperWidth p.2) :
    0 ≤ scalarProperFirstMoment m p :=
  mul_nonneg (scalarProperDensity_nonneg _ _) (scalarProperLambda_pos h₁ h₂).le

theorem scalarProperFirstMoment_upper {m : ℝ} {p : ScalarTwoTime}
    (hτ₁ : 0 ≤ p.1.1) (hα₁ : 0 < p.1.2) (hτ₂ : 0 ≤ p.2.1) (hα₂ : 0 < p.2.2) :
    scalarProperFirstMoment m p ≤
      (1 / (64 * Real.pi ^ 2)) * feynmanTimeEnvelope m (scalarAlphaPair p) := by
  let W := scalarProperWidth p.1 + scalarProperWidth p.2
  let S := p.1.2 + p.2.2
  have hS : 0 < S := add_pos hα₁ hα₂
  have hSW : S ≤ W := by dsimp [S, W, scalarProperWidth]; linarith
  have hW : 0 < W := hS.trans_le hSW
  calc
    scalarProperFirstMoment m p ≤ scalarProperDensity m p * (W / 4) :=
      mul_le_mul_of_nonneg_left (scalarProperLambda_upper hW) (scalarProperDensity_nonneg m p)
    _ = (1 / (64 * Real.pi ^ 2)) * (Real.exp (-(m ^ 2) * S) / W) := by
      dsimp [scalarProperDensity, W, S]
      field_simp
      ring
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (Real.exp_pos _).le hS hSW) (by positivity)

def scalarDepthFirstIntegrand (a M m : ℝ) (p : ScalarTwoTime) : ℝ :=
  scalarHeatTilt a M p * scalarProperFirstMoment m (scalarPairScale a p)

def scalarDepthSlope (a M m : ℝ) : ℝ :=
  ∫ p, scalarDepthFirstIntegrand a M m p ∂scalarProperBase (oqedMeasure 0)

@[measurability, fun_prop] theorem scalarDepthFirstIntegrand_measurable (a M m : ℝ) :
    Measurable (scalarDepthFirstIntegrand a M m) := by unfold scalarDepthFirstIntegrand; fun_prop

theorem scalarDepthFirstIntegrand_nonneg {a M m : ℝ} {p : ScalarTwoTime}
    (hp : (0 < p.1.1 ∧ 0 < p.1.2) ∧ (0 < p.2.1 ∧ 0 < p.2.2)) :
    0 ≤ scalarDepthFirstIntegrand a M m p := by
  have ht1 := hp.1.1
  have ha1 := hp.1.2
  have ht2 := hp.2.1
  have ha2 := hp.2.2
  apply mul_nonneg (Real.exp_pos _).le
  apply scalarProperFirstMoment_nonneg
  · change 0 < a ^ 2 * p.1.1 + p.1.2
    positivity
  · change 0 < a ^ 2 * p.2.1 + p.2.2
    positivity

theorem scalarDepthFirstIntegrand_bound {a M m : ℝ} {p : ScalarTwoTime}
    (hp : (0 < p.1.1 ∧ 0 < p.1.2) ∧ (0 < p.2.1 ∧ 0 < p.2.2)) :
    ‖scalarDepthFirstIntegrand a M m p‖ ≤
      (Real.exp (2 * a * M) / (64 * Real.pi ^ 2)) * feynmanTimeEnvelope m (scalarAlphaPair p) := by
  rw [Real.norm_of_nonneg (scalarDepthFirstIntegrand_nonneg hp)]
  have hs : 0 ≤ (a * M) ^ 2 * (p.1.1 + p.2.1) :=
    mul_nonneg (sq_nonneg _) (add_nonneg hp.1.1.le hp.2.1.le)
  have ht : scalarHeatTilt a M p ≤ Real.exp (2 * a * M) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hf := scalarProperFirstMoment_upper (m := m) (p := scalarPairScale a p)
    (mul_nonneg (sq_nonneg a) hp.1.1.le) hp.1.2
    (mul_nonneg (sq_nonneg a) hp.2.1.le) hp.2.2
  have hn : 0 ≤ scalarProperFirstMoment m (scalarPairScale a p) := by
    apply scalarProperFirstMoment_nonneg
    · change 0 < a ^ 2 * p.1.1 + p.1.2
      exact add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg a) hp.1.1.le) hp.1.2
    · change 0 < a ^ 2 * p.2.1 + p.2.2
      exact add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg a) hp.2.1.le) hp.2.2
  calc
    _ ≤ Real.exp (2 * a * M) *
        ((1 / (64 * Real.pi ^ 2)) * feynmanTimeEnvelope m (scalarAlphaPair p)) :=
      mul_le_mul ht hf hn (Real.exp_pos _).le
    _ = _ := by simp only [div_eq_mul_inv]; ring

theorem scalarDepthFirstIntegrand_integrable (a M : ℝ) {m : ℝ} (hm : 0 < m) :
    Integrable (scalarDepthFirstIntegrand a M m) (scalarProperBase (oqedMeasure 0)) := by
  letI := oqedMeasure_zero_probability
  apply ((scalarProperBase_envelope_integrable (oqedMeasure 0) hm).const_mul
    (Real.exp (2 * a * M) / (64 * Real.pi ^ 2))).mono'
    (scalarDepthFirstIntegrand_measurable _ _ _).aestronglyMeasurable
  filter_upwards [scalarProperBase_zero_positive] with p hp
  exact scalarDepthFirstIntegrand_bound hp

theorem positiveLaplace_subtraction_boundary_slope (ν : Measure ℝ)
    (hp : ∀ᵐ ell ∂ν, 0 ≤ ell) (hi : Integrable (fun ell : ℝ => ell) ν) :
    HasDerivWithinAt (fun w : ℝ => ∫ ell, (1 - Real.exp (-ell * w)) ∂ν)
      (∫ ell, ell ∂ν) (Ici 0) 0 := by
  apply HasDerivWithinAt.Ici_of_Ioi
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mpr
  have hq : Tendsto (fun w : ℝ => ∫ ell, (1 - Real.exp (-ell * w)) / w ∂ν)
      (𝓝[>] 0) (𝓝 (∫ ell, ell ∂ν)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun ell : ℝ => ell)
    · exact Eventually.of_forall (fun _ => by fun_prop)
    · filter_upwards [self_mem_nhdsWithin] with w hw
      change 0 < w at hw
      filter_upwards [hp] with ell hell
      have hn : 0 ≤ 1 - Real.exp (-ell * w) :=
        sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith))
      rw [Real.norm_of_nonneg (div_nonneg hn hw.le)]
      apply (div_le_iff₀ hw).mpr
      linarith [Real.add_one_le_exp (-ell * w)]
    · exact hi
    · filter_upwards with ell
      have hd : HasDerivAt (fun w : ℝ => 1 - Real.exp (-ell * w)) ell 0 := by
        convert (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
          (((hasDerivAt_id (0 : ℝ)).const_mul (-ell)).exp) using 1
        simp
      simpa only [zero_add, mul_zero, Real.exp_zero, sub_self, sub_zero, smul_eq_mul,
        div_eq_inv_mul] using hd.tendsto_slope_zero_right
  convert hq using 1
  funext w
  simp only [slope_def_field, mul_zero, Real.exp_zero, sub_self, integral_zero, sub_zero]
  exact (integral_div w (fun ell : ℝ => 1 - Real.exp (-ell * w))).symm

theorem scalarProperFirstMoment_heat_integrable {a M m : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M) (hm : 0 < m) :
    Integrable (scalarProperFirstMoment m) (scalarProperBase (oqedHeatMeasure a M)) := by
  letI := oqedHeatMeasure_probability ha.le hM
  apply ((scalarProperBase_envelope_integrable (oqedHeatMeasure a M) hm).const_mul
    (1 / (64 * Real.pi ^ 2))).mono'
    (scalarProperFirstMoment_measurable _).aestronglyMeasurable
  filter_upwards [scalarProperBase_positive (oqedHeatMeasure a M)
    (oqedHeatMeasure_no_negative ha M) (oqedHeatMeasure_no_atom_zero ha M)] with p hp
  rw [Real.norm_of_nonneg (scalarProperFirstMoment_nonneg (by
    unfold scalarProperWidth; linarith [hp.1.1, hp.1.2]) (by
    unfold scalarProperWidth; linarith [hp.2.1, hp.2.2]))]
  exact scalarProperFirstMoment_upper hp.1.1.le hp.1.2 hp.2.1.le hp.2.2

theorem scalarLaplaceMeasure_firstMoment_integrable {a M m : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M) (hm : 0 < m) :
    Integrable (fun ell : ℝ => ell) (oqedScalarLaplaceMeasure a M m) := by
  exact (scalarLaplaceMeasure_integrable_iff (oqedHeatMeasure a M) m measurable_id).mpr
    (scalarProperFirstMoment_heat_integrable ha hM hm)

theorem scalarDepthSlope_eq_laplaceMoment (a M m : ℝ) :
    scalarDepthSlope a M m = ∫ ell, ell ∂oqedScalarLaplaceMeasure a M m := by
  change scalarDepthSlope a M m = ∫ ell, id ell ∂scalarLaplaceMeasure (oqedHeatMeasure a M) m
  rw [scalarLaplaceMeasure_integral (oqedHeatMeasure a M) m measurable_id,
    scalarProperBase_heat_fixed, integral_map (by fun_prop) (by fun_prop),
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [scalarDepthSlope, scalarDepthFirstIntegrand, scalarProperFirstMoment,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, scalarHeatTilt, id_eq]

def scalarInvariantSubtraction (a M m w : ℝ) : ℝ :=
  scalarSubtractedBubble a M m (scalarAxis (Real.sqrt w))

theorem scalarInvariantSubtraction_laplace {a M m w : ℝ}
    (ha : 0 < a) (hm : 0 < m) (hw : 0 ≤ w) :
    scalarInvariantSubtraction a M m w =
      ∫ ell, (1 - Real.exp (-ell * w)) ∂oqedScalarLaplaceMeasure a M m := by
  have hn : ‖scalarAxis (Real.sqrt w)‖ ^ 2 = w := by
    rw [scalarAxis_norm, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hw]
  unfold oqedScalarLaplaceMeasure
  rw [scalarInvariantSubtraction, scalarSubtractedBubble_proper ha hm,
    scalarLaplaceMeasure_integral (oqedHeatMeasure a M) m (by fun_prop), hn]
  rfl

/-- The derivative at the endpoint is the actual right derivative of the
invariant literal bubble, including the massless kernel parameter M=0. -/
theorem scalarInvariantSubtraction_boundary_derivative {a M m : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M) (hm : 0 < m) :
    HasDerivWithinAt (scalarInvariantSubtraction a M m) (scalarDepthSlope a M m) (Ici 0) 0 := by
  rw [scalarDepthSlope_eq_laplaceMoment]
  apply (positiveLaplace_subtraction_boundary_slope (oqedScalarLaplaceMeasure a M m)
    ((oqedScalarLaplaceMeasure_positive ha m).mono fun _ h => h.le)
    (scalarLaplaceMeasure_firstMoment_integrable ha hM hm)).congr
  · intro w hw
    exact scalarInvariantSubtraction_laplace ha hm hw
  · exact scalarInvariantSubtraction_laplace ha hm le_rfl

theorem scalarDepthFirstIntegrand_continuous (M m : ℝ) {p : ScalarTwoTime}
    (hp : (0 < p.1.1 ∧ 0 < p.1.2) ∧ (0 < p.2.1 ∧ 0 < p.2.2)) :
    Continuous (fun a : ℝ => scalarDepthFirstIntegrand a M m p) := by
  have ht1 := hp.1.1
  have ha1 := hp.1.2
  have ht2 := hp.2.1
  have ha2 := hp.2.2
  have hd (a : ℝ) : (a ^ 2 * p.1.1 + p.1.2) + (a ^ 2 * p.2.1 + p.2.2) ≠ 0 := by
    apply ne_of_gt
    positivity
  unfold scalarDepthFirstIntegrand scalarHeatTilt scalarProperFirstMoment scalarProperDensity
    scalarProperLambda scalarProperWidth scalarPairScale scalarLineScale
  dsimp only
  fun_prop (disch := aesop)

theorem scalarDepthSlope_tendsto_zero {M m : ℝ} (hM : 0 ≤ M) (hm : 0 < m) :
    Tendsto (fun a : ℝ => scalarDepthSlope a M m) (𝓝[>] 0) (𝓝 (scalarDepthSlope 0 M m)) := by
  letI := oqedMeasure_zero_probability
  apply tendsto_integral_filter_of_dominated_convergence
    (fun p : ScalarTwoTime =>
      (Real.exp (2 * M) / (64 * Real.pi ^ 2)) * feynmanTimeEnvelope m (scalarAlphaPair p))
  · exact Eventually.of_forall (fun a => (scalarDepthFirstIntegrand_measurable a M m).aestronglyMeasurable)
  · have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, a < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
    filter_upwards [hsmall] with a ha
    filter_upwards [scalarProperBase_zero_positive] with p hp
    have hE : Real.exp (2 * a * M) ≤ Real.exp (2 * M) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    exact (scalarDepthFirstIntegrand_bound hp).trans
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hE (by positivity))
        (div_nonneg (Real.exp_nonneg _) (add_nonneg hp.1.2.le hp.2.2.le)))
  · exact (scalarProperBase_envelope_integrable (oqedMeasure 0) hm).const_mul _
  · filter_upwards [scalarProperBase_zero_positive] with p hp
    exact (scalarDepthFirstIntegrand_continuous M m hp).continuousAt.tendsto.mono_left nhdsWithin_le_nhds

def scalarZeroFirstMoment (m : ℝ) (t : ℝ × ℝ) : ℝ :=
  scalarProperFirstMoment m ((0, t.1), (0, t.2))

@[measurability, fun_prop] theorem scalarZeroFirstMoment_measurable (m : ℝ) :
    Measurable (scalarZeroFirstMoment m) := by unfold scalarZeroFirstMoment; fun_prop

theorem scalarZeroFirstMoment_nonneg {m α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    0 ≤ scalarZeroFirstMoment m (α, β) := by
  apply scalarProperFirstMoment_nonneg <;> simpa [scalarProperWidth]

theorem scalarZeroFirstMoment_rescaled (m : ℝ) {S x : ℝ} (hS : 0 < S) :
    S * scalarZeroFirstMoment m (S * x, S * (1 - x)) =
      (1 / (16 * Real.pi ^ 2)) * (Real.exp (-(m ^ 2) * S) * (x * (1 - x))) := by
  have hsum : S * x + S * (1 - x) = S := by ring
  unfold scalarZeroFirstMoment scalarProperFirstMoment scalarProperDensity
    scalarProperLambda scalarProperWidth
  dsimp only
  simp only [zero_add, hsum]
  field_simp

theorem scalarDepthSlope_zero_proper (M m : ℝ) :
    scalarDepthSlope 0 M m = ∫ t, scalarZeroFirstMoment m t
      ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))) := by
  letI := oqedMeasure_zero_probability
  unfold scalarDepthSlope
  have he : (fun p : ScalarTwoTime => scalarDepthFirstIntegrand 0 M m p) =
      (fun p => scalarZeroFirstMoment m (scalarAlphaPair p)) := by
    funext p
    simp [scalarDepthFirstIntegrand, scalarHeatTilt, scalarPairScale, scalarLineScale,
      scalarZeroFirstMoment, scalarAlphaPair]
  rw [he, ← integral_map (by unfold scalarAlphaPair; fun_prop)
    (scalarZeroFirstMoment_measurable m).aestronglyMeasurable, scalarProperBase_alpha_marginal]

theorem scalarFeynman_parameter_first_moment :
    (∫ x in Ioo (0 : ℝ) 1, x * (1 - x)) = 1 / 6 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have hfun : (fun x : ℝ => x * (1 - x)) = fun x => x - x ^ 2 := by funext; ring
  rw [hfun, intervalIntegral.integral_sub
    ((by fun_prop : Continuous (fun x : ℝ => x)).intervalIntegrable 0 1)
    ((by fun_prop : Continuous (fun x : ℝ => x ^ 2)).intervalIntegrable 0 1)]
  norm_num [integral_id, integral_pow]

theorem scalarDepthSlope_zero {m : ℝ} (hm : 0 < m) (M : ℝ) :
    scalarDepthSlope 0 M m = 1 / (96 * Real.pi ^ 2 * m ^ 2) := by
  rw [scalarDepthSlope_zero_proper, positive_feynman_time_real _
    (scalarZeroFirstMoment_measurable m) (fun _ hα _ hβ => scalarZeroFirstMoment_nonneg hα hβ)]
  have he : (fun p : ℝ × ℝ => p.1 * scalarZeroFirstMoment m (p.1 * p.2, p.1 * (1 - p.2)))
      =ᵐ[(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1))]
      (fun p => (1 / (16 * Real.pi ^ 2)) *
        (Real.exp (-(m ^ 2) * p.1) * (p.2 * (1 - p.2)))) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst).ae (ae_restrict_mem measurableSet_Ioi)] with p hp
    exact scalarZeroFirstMoment_rescaled m hp
  rw [integral_congr_ae he, integral_const_mul,
    integral_prod_mul (fun S : ℝ => Real.exp (-(m ^ 2) * S)) (fun x : ℝ => x * (1 - x)),
    scalarFeynman_parameter_first_moment,
    integral_exp_mul_Ioi (neg_lt_zero.mpr (sq_pos_of_pos hm)) 0]
  simp only [mul_zero, Real.exp_zero]
  ring

/-- The explicit source slope limit is a limit of right derivatives of
the actual radial invariant, with its value at w=0 retained. -/
theorem scalarSubtractedBubble_slope_zero_depth {M m : ℝ} (hM : 0 ≤ M) (hm : 0 < m) :
    Tendsto (fun a : ℝ => derivWithin (scalarInvariantSubtraction a M m) (Ici 0) 0)
      (𝓝[>] 0) (𝓝 (1 / (96 * Real.pi ^ 2 * m ^ 2))) := by
  have ht := scalarDepthSlope_tendsto_zero hM hm
  rw [scalarDepthSlope_zero hm M] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact ((scalarInvariantSubtraction_boundary_derivative ha hM hm).derivWithin
    (uniqueDiffWithinAt_Ici 0)).symm

theorem scalarSubtractedBubble_common_integral {a M m : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M) (hm : 0 < m) (P : ScalarMomentum) :
    Integrable (fun q : ScalarMomentum => scalarCovariance a M m q ^ 2 -
      scalarCovariance a M m q * scalarCovariance a M m (q + P)) ∧
    scalarSubtractedBubble a M m P = (2 * Real.pi) ^ (-4 : ℤ) *
      ∫ q : ScalarMomentum, scalarCovariance a M m q ^ 2 -
        scalarCovariance a M m q * scalarCovariance a M m (q + P) := by
  have h₁ := scalarCovariance_sq_integrable ha hM hm
  have h₂ : Integrable (fun q : ScalarMomentum => scalarCovariance a M m q *
      scalarCovariance a M m (q + P)) := scalarBubbleIntegrand_integrable ha hM hm P
  refine ⟨h₁.sub h₂, ?_⟩
  rw [integral_sub h₁ h₂]
  unfold scalarSubtractedBubble scalarBubble scalarBubbleIntegrand
  simp only [add_zero, ← pow_two]
  ring

theorem scalarSubtractedBubble_centered_square {a M m : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M) (hm : 0 < m) (P : ScalarMomentum) :
    Integrable (fun q : ScalarMomentum =>
      (scalarCovariance a M m (q - (1 / 2 : ℝ) • P) -
        scalarCovariance a M m (q + (1 / 2 : ℝ) • P)) ^ 2) ∧
    scalarSubtractedBubble a M m P = (2 * Real.pi) ^ (-4 : ℤ) / 2 *
      ∫ q : ScalarMomentum, (scalarCovariance a M m (q - (1 / 2 : ℝ) • P) -
        scalarCovariance a M m (q + (1 / 2 : ℝ) • P)) ^ 2 := by
  let C := scalarCovariance a M m
  let h := (1 / 2 : ℝ) • P
  let f := fun q : ScalarMomentum => (C q - C (q + P)) ^ 2
  have h₁ : Integrable (fun q : ScalarMomentum => C q ^ 2) := scalarCovariance_sq_integrable ha hM hm
  have h₂ : Integrable (fun q : ScalarMomentum => C (q + P) ^ 2) :=
    (measurePreserving_add_right volume P).integrable_comp_of_integrable h₁
  have h₃ : Integrable (fun q : ScalarMomentum => C q * C (q + P)) :=
    scalarBubbleIntegrand_integrable ha hM hm P
  have hf : Integrable f := by
    convert (h₁.add h₂).sub (h₃.const_mul 2) using 1
    funext q
    dsimp [f]
    ring
  have hcenter : (fun q : ScalarMomentum => (C (q - h) - C (q + h)) ^ 2) =
      (fun q => f (q + -h)) := by
    funext q
    have he : q + -h + P = q + h := by dsimp [h]; module
    simp only [f, he, sub_eq_add_neg]
  refine ⟨?_, ?_⟩
  · change Integrable (fun q : ScalarMomentum => (C (q - h) - C (q + h)) ^ 2)
    rw [hcenter]
    exact (measurePreserving_add_right volume (-h)).integrable_comp_of_integrable hf
  · rw [scalarBubble_difference_square ha hM hm]
    change (2 * Real.pi) ^ (-4 : ℤ) / 2 * ∫ q, f q =
      (2 * Real.pi) ^ (-4 : ℤ) / 2 * ∫ q, (C (q - h) - C (q + h)) ^ 2
    rw [hcenter, integral_add_right_eq_self f (-h)]

end UV
