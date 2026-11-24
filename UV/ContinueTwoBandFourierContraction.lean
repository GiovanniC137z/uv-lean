import UV.ContinueTwoBandFourierOperator
import UV.ContinueTwoBandFourierSchurTest
import UV.ContinueTwoBandFourierCellMass

/-! The sharp row and column bounds for each composed one-sided slab hop.
The temporal half-line mass is exactly `1/m`. The periodized spatial
Gaussian has unit mass even at nonzero scalar and spatial backgrounds
after the unit Wilson phases are bounded. -/

noncomputable section
open MeasureTheory Set Filter

namespace UV.SectorPlane

private def positiveLag (m : ℝ) : ℝ → ℝ :=
  (Ici 0).indicator (fun u => Real.exp (-m*u))

private theorem lag_nonneg (m u : ℝ) : 0 ≤ positiveLag m u := Set.indicator_nonneg (fun _ _ => Real.exp_nonneg _) _

private theorem lag_integral {m : ℝ} (hm : 0 < m) :
    Integrable (positiveLag m) ∧ (∫ u,positiveLag m u) = 1/m := by
  have hi := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hm) 0
  have he := integral_exp_mul_Ioi (neg_lt_zero.mpr hm) 0
  unfold positiveLag
  rw [integral_indicator measurableSet_Ici,integral_Ici_eq_integral_Ioi]
  exact ⟨((integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hi).integrable_indicator measurableSet_Ici, by simpa using he⟩

private def timeEnvelope (upper : Bool) (m t s : ℝ) : ℝ :=
  positiveLag m (if upper then t-s else s-t)

private theorem time_row {m : ℝ} (hm : 0 < m) (upper : Bool) (t T : ℝ) :
    IntegrableOn (timeEnvelope upper m t) (Icc (-T) T) ∧
      (∫ s in Icc (-T) T, timeEnvelope upper m t s) ≤ 1/m := by
  have he : (∫ s,timeEnvelope upper m t s) = 1/m := by
    cases upper
    · change (∫ s : ℝ,positiveLag m (s-t)) = _
      exact (integral_sub_right_eq_self (positiveLag m) t).trans (lag_integral hm).2
    · change (∫ s : ℝ,positiveLag m (t-s)) = _
      exact (integral_sub_left_eq_self (positiveLag m) volume t).trans (lag_integral hm).2
  have hi : Integrable (timeEnvelope upper m t) := Integrable.of_integral_ne_zero
    (he.trans_ne (one_div_ne_zero hm.ne'))
  exact ⟨hi.integrableOn,(integral_mono_measure Measure.restrict_le_self
    (ae_of_all _ (fun s => (lag_nonneg _ _ : 0 ≤ timeEnvelope upper m t s))) hi).trans_eq he⟩

private def spatialTemporalEnvelope (upper : Bool) (m σ L₁ L₂ L₃ : ℝ) (x y : TwoBandPoint) : ℝ :=
  timeEnvelope upper m x.1 y.1 * twoBandHeatEnvelope σ L₁ L₂ L₃ x.2 y.2

private theorem envelope_swap (upper : Bool) (m σ L₁ L₂ L₃ : ℝ) (x y : TwoBandPoint) :
    spatialTemporalEnvelope upper m σ L₁ L₂ L₃ x y =
      spatialTemporalEnvelope (!upper) m σ L₁ L₂ L₃ y x := by
  unfold spatialTemporalEnvelope
  rw [twoBand_heat_envelope_symm σ L₁ L₂ L₃ x.2 y.2]
  cases upper <;> rfl

private theorem slab_product_measure (T L₁ L₂ L₃ : ℝ) :
    twoBandSlabMeasure T L₁ L₂ L₃ = ((volume : Measure ℝ).restrict (Icc (-T) T)).prod
      ((volume : Measure Spatial).restrict (twoBandTorusCell L₁ L₂ L₃)) := by
  rw [Measure.prod_restrict]
  rfl

private theorem envelope_row {m σ L₁ L₂ L₃ : ℝ} (hm : 0 < m) (hσ : 0 < σ) (h₁ : 0 < L₁)
    (h₂ : 0 < L₂) (h₃ : 0 < L₃) (upper : Bool) (T : ℝ) (x : TwoBandPoint) :
    Integrable (spatialTemporalEnvelope upper m σ L₁ L₂ L₃ x) (twoBandSlabMeasure T L₁ L₂ L₃) ∧
      (∫ y, spatialTemporalEnvelope upper m σ L₁ L₂ L₃ x y ∂twoBandSlabMeasure T L₁ L₂ L₃) ≤ 1/m := by
  have hs := twoBand_heat_envelope_mass hσ h₁ h₂ h₃ x.2
  have hsI : IntegrableOn (twoBandHeatEnvelope σ L₁ L₂ L₃ x.2) (twoBandTorusCell L₁ L₂ L₃) :=
    Integrable.of_integral_ne_zero (hs.trans_ne one_ne_zero)
  obtain ⟨htI,ht⟩ := time_row hm upper x.1 T
  rw [slab_product_measure]
  refine ⟨htI.mul_prod hsI,?_⟩
  unfold spatialTemporalEnvelope
  rw [integral_prod_mul,hs,mul_one]
  exact ht

private theorem physical_envelope (upper : Bool)
    (A : TwoBandPoint → Spatial →L[ℝ] ℝ) (φ : TwoBandPoint → ℝ) (m q g : ℝ)
    {σ L₁ L₂ L₃ : ℝ} (hσ : 0 < σ) (h₁ : 0 < L₁) (h₂ : 0 < L₂) (h₃ : 0 < L₃)
    (x y : TwoBandPoint) :
    ‖twoBandSlabHopKernel upper A φ m q g σ L₁ L₂ L₃ x y‖ ≤ |g| * spatialTemporalEnvelope upper m σ L₁ L₂ L₃ x y := by
  have ht : 0 ≤ timeEnvelope upper m x.1 y.1 := lag_nonneg _ _
  have hE := twoBand_heat_envelope_nonneg σ L₁ L₂ L₃ x.2 y.2
  unfold twoBandSlabHopKernel
  split_ifs
  · have hS : ‖if upper then twoBandPeriodizedHop A q g σ L₁ L₂ L₃ y.1 x.2 y.2
                     else (starRingEnd ℂ) (twoBandPeriodizedHop A q g σ L₁ L₂ L₃ y.1 y.2 x.2)‖
        ≤ |g| * twoBandHeatEnvelope σ L₁ L₂ L₃ x.2 y.2 := by
      cases upper
      · simpa only [Bool.false_eq_true,if_false,Complex.norm_conj,twoBand_heat_envelope_symm σ L₁ L₂ L₃ y.2 x.2] using
          twoBand_periodized_hop_envelope A q g hσ h₁ h₂ h₃ y.1 y.2 x.2
      · exact twoBand_periodized_hop_envelope A q g hσ h₁ h₂ h₃ y.1 x.2 y.2
    unfold twoBandDirectedSlabHop
    rw [norm_mul,norm_mul,twoBand_onsite_transport_unit,mul_one]
    apply (mul_le_mul_of_nonneg_left hS (norm_nonneg _)).trans
    rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    have hT : |(if upper then (if y.1 ≤ x.1 then 1 else 0) else (if x.1 < y.1 then -1 else 0):ℝ)| *
        Real.exp (-m*|x.1-y.1|) ≤ timeEnvelope upper m x.1 y.1 := by
      cases upper <;> by_cases h : y.1 ≤ x.1
      · by_cases e : x.1 = y.1
        · simp [timeEnvelope,positiveLag,e]
        · simp [timeEnvelope,positiveLag,not_lt.mpr h,not_le.mpr (lt_of_le_of_ne h (Ne.symm e))]
      · simp [timeEnvelope,positiveLag,lt_of_not_ge h,abs_of_neg (sub_neg.mpr (lt_of_not_ge h)),
          sub_nonneg.mpr (le_of_lt (lt_of_not_ge h))]
      · simp [timeEnvelope,positiveLag,h,abs_of_nonneg (sub_nonneg.mpr h),sub_nonneg.mpr h]
      · simp [timeEnvelope,positiveLag,h,not_le.mpr (sub_neg.mpr (lt_of_not_ge h))]
    exact (mul_le_mul_of_nonneg_right hT (mul_nonneg (abs_nonneg _) hE)).trans_eq (by unfold spatialTemporalEnvelope; ring)
  · simpa only [norm_zero,spatialTemporalEnvelope] using mul_nonneg (abs_nonneg g) (mul_nonneg ht hE)

/-- At positive mass each individual directed block on the slab has
operator norm at most `|g|/m`, uniformly in the continuous real gauge
backgrounds, the cell periods and the slab length. -/
theorem twoBand_slab_operator_contraction (upper : Bool) (T : ℝ)
    {A : TwoBandPoint → Spatial →L[ℝ] ℝ} (hA : Continuous A)
    {φ : TwoBandPoint → ℝ} (hφ : Continuous φ) {m : ℝ} (hm : 0 < m) (q g : ℝ)
    {σ L₁ L₂ L₃ : ℝ} (hσ : 0 < σ) (h₁ : 0 < L₁) (h₂ : 0 < L₂) (h₃ : 0 < L₃) :
    ‖twoBandSlabOperator upper T hA hφ hm.le q g hσ h₁ h₂ h₃‖ ≤ |g| / m := by
  let μ := twoBandSlabMeasure T L₁ L₂ L₃
  let K := twoBandBoundedSlabHop upper hA hφ hm.le q g hσ h₁ h₂ h₃
  have h (a : Bool) (x : TwoBandPoint) (f : TwoBandPoint → ℝ) (hf : Measurable f)
      (hn : ∀ y, 0 ≤ f y) (hb : ∀ y, f y ≤ |g| * spatialTemporalEnvelope a m σ L₁ L₂ L₃ x y) :
      (∫ y, f y ∂μ) ≤ |g| / m := by
    obtain ⟨hi,he⟩ := envelope_row hm hσ h₁ h₂ h₃ a T x
    have hE := hi.const_mul |g|
    have hI := hE.mono' hf.aestronglyMeasurable (ae_of_all _ (fun y => by simpa only [Real.norm_of_nonneg (hn y)] using hb y))
    apply (integral_mono hI hE hb).trans
    rw [integral_const_mul,div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left he (abs_nonneg _)
  apply SlabKernel.schur_test μ K (by positivity)
  · intro x
    exact h upper x _ (K.measurable.comp (measurable_const.prodMk measurable_id)).norm (fun _ => norm_nonneg _)
      (physical_envelope upper A φ m q g hσ h₁ h₂ h₃ x)
  · intro y
    apply h (!upper) y _ (K.measurable.comp (measurable_id.prodMk measurable_const)).norm (fun _ => norm_nonneg _)
    intro x
    rw [←envelope_swap upper m σ L₁ L₂ L₃ x y]
    exact physical_envelope upper A φ m q g hσ h₁ h₂ h₃ x y

end UV.SectorPlane
