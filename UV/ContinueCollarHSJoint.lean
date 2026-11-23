import UV.ContinueCollarHSIdentity

/-! The operator-basis readout of the shared normal coordinate obeys
the finite joint proper-time bound under the stated positive-kernel
comparison. -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace UV.ContinueCollarHSJoint

open UV.ContinueCollarHSIdentity UV.FurtherBoundaryCollar UV.FurtherBoundaryEnvelope

private theorem extend_short_tip_bound {D : ℝ → ℝ → ℝ} {C k T : ℝ}
    (hC : 0 ≤ C) (hk : 0 < k)
    (hFree : ∀ t ∈ Ioc 0 T, ∀ r ∈ Ioc 0 1, D t r ≤ C * t ^ (-1 / 2 : ℝ))
    (hTip : ∀ t ∈ Ioc 0 T, ∀ r ∈ Ioc 0 1, r < 1 / 4 → r ^ (5 : ℕ) ≤ t →
      D t r ≤ C * t ^ (-1 / 2 : ℝ) * Real.exp (-k / r ^ (3 : ℕ)))
    {t r : ℝ} (ht : t ∈ Ioc 0 T) (hr : r ∈ Ioc 0 1) (hrt : r ^ (5 : ℕ) ≤ t) :
    D t r ≤ (C * Real.exp (64 * k)) * t ^ (-1 / 2 : ℝ) * Real.exp (-k / r ^ (3 : ℕ)) := by
  have hCC : C ≤ C * Real.exp (64 * k) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.one_le_exp_iff.mpr (mul_nonneg (by norm_num : (0 : ℝ) ≤ 64) hk.le)) hC
  by_cases hsmall : r < 1 / 4
  · exact (hTip t ht r hr hsmall hrt).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCC (Real.rpow_nonneg ht.1.le _)) (Real.exp_nonneg _))
  · have hrf : (1 / 4 : ℝ) ≤ r := le_of_not_gt hsmall
    have hpow : (1 / 64 : ℝ) ≤ r ^ (3 : ℕ) := by
      convert pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 / 4 by norm_num) hrf 3 using 1
      norm_num
    have hdiv : k / r ^ (3 : ℕ) ≤ 64 * k :=
      (div_le_iff₀ (pow_pos hr.1 _)).mpr (by nlinarith [mul_le_mul_of_nonneg_left hpow hk.le])
    have harg : 0 ≤ 64 * k + -k / r ^ (3 : ℕ) := by rw [neg_div]; linarith
    calc
      _ ≤ C * t ^ (-1 / 2 : ℝ) := hFree t ht r hr
      _ ≤ C * t ^ (-1 / 2 : ℝ) * Real.exp (64 * k + -k / r ^ (3 : ℕ)) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.mpr harg)
          (mul_nonneg hC (Real.rpow_nonneg ht.1.le _))
      _ = _ := by rw [Real.exp_add]; ring

private def collarDurationMajorant (M c t : ℝ) : ℝ :=
  M * (t ^ (-1 / 2 : ℝ) * Real.exp (-c * t ^ (-3 / 5 : ℝ)))

private theorem shared_trace_duration_integral_ne_top {H : ℝ → ℝ≥0∞} {M c T : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c)
    (h : ∀ t ∈ Ioc 0 T, H t ≤ ENNReal.ofReal (collarDurationMajorant M c t)) :
    (∫⁻ t in Ioc (0 : ℝ) T, ENNReal.ofReal (1 / (2 * Real.pi * t)) * H t) ≠ ⊤ := by
  let G := fun t : ℝ => M / (2 * Real.pi) *
    (t ^ (-(3 / 2) : ℝ) * Real.exp (-c * t ^ (-(3 / 5) : ℝ)))
  have hG : IntegrableOn G (Ioc 0 T) :=
    (stretched_exponential_integrableOn (a := 3 / 5) (T := T) (by norm_num) hc (3 / 2)).const_mul _
  have hGpos : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioc 0 T), 0 ≤ G t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t (ht : t ∈ Ioc 0 T)
    unfold G
    exact mul_nonneg (div_nonneg hM (by positivity))
      (mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.exp_nonneg _))
  have hfin : (∫⁻ t in Ioc (0 : ℝ) T, ENNReal.ofReal (G t)) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hG hGpos]
    exact ENNReal.ofReal_ne_top
  refine ne_top_of_le_ne_top hfin (lintegral_mono_ae ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t (ht : t ∈ Ioc 0 T)
  refine (mul_le_mul_left' (h t ht) (ENNReal.ofReal (1 / (2 * Real.pi * t)))).trans_eq ?_
  have hpos : 0 ≤ 1 / (2 * Real.pi * t) :=
    div_nonneg zero_le_one (mul_nonneg (mul_nonneg zero_le_two Real.pi_pos.le) ht.1.le)
  rw [← ENNReal.ofReal_mul hpos]
  congr 1
  unfold G collarDurationMajorant
  rw [show (-(3 / 2) : ℝ) = -1 / 2 - 1 by norm_num, Real.rpow_sub_one ht.1.ne',
    show (-(3 / 5) : ℝ) = -3 / 5 by norm_num]
  ring

private theorem radial_lintegral_le_constant {f : ℝ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ r ∈ Ioc (0 : ℝ) 1, f r ≤ c) : (∫⁻ r, f r ∂radialMeasure) ≤ c := by
  calc
    _ ≤ ∫⁻ _r, c ∂radialMeasure := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact h r hr
    _ = _ := by
      rw [lintegral_const]
      norm_num [radialMeasure, Measure.restrict_apply_univ, Real.volume_Ioc]

set_option maxHeartbeats 500000 in
/-- A represented symmetric heat kernel with the manuscript's free
and short-tip diagonal comparisons has square-summable weighted
collar images at each positive duration and a finite joint duration
integral. The factor is measured in the same radial coordinate as the
determinant. -/
theorem weighted_collar_hs_joint_finite {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ RadialL2) (A : ℝ → RadialL2 →L[ℂ] RadialL2)
    (rows : ℝ → ℝ → RadialL2) (K : ℝ → ℝ → ℝ → ℝ)
    (D : ℝ → ℝ → ℝ) (F : ℝ → ℝ) {C B N k T : ℝ}
    (hC : 0 ≤ C) (hk : 0 < k)
    (hF0 : ∀ r ∈ Ioc 0 1, 0 ≤ F r)
    (hF : ∀ r ∈ Ioc 0 1, F r ≤ Real.exp (logEnvelope B N r))
    (hFree : ∀ t ∈ Ioc 0 T, ∀ r ∈ Ioc 0 1, D t r ≤ C * t ^ (-1 / 2 : ℝ))
    (hTip : ∀ t ∈ Ioc 0 T, ∀ r ∈ Ioc 0 1, r < 1 / 4 → r ^ (5 : ℕ) ≤ t →
      D t r ≤ C * t ^ (-1 / 2 : ℝ) * Real.exp (-k / r ^ (3 : ℕ)))
    (hKernelRows : ∀ t ∈ Ioc 0 T, ∀ᵐ r ∂radialMeasure,
      ∀ᵐ y ∂radialMeasure, rows t r y = (K t r y : ℂ))
    (hSymmetric : ∀ t ∈ Ioc 0 T, ∀ᵐ r ∂radialMeasure,
      ∀ᵐ y ∂radialMeasure, K t y r = K t r y)
    (hDiagonal : ∀ t ∈ Ioc 0 T, ∀ᵐ r ∂radialMeasure,
      (∫ y, K t r y * K t y r ∂radialMeasure) = D t r)
    (hRows : ∀ t ∈ Ioc 0 T, ∀ i, ∀ᵐ r ∂radialMeasure,
      A t (b i) r = weightedCollarMultiplier F t r * inner ℂ (rows t r) (b i)) :
    (∀ t ∈ Ioc 0 T, collarHSSq b (A t) ≠ ⊤) ∧
      (∫⁻ t in Ioc (0 : ℝ) T,
        ENNReal.ofReal (1 / (2 * Real.pi * t)) * collarHSSq b (A t)) ≠ ⊤ := by
  let c : ℝ := min (k / 2) (1 / 2)
  have hc : 0 < c := lt_min (half_pos hk) (by norm_num)
  obtain ⟨M, hM, hFbound⟩ := determinant_envelope_absorbed B N hc hF
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  let C' := C * Real.exp (64 * k)
  have hCC' : C ≤ C' := by
    have he := Real.one_le_exp_iff.mpr (by positivity : 0 ≤ 64 * k)
    simpa [C'] using mul_le_mul_of_nonneg_left he hC
  have hC' : 0 ≤ C' := hC.trans hCC'
  have hBound (t : ℝ) (ht : t ∈ Ioc 0 T) :
      collarHSSq b (A t) ≤ ENNReal.ofReal (collarDurationMajorant (M * C') c t) := by
    have hf : ∀ᵐ r ∂radialMeasure, 0 ≤ F r := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr using hF0 r hr
    rw [weighted_collar_hs_sq_from_semigroup b hf (hKernelRows t ht) (hSymmetric t ht)
      (hDiagonal t ht) (hRows t ht)]
    apply radial_lintegral_le_constant
    intro r hr
    apply ENNReal.ofReal_le_ofReal
    have hFree' : D t r ≤ C' * t ^ (-1 / 2 : ℝ) :=
      (hFree t ht r hr).trans (mul_le_mul_of_nonneg_right hCC' (Real.rpow_nonneg ht.1.le _))
    unfold collarDurationMajorant
    rw [← mul_assoc]
    exact joint_collar_pointwise_bound hC' hM0 hk hr.1 ht.1 (hF0 r hr) (hFbound r hr) hFree'
      (extend_short_tip_bound hC hk hFree hTip ht hr)
  exact ⟨fun t ht => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hBound t ht),
    shared_trace_duration_integral_ne_top (mul_nonneg hM0 hC') hc hBound⟩

end UV.ContinueCollarHSJoint
