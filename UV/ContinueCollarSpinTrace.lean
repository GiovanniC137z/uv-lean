import UV.ContinueCollarAngular

/-! The shared-readout spin trace, summed over exact shifted integer modes and both chiralities. -/

noncomputable section

open MeasureTheory Set

namespace UV.ContinueCollarSpinTrace

/-- The scalar trace summed over the normal angular Fourier basis and both chiralities. -/
def spinReadout (F : ℝ → ℝ) (K : ℤ → Fin 2 → ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑' n : ℤ, ∑ s : Fin 2, UV.FurtherBoundaryCollar.collarReadout F (K n s) t

set_option maxHeartbeats 700000 in
/-- The full angular trace has the claimed short-time rate after the scalar kernel comparisons. -/
theorem normal_spin_trace_from_diagonal_comparison
    {F : ℝ → ℝ} {K : ℤ → Fin 2 → ℝ → ℝ → ℝ} {K₀ : ℝ → ℝ → ℝ}
    {C A N k a b θ T : ℝ} (hC : 0 ≤ C) (hk : 0 < k) (ha : 0 < a) (hb : 0 ≤ b)
    (hT : T < (1 / 4 : ℝ) ^ (5 : ℕ))
    (hFmeas : Measurable F) (hKmeas : ∀ n s, Measurable (Function.uncurry (K n s)))
    (hF0 : ∀ r ∈ Ioc 0 1, 0 ≤ F r)
    (hF : ∀ r ∈ Ioc 0 1, F r ≤ Real.exp (UV.FurtherBoundaryEnvelope.logEnvelope A N r))
    (hFree : ∀ t ∈ Ioc 0 T, ∀ r ∈ Ioc 0 1, K₀ t r ≤ C * t ^ (-1 / 2 : ℝ))
    (hTip : ∀ t ∈ Ioc 0 T, ∀ r ∈ Ioc 0 1, r < 1 / 4 → r ^ (5 : ℕ) ≤ t →
      K₀ t r ≤ C * t ^ (-1 / 2 : ℝ) * Real.exp (-k / r ^ (3 : ℕ)))
    (hK0 : ∀ n s, ∀ t ∈ Ioc 0 T, ∀ r ∈ Ioc 0 1, 0 ≤ K n s t r)
    (hCompare : ∀ n s, ∀ t ∈ Ioc 0 T, ∀ r ∈ Ioc 0 1,
      K n s t r ≤ Real.exp (-(a * t) * ((n : ℝ) + θ) ^ (2 : ℕ) + b * t) * K₀ t r) :
    (∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Ioc 0 T,
      Summable (fun n : ℤ => ∑ s : Fin 2, UV.FurtherBoundaryCollar.collarReadout F (K n s) t) ∧
        spinReadout F K t ≤ D * t⁻¹ *
          Real.exp (-min (k / 2) (1 / 2) * t ^ (-3 / 5 : ℝ))) ∧
      IntegrableOn (fun t => spinReadout F K t / t) (Ioc 0 T) := by
  let c : ℝ := min (k / 2) (1 / 2)
  have hc : 0 < c := lt_min (by linarith) (by norm_num)
  obtain ⟨M, hM, henv⟩ := UV.FurtherBoundaryEnvelope.determinant_envelope_absorbed A N hc hF
  have hM0 := zero_le_one.trans hM
  let Q := 2 * M * C * Real.exp (b * T)
  let D := Q * (2 + Real.sqrt (Real.pi / a))
  have hQ : 0 ≤ Q := by positivity
  have hD : 0 ≤ D := by positivity
  have hread {t : ℝ} (ht : t ∈ Ioc 0 T) (n : ℤ) (s : Fin 2) :
      0 ≤ UV.FurtherBoundaryCollar.collarReadout F (K n s) t ∧
      UV.FurtherBoundaryCollar.collarReadout F (K n s) t ≤
        M * C * Real.exp (b * T) * t ^ (-1 / 2 : ℝ) * Real.exp (-c * t ^ (-3 / 5 : ℝ)) *
          Real.exp (-(a * t) * ((n : ℝ) + θ) ^ (2 : ℕ)) := by
    have ht0 : 0 < t := ht.1
    let q := M * C * Real.exp (b * T) * t ^ (-1 / 2 : ℝ) * Real.exp (-c * t ^ (-3 / 5 : ℝ)) *
      Real.exp (-(a * t) * ((n : ℝ) + θ) ^ (2 : ℕ))
    have hnneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioc 0 1)]
        fun r => F r * Real.exp (-(r ^ (2 : ℕ)) / t) * K n s t r := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact mul_nonneg (mul_nonneg (hF0 r hr) (Real.exp_nonneg _)) (hK0 n s t ht r hr)
    refine ⟨integral_nonneg_of_ae hnneg, ?_⟩
    change ∫ r in Ioc 0 1, F r * Real.exp (-(r ^ (2 : ℕ)) / t) * K n s t r ≤ q
    refine (integral_mono_of_nonneg hnneg
      (integrableOn_const (C := q) (by simp [Real.volume_Ioc])) ?_).trans_eq ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      have hlocal := UV.FurtherBoundaryCollar.joint_collar_pointwise_bound hC hM0 hk hr.1 ht.1
        (hF0 r hr) (henv r hr) (hFree t ht r hr) (fun htr => hTip t ht r hr (by
          by_contra! hnot
          have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) hnot 5
          linarith [hpow.trans (htr.trans ht.2)]) htr)
      let w := -(a * t) * ((n : ℝ) + θ) ^ (2 : ℕ)
      change F r * Real.exp (-(r ^ (2 : ℕ)) / t) * K n s t r ≤ q
      calc
        _ ≤ F r * Real.exp (-(r ^ (2 : ℕ)) / t) * (Real.exp (w + b * t) * K₀ t r) :=
          mul_le_mul_of_nonneg_left (hCompare n s t ht r hr) (mul_nonneg (hF0 r hr) (Real.exp_nonneg _))
        _ = Real.exp (w + b * t) * (F r * Real.exp (-(r ^ (2 : ℕ)) / t) * K₀ t r) := by ring
        _ ≤ Real.exp (w + b * t) *
              (M * C * t ^ (-1 / 2 : ℝ) * Real.exp (-c * t ^ (-3 / 5 : ℝ))) :=
          mul_le_mul_of_nonneg_left hlocal (Real.exp_nonneg _)
        _ ≤ Real.exp (w + b * T) *
              (M * C * t ^ (-1 / 2 : ℝ) * Real.exp (-c * t ^ (-3 / 5 : ℝ))) :=
          mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.mpr (add_le_add_left (mul_le_mul_of_nonneg_left ht.2 hb) _))
            (by positivity)
        _ = q := by rw [Real.exp_add]; unfold w q; ring
    · rw [setIntegral_const, Real.volume_real_Ioc]
      norm_num
  have hsum (t : ℝ) (ht : t ∈ Ioc 0 T) :
      Summable (fun n : ℤ => ∑ s : Fin 2, UV.FurtherBoundaryCollar.collarReadout F (K n s) t) ∧
        spinReadout F K t ≤ D * t⁻¹ * Real.exp (-c * t ^ (-3 / 5 : ℝ)) := by
    have ht0 : 0 < t := ht.1
    have ht1 : t ≤ 1 := ht.2.trans (hT.le.trans (by norm_num))
    obtain ⟨hgauss, hgaussbound⟩ := UV.ContinueCollarAngular.shifted_angular_short_time_bound ha ht.1 ht1 θ
    let P := Q * t ^ (-1 / 2 : ℝ) * Real.exp (-c * t ^ (-3 / 5 : ℝ))
    have hP : 0 ≤ P := by positivity
    let f := fun n : ℤ => ∑ s : Fin 2, UV.FurtherBoundaryCollar.collarReadout F (K n s) t
    have hf (n : ℤ) : 0 ≤ f n := Finset.sum_nonneg (fun s _ => (hread ht n s).1)
    have hterm (n : ℤ) : f n ≤ P * Real.exp (-(a * t) * ((n : ℝ) + θ) ^ (2 : ℕ)) := by
      have hh := Finset.sum_le_sum (s := Finset.univ) (fun s (_ : s ∈ Finset.univ) => (hread ht n s).2)
      change f n ≤ _ at hh
      refine hh.trans_eq ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      unfold P Q
      norm_num
      ring
    have hgs := hgauss.mul_left P
    have hfs := Summable.of_nonneg_of_le hf hterm hgs
    refine ⟨hfs, ?_⟩
    have hcmp := hfs.tsum_le_tsum hterm hgs
    rw [tsum_mul_left] at hcmp
    calc
      spinReadout F K t ≤ P * ∑' n : ℤ, Real.exp (-(a * t) * ((n : ℝ) + θ) ^ (2 : ℕ)) := hcmp
      _ ≤ P * ((2 + Real.sqrt (Real.pi / a)) * t ^ (-1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hgaussbound hP
      _ = _ := by
        have hpow : t ^ (-1 / 2 : ℝ) * t ^ (-1 / 2 : ℝ) = t⁻¹ := by
          rw [← Real.rpow_add ht.1, show (-1 / 2 : ℝ) + (-1 / 2) = -1 by ring, Real.rpow_neg_one]
        unfold P D
        rw [show Q * t ^ (-1 / 2 : ℝ) * Real.exp (-c * t ^ (-3 / 5 : ℝ)) *
            ((2 + Real.sqrt (Real.pi / a)) * t ^ (-1 / 2 : ℝ)) =
              Q * (2 + Real.sqrt (Real.pi / a)) *
                (t ^ (-1 / 2 : ℝ) * t ^ (-1 / 2 : ℝ)) * Real.exp (-c * t ^ (-3 / 5 : ℝ)) by ring,
          hpow]
  refine ⟨⟨D, hD, hsum⟩, ?_⟩
  have hreadmeas (n : ℤ) (s : Fin 2) :
      Measurable (UV.FurtherBoundaryCollar.collarReadout F (K n s)) := by
    have hmeas : Measurable (fun z : ℝ × ℝ =>
        F z.2 * Real.exp (-(z.2 ^ (2 : ℕ)) / z.1) * K n s z.1 z.2) :=
      ((hFmeas.comp measurable_snd).mul (by fun_prop)).mul (hKmeas n s)
    exact (hmeas.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 1))).measurable
  have hsp : AEMeasurable (spinReadout F K) (volume.restrict (Ioc 0 T)) := by
    apply aemeasurable_of_tendsto_metrizable_ae (Filter.atTop : Filter (Finset ℤ))
      (f := fun S : Finset ℤ => fun t => ∑ n ∈ S, ∑ s : Fin 2,
        UV.FurtherBoundaryCollar.collarReadout F (K n s) t)
    · intro S
      exact (Finset.measurable_sum _ (fun n _ => Finset.measurable_sum _
        (fun s _ => hreadmeas n s))).aemeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (hsum t ht).1.hasSum
  have htime : AEMeasurable (fun t : ℝ => spinReadout F K t / t)
      (volume.restrict (Ioc 0 T)) := hsp.div measurable_id.aemeasurable
  have htemp := (UV.FurtherBoundaryCollar.stretched_exponential_integrableOn (a := 3 / 5) (T := T)
    (by norm_num) hc 2).const_mul D
  apply htemp.mono' htime.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hsum0 : 0 ≤ spinReadout F K t :=
    tsum_nonneg (fun n => Finset.sum_nonneg (fun s _ => (hread ht n s).1))
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hsum0 ht.1.le)]
  have hdiv := div_le_div_of_nonneg_right (hsum t ht).2 ht.1.le
  change _ ≤ D * (t ^ (-2 : ℝ) * Real.exp (-c * t ^ (-(3 / 5) : ℝ)))
  rw [show (-(3 / 5) : ℝ) = -3 / 5 by norm_num]
  refine hdiv.trans_eq ?_
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht.1.le,
    Real.rpow_natCast, ← inv_pow]
  ring

end UV.ContinueCollarSpinTrace
