import UV.ContinueSewnFlagSchwinger

/-! The conditional geometric moment test for the original bare loop
momentum integral. The finite complex displacement law is represented
by a bounded density over its given positive dominating measure. -/

noncomputable section
open Real MeasureTheory Set Filter Matrix
open scoped BigOperators ENNReal Matrix
namespace UV.SewnFlags

def routedCharacteristic {L : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin L × Fin 4)))
    (w : EuclideanSpace ℝ (Fin L × Fin 4) → ℂ) (k : EuclideanSpace ℝ (Fin L × Fin 4)) : ℂ :=
  ∫ d, w d*routedPhase d k ∂μ

theorem routedCharacteristic_measurable {L : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin L × Fin 4)))
    [IsFiniteMeasure μ] (w : EuclideanSpace ℝ (Fin L × Fin 4) → ℂ) (hw : Measurable w) :
    Measurable (routedCharacteristic μ w) := by
  have hf : Measurable (fun q : (EuclideanSpace ℝ (Fin L × Fin 4)) ×
        (EuclideanSpace ℝ (Fin L × Fin 4)) => w q.1*routedPhase q.1 q.2) :=
    (hw.comp measurable_fst).mul routedPhase_continuous.measurable
  exact hf.stronglyMeasurable.integral_prod_left'.measurable

private theorem routed_fixed_time_pairing_le {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (hC : Function.Injective C.mulVec) (t : Fin N → ℝ) (ht : ∀ i, 0 < t i)
    (p : Fin N → ScalarMomentum) (μ : Measure (EuclideanSpace ℝ (Fin L × Fin 4))) [IsFiniteMeasure μ]
    (w : EuclideanSpace ℝ (Fin L × Fin 4) → ℂ) (hw : Measurable w) (hw₁ : ∀ d, ‖w d‖ ≤ 1)
    (hγ : ∀ k, 0 ≤ (routedCharacteristic μ w k).re) :
    (∫⁻ k, ENNReal.ofReal (routedCharacteristic μ w k).re *
      ENNReal.ofReal (exp (-(routedAffineEnergy C t p k)))) ≤
      ENNReal.ofReal (π^(L*2)) * ∫⁻ d,
        ENNReal.ofReal (((residualGram C t).det^2)⁻¹ * exp (-(routedInverseWeight C t d)/4)) ∂μ := by
  let V := EuclideanSpace ℝ (Fin L × Fin 4)
  let R := fun k : V => exp (-(routedAffineEnergy C t p k))
  have hR_cont : Continuous R := Real.continuous_exp.comp
    ((routedAffineEnergy_continuous C p).comp (continuous_const.prodMk continuous_id)).neg
  have hRint : Integrable R := by
    apply (routed_affine_wave_bound C hC t ht p 0).1.norm.congr
    filter_upwards with k
    change ‖routedAffineWave C t p 0 k‖ = R k
    rw [routedAffineWave,norm_mul,routedPhase_norm,one_mul,Complex.norm_real,Real.norm_of_nonneg (exp_pos _).le]
  let F := fun v : V × V => w v.1 * routedAffineWave C t p v.1 v.2
  have hFm : Measurable F := by
    unfold F routedAffineWave
    exact (hw.comp measurable_fst).mul (routedPhase_continuous.measurable.mul
      ((hR_cont.measurable.comp measurable_snd).complex_ofReal))
  have hFi : Integrable F (μ.prod (volume : Measure V)) := by
    have h := (integrable_const (μ := μ) (1:ℝ)).mul_prod hRint
    refine h.mono' hFm.aestronglyMeasurable (ae_of_all _ fun v => ?_)
    change ‖w v.1 * routedAffineWave C t p v.1 v.2‖ ≤ 1*R v.2
    rw [routedAffineWave,norm_mul,norm_mul,routedPhase_norm,one_mul,Complex.norm_real,
      Real.norm_of_nonneg (exp_pos _).le]
    exact mul_le_mul_of_nonneg_right (hw₁ v.1) (exp_pos _).le
  let G := fun k : V => ∫ d, F (d,k) ∂μ
  let H := fun d : V => ∫ k, F (d,k)
  have hGi : Integrable G := hFi.integral_prod_right
  have hHi : Integrable H μ := hFi.integral_prod_left
  have hG (k : V) : (G k).re = (routedCharacteristic μ w k).re * R k := by
    unfold G F routedAffineWave
    simp_rw [← mul_assoc]
    change (∫ d, (w d * routedPhase d k)*(R k:ℂ) ∂μ).re = _
    rw [integral_mul_const]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,routedCharacteristic]
  have hGi' : Integrable (fun k => (routedCharacteristic μ w k).re * R k) :=
    hGi.re.congr (ae_of_all _ fun k => hG k)
  have hC₀ : 0 ≤ᵐ[volume] fun k : V => (routedCharacteristic μ w k).re * R k :=
    ae_of_all _ fun k => mul_nonneg (hγ k) (exp_pos _).le
  have hSwap : (∫ k, G k) = ∫ d, H d ∂μ :=
    (integral_integral_swap (f := fun d k => F (d,k)) hFi).symm
  have hEq : (∫ k : V, (routedCharacteristic μ w k).re * R k) = (∫ d, H d ∂μ).re := by
    simp_rw [← hG]
    change (∫ k, RCLike.re (G k)) = _
    rw [integral_re hGi,hSwap]
    rfl
  simp_rw [← ENNReal.ofReal_mul (hγ _)]
  change (∫⁻ k : V, ENNReal.ofReal ((routedCharacteristic μ w k).re * R k)) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal hGi' hC₀,hEq]
  calc
    _ ≤ ENNReal.ofReal (∫ d, ‖H d‖ ∂μ) :=
      ENNReal.ofReal_le_ofReal ((Complex.re_le_norm _).trans (norm_integral_le_integral_norm _))
    _ = ∫⁻ d, ENNReal.ofReal ‖H d‖ ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hHi.norm (ae_of_all _ fun _ => norm_nonneg _)
    _ ≤ _ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono
      intro d
      dsimp only
      rw [← ENNReal.ofReal_mul (pow_nonneg pi_pos.le _)]
      apply ENNReal.ofReal_le_ofReal
      change ‖∫ k, w d*routedAffineWave C t p d k‖ ≤ _
      rw [integral_const_mul,norm_mul]
      calc
        _ ≤ ‖∫ k, routedAffineWave C t p d k‖ := mul_le_of_le_one_left (norm_nonneg _) (hw₁ d)
        _ ≤ _ := by rw [← mul_assoc]; exact (routed_affine_wave_bound C hC t ht p d).2

/-- The all-ordering projected moment condition implies finiteness of
the literal nonnegative bare momentum majorant, for arbitrary real
affine routing shifts, at positive edge masses and Schwinger exponents. -/
theorem routed_bare_momentum_finite {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (hC : Function.Injective C.mulVec) (ν m : Fin N → ℝ)
    (hν : ∀ i, 0 < ν i) {η : ℝ} (hη : 0 < η) (hm : ∀ i, η ≤ (m i)^2)
    (p : Fin N → ScalarMomentum) (μ : Measure (EuclideanSpace ℝ (Fin L × Fin 4))) [IsFiniteMeasure μ]
    (w : EuclideanSpace ℝ (Fin L × Fin 4) → ℂ) (hw : Measurable w) (hw₁ : ∀ d, ‖w d‖ ≤ 1)
    (hγ : ∀ k, 0 ≤ (routedCharacteristic μ w k).re)
    (hJoint : ∀ e : Equiv.Perm (Fin N),
      (∫⁻ d, ∏ i, displacementCost (routingFaceExcess (reindexRouting C e) (ν ∘ e) i)
        (projectedDisplacement (reindexRouting C e) (routingShortPrefix i) d) ∂μ) < ⊤) :
    (∫⁻ k, ENNReal.ofReal (routedCharacteristic μ w k).re *
      ENNReal.ofReal (routedDenominator C ν m p k)) < ⊤ := by
  let V := EuclideanSpace ℝ (Fin L × Fin 4)
  let U := Fin N → ℝ
  let τ := (volume : Measure U).restrict (positiveDurations N)
  let g := fun k : V => ENNReal.ofReal (routedCharacteristic μ w k).re
  have hg : Measurable g := (Complex.measurable_re.comp (routedCharacteristic_measurable μ w hw)).ennreal_ofReal
  let B := fun (d : V) (t : U) => ENNReal.ofReal (routedMassSchwingerWeight C ν m t d)
  have hB : Measurable (fun q : V × U => B q.1 q.2) :=
    (routedMassSchwingerWeight_measurable C ν m).ennreal_ofReal
  have hcost : (∫⁻ d, (∫⁻ t, B d t ∂τ) ∂μ) < ⊤ :=
    massive_all_flag_cost_finite C hC ν m hη hm μ hJoint
  let K := ENNReal.ofReal (π^(L*2))
  let Γ := ENNReal.ofReal (∏ i, Gamma (ν i))
  have hΓ : Γ ≠ 0 := by
    unfold Γ
    exact ENNReal.ofReal_ne_zero_iff.mpr (Finset.prod_pos fun i _ => Gamma_pos_of_pos (hν i))
  have hfull : Γ * (∫⁻ k, g k * ENNReal.ofReal (routedDenominator C ν m p k)) < ⊤ := by
    unfold Γ
    rw [routed_schwinger_identity C ν m hν (fun i => hη.trans_le (hm i)) p g hg]
    have hT (t : U) (ht : t ∈ positiveDurations N) :
        ENNReal.ofReal (routedTimePower ν m t) *
          (∫⁻ k, g k * ENNReal.ofReal (exp (-(routedAffineEnergy C t p k)))) ≤
          K*(∫⁻ d, B d t ∂μ) := by
      apply (mul_le_mul_left' (routed_fixed_time_pairing_le C hC t ht p μ w hw hw₁ hγ) _).trans
      rw [mul_left_comm]
      apply mul_le_mul_left'
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono
      intro d
      dsimp only
      rw [← ENNReal.ofReal_mul (routedTimePower_nonneg ν m t ht)]
      unfold B routedTimePower routedMassSchwingerWeight routedSchwingerWeight
      apply le_of_eq
      congr 1
      ring
    change (∫⁻ t, _ ∂τ) < ⊤
    refine (lintegral_mono_ae ((ae_restrict_mem (positiveDurations_measurable N)).mono hT)).trans_lt ?_
    rw [lintegral_const_mul' _ _ (show K ≠ ⊤ from ENNReal.ofReal_ne_top),
      ← lintegral_lintegral_swap hB.aemeasurable]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hcost
  by_contra! hinf
  change ⊤ ≤ (∫⁻ k, g k * ENNReal.ofReal (routedDenominator C ν m p k)) at hinf
  rw [top_le_iff.mp hinf,ENNReal.mul_top hΓ] at hfull
  exact (lt_irrefl _ hfull)

/-- Absolute convergence of any measurable contribution with the
stated nonnegative characteristic majorant and positive edge masses. -/
theorem routed_bare_momentum_integrable {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (hC : Function.Injective C.mulVec) (ν m : Fin N → ℝ) (hν : ∀ i, 0 < ν i) (hm : ∀ i, 0 < m i)
    (p : Fin N → ScalarMomentum) (μ : Measure (EuclideanSpace ℝ (Fin L × Fin 4))) [IsFiniteMeasure μ]
    (w : EuclideanSpace ℝ (Fin L × Fin 4) → ℂ) (hw : Measurable w) (hw₁ : ∀ᵐ d ∂μ, ‖w d‖ ≤ 1)
    (hγ : ∀ k, 0 ≤ (routedCharacteristic μ w k).re)
    (hJoint : ∀ e : Equiv.Perm (Fin N),
      (∫⁻ d, ∏ i, let S := (routingShortPrefix i).map e.toEmbedding
        displacementCost ((∑ j ∈ S, ν j) - 2 * Module.finrank ℝ (routingFace C S))
          (projectedDisplacement C S d) ∂μ) < ⊤)
    (A : EuclideanSpace ℝ (Fin L × Fin 4) → ℂ) (hA : AEStronglyMeasurable A volume)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ᵐ k, ‖A k‖ ≤ K * (routedCharacteristic μ w k).re * routedDenominator C ν m p k) :
    Integrable A := by
  let S := {d | ‖w d‖ ≤ 1}
  let W := S.indicator w
  have hW : Measurable W := hw.indicator (measurableSet_le hw.norm measurable_const)
  have hW₁ (d) : ‖W d‖ ≤ 1 := by
    change ‖S.indicator w d‖ ≤ 1
    by_cases h : d ∈ S
    · rw [indicator_of_mem h]
      exact h
    · rw [indicator_of_notMem h,norm_zero]
      exact zero_le_one
  have hChar : routedCharacteristic μ w = routedCharacteristic μ W := by
    funext k
    unfold routedCharacteristic
    apply integral_congr_ae
    filter_upwards [hw₁] with d hd
    change w d*routedPhase d k = (S.indicator w d)*routedPhase d k
    rw [indicator_of_mem (show d ∈ S from hd)]
  simp_rw [hChar] at hγ hbound
  have hmin : ∃ η : ℝ, 0 < η ∧ ∀ i, η ≤ (m i)^2 := by
    by_cases h : (Finset.univ : Finset (Fin N)).Nonempty
    · exact ⟨Finset.univ.inf' h (fun i => (m i)^2),
        (Finset.lt_inf'_iff h).mpr (fun i _ => pow_pos (hm i) _),
        fun i => Finset.inf'_le _ (Finset.mem_univ i)⟩
    · exact ⟨1, zero_lt_one, fun i => False.elim (h ⟨i, Finset.mem_univ i⟩)⟩
  obtain ⟨η,hη,hm'⟩ := hmin
  refine ⟨hA, hasFiniteIntegral_iff_enorm.mpr ?_⟩
  have hg : Measurable (fun k => ENNReal.ofReal (routedCharacteristic μ W k).re) :=
    (Complex.measurable_re.comp (routedCharacteristic_measurable μ W hW)).ennreal_ofReal
  have hD : Measurable (fun k => ENNReal.ofReal (routedDenominator C ν m p k)) := by
    unfold routedDenominator
    exact (Finset.measurable_prod _ fun i _ =>
      (continuous_const.add (((residualRouting C i).continuous.add continuous_const).norm.pow 2)).measurable.pow_const _).ennreal_ofReal
  calc
    _ ≤ ∫⁻ k, ENNReal.ofReal K * (ENNReal.ofReal (routedCharacteristic μ W k).re *
        ENNReal.ofReal (routedDenominator C ν m p k)) := by
      apply lintegral_mono_ae
      filter_upwards [hbound] with k hk
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (hγ k), ← ENNReal.ofReal_mul hK]
      exact ENNReal.ofReal_le_ofReal (by simpa only [mul_assoc] using hk)
    _ < ⊤ := by
      rw [lintegral_const_mul _ (hg.mul hD)]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (routed_bare_momentum_finite C hC ν m hν hη hm' p μ W hW hW₁ hγ
          (fun e => by simpa only [reindexRouting_prefix_cost] using hJoint e))

end UV.SewnFlags
