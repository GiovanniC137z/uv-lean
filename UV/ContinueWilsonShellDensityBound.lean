import UV.ContinueWilsonDisplacementDensity

/-! Uniform density control for a genuine A4 mark, its independent pair,
and further independent translated increments on the four-plane. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter Metric
open scoped ENNReal Topology RealInnerProductSpace

namespace UV

variable {ι : Type*} [Fintype ι]

def wilsonSingleDisplacement (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    WilsonBallSpace ι →L[ℝ] OSFourSpace := L • T.toContinuousLinearMap.adjoint

/-- A ball and its translates along the four readout directions fit inside
a slightly larger finite-volume ball. Slicing in the opposite order
bounds the projected mark by a fixed multiple of four-volume. -/
theorem wilson_single_density_bound {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ (wilsonBallMeasure ι).map (wilsonSingleDisplacement L T) ≤ C • volume := by
  let R := wilsonSingleDisplacement L T
  let J : OSFourSpace →L[ℝ] WilsonBallSpace ι := L⁻¹ • T.toContinuousLinearMap
  let ν := wilsonBallMeasure (Fin 4)
  let B : Set (WilsonBallSpace ι) := ball 0 1
  let G : Set (WilsonBallSpace ι) := ball 0 (1+L⁻¹)
  let b := (volume (ball (0:OSFourSpace) 1))⁻¹
  let a := ((volume : Measure (WilsonBallSpace ι)) B)⁻¹
  have hRT (x : OSFourSpace) : R (J x) = x := by
    have he := T.toContinuousLinearMap.norm_map_iff_adjoint_comp_self.mp T.norm_map
    have hi : T.toContinuousLinearMap.adjoint (T x) = x :=
      congrArg (fun f : OSFourSpace →L[ℝ] OSFourSpace => f x) he
    simp [R,J,wilsonSingleDisplacement,hi,smul_smul,hL.ne']
  have hnorm (x : OSFourSpace) : ‖J x‖ = L⁻¹*‖x‖ := by
    simp [J,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hL.le)]
  have hν : ∀ᵐ x ∂ν, ‖x‖ < 1 := by
    simpa only [mem_ball,dist_zero_right] using
      (ae_cond_mem (μ := (volume : Measure OSFourSpace)) (s := ball 0 1) measurableSet_ball)
  refine ⟨a*(b*volume G), ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (measure_ball_pos volume 0 zero_lt_one).ne')
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (measure_ball_pos volume 0 zero_lt_one).ne') measure_ball_ne_top),?_⟩
  apply Measure.le_iff.mpr
  intro S hS
  let A := B ∩ R ⁻¹' S
  let W := (fun p : OSFourSpace × WilsonBallSpace ι => p.2 + J p.1) ⁻¹' A
  have hA : MeasurableSet A := measurableSet_ball.inter (R.continuous.measurable hS)
  have hW : MeasurableSet W := (continuous_snd.add (J.continuous.comp continuous_fst)).measurable hA
  have hx (x : OSFourSpace) : volume (Prod.mk x ⁻¹' W) = volume A :=
    (measurePreserving_add_right volume (J x)).measure_preimage hA.nullMeasurableSet
  have he : ν.prod (volume : Measure (WilsonBallSpace ι)) W = volume A := by
    rw [Measure.prod_apply hW]
    simp only [hx,lintegral_const,measure_univ,mul_one]
  have hy (y : WilsonBallSpace ι) : ν ((fun x => (x,y)) ⁻¹' W) ≤
      G.indicator (fun _ => b*volume S) y := by
    by_cases hg : y ∈ G
    · rw [indicator_of_mem hg]
      have hs : (fun x => (x,y)) ⁻¹' W ⊆ (R y+·) ⁻¹' S := by
        intro x hx'
        have h := hx'.2
        change R (y+J x) ∈ S at h
        simpa only [map_add,hRT] using h
      apply (measure_mono hs).trans
      rw [show ν = ProbabilityTheory.cond volume (ball (0:OSFourSpace) 1) from rfl,
        cond_apply' ((measurable_const_add (R y)) hS)]
      exact mul_le_mul_left' ((measure_mono inter_subset_right).trans_eq
        ((measurePreserving_add_left volume (R y)).measure_preimage hS.nullMeasurableSet)) _
    · rw [indicator_of_notMem hg]
      apply le_of_eq
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hν] with x hx' hw
      have hmem := hw.1
      change y+J x ∈ ball 0 1 at hmem
      have hy' : ‖y+J x‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hmem
      apply hg
      change y ∈ ball 0 (1+L⁻¹)
      rw [mem_ball,dist_zero_right]
      have hn : ‖y‖ ≤ ‖y+J x‖+‖J x‖ := by simpa only [add_sub_cancel_right] using norm_sub_le (y+J x) (J x)
      rw [hnorm] at hn
      nlinarith [mul_lt_mul_of_pos_left hx' (inv_pos.mpr hL)]
  have hb : volume A ≤ (b*volume S)*volume G := by
    rw [←he,Measure.prod_apply_symm hW]
    apply (lintegral_mono hy).trans_eq
    rw [lintegral_indicator (show MeasurableSet G from measurableSet_ball),setLIntegral_const]
  rw [Measure.map_apply R.continuous.measurable hS,wilsonBallMeasure,cond_apply' (R.continuous.measurable hS),Measure.smul_apply,smul_eq_mul]
  change a * volume A ≤ a*(b*volume G)*volume S
  exact (mul_le_mul_left' hb a).trans_eq (by ac_rfl)

/-- Adding an independent random translation preserves the same volume
bound, regardless of that translation's probability law. -/
theorem wilson_translated_density_bound {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [IsProbabilityMeasure ν]
    {F : α → OSFourSpace} {G : β → OSFourSpace} (hF : Measurable F) (hG : Measurable G)
    {C : ℝ≥0∞} (hC : μ.map F ≤ C • volume) :
    (μ.prod ν).map (fun z => F z.1 + G z.2) ≤ C • volume := by
  apply Measure.le_iff.mpr
  intro S hS
  have hm : Measurable (fun z : α × β => F z.1 + G z.2) :=
    (hF.comp measurable_fst).add (hG.comp measurable_snd)
  rw [Measure.map_apply hm hS,Measure.prod_apply_symm (hm hS),Measure.smul_apply,smul_eq_mul]
  have hb (y : β) : μ ((fun x => (x,y)) ⁻¹' ((fun z : α × β => F z.1+G z.2) ⁻¹' S)) ≤ C*volume S := by
    change μ (F ⁻¹' ((·+G y) ⁻¹' S)) ≤ _
    have hs := (measurable_add_const (G y)) hS
    rw [←Measure.map_apply hF hs]
    exact (hC ((·+G y) ⁻¹' S)).trans_eq (by
      rw [Measure.smul_apply,smul_eq_mul,(measurePreserving_add_right volume (G y)).measure_preimage hS.nullMeasurableSet])
  exact (lintegral_mono hb).trans_eq (by simp)

theorem wilson_two_mark_density_bound {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ wilsonDisplacementMeasure L T ≤ C • volume := by
  obtain ⟨C,hC,hμ⟩ := wilson_single_density_bound hL T
  let R := wilsonSingleDisplacement L T
  have he (z : WilsonBallSpace ι × WilsonBallSpace ι) : wilsonPairDisplacement L T z = R z.1+R z.2 := by
    change R (z.1+z.2) = _
    exact map_add R _ _
  refine ⟨C,hC,?_⟩
  simp only [wilsonDisplacementMeasure,funext he]
  exact wilson_translated_density_bound R.continuous.measurable R.continuous.measurable hμ

theorem wilson_rn_density_bounded {μ : Measure OSFourSpace} [IsFiniteMeasure μ] {C : ℝ≥0∞}
    (hC : μ ≤ C • volume) : ∀ᵐ d ∂volume, μ.rnDeriv volume d ≤ C := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv _ _)
  intro S hS _
  rw [setLIntegral_const,←withDensity_apply _ hS,Measure.withDensity_rnDeriv_eq _ _ (absolutelyContinuous_of_le_smul hC)]
  exact hC S

theorem wilson_displacement_density_bounded {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ᵐ d ∂volume, wilsonDisplacementDensity L T d ≤ C := by
  obtain ⟨C,hC,hμ⟩ := wilson_two_mark_density_bound hL T
  exact ⟨C,hC,wilson_rn_density_bounded hμ⟩

end UV
