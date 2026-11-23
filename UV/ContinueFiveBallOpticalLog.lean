import UV.ContinueFiveBallOpticalPhase

/-! The lower Dirac cut controls the complete phase integral. All
remaining physical channels may have arbitrary nonnegative weight. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology

namespace UV

theorem parity_phase_cut_measurable {b : ℝ → ℝ} (hb : Measurable b) : Measurable (parityPhaseCut b) := by
  have h : Measurable (fun z:ℝ×ℝ => parityFeynman z.2*b (parityFeynman z.2*z.1)) := by dsimp [parityFeynman]; fun_prop
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem parity_phase_cut_bound {b : ℝ → ℝ} {N : ℝ} (hN : ∀ v, |b v|≤N) (S : ℝ) : |parityPhaseCut b S| ≤ N := by
  change ‖∫ u in Ioo 0 1, parityFeynman u*b (parityFeynman u*S)‖ ≤ N
  apply (norm_integral_le_of_norm_le_const (C := N) _).trans_eq
  · simp [Real.volume_real_Ioo]
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [norm_mul,Real.norm_of_nonneg (parity_feynman_bounds hu).1.le,Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (abs_nonneg _) (parity_feynman_bounds hu).2).trans (hN _)

theorem parity_opening_lower {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) : 1-q ≤ openingWeight q := by
  rw [openingWeight_eq_of_nonneg hq]
  have hx := sub_nonneg.mpr hq1
  have h : 1-q ≤ Real.sqrt (1-q) := by
    apply (sq_le_sq₀ hx (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hx]
    nlinarith [mul_nonneg hq hx]
  exact h.trans (le_mul_of_one_le_right (Real.sqrt_nonneg _) (by linarith))

private theorem parity_log_pointwise {a X ε S : ℝ} (ha : 0<a) (hX : 0<X) (hε : 0<ε) (hS : a≤S) :
    S⁻¹-((a+X)*(S^2)⁻¹+ε) ≤ openingWeight (a/S)*parityCutWeight ε X S := by
  have hS0 := ha.trans_le hS
  have hz : 0 < S+X := by linarith
  have hx : 0 ≤ 1-a/S := sub_nonneg.mpr ((div_le_one hS0).mpr hS)
  have hp := parity_opening_lower (div_nonneg ha.le hS0.le) ((div_le_one hS0).mpr hS)
  have hW := parity_cut_weight_le_exp hε.le hX hS0.le
  have hlog : (1-a/S)/(S+X) - (1-a/S)*ε ≤ (1-a/S)*parityCutWeight ε X S := by
    rw [parityCutWeight,mul_div_assoc',le_div_iff₀ hz]
    have heq : ((1-a/S)/(S+X))*(S+X) = 1-a/S := div_mul_cancel₀ _ hz.ne'
    rw [sub_mul,heq]
    nlinarith [mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-ε*(S+X))) hx]
  apply (le_trans _ hlog).trans (mul_le_mul_of_nonneg_right hp hW.1)
  have hbase : S⁻¹-(a+X)*(S^2)⁻¹ ≤ (1-a/S)/(S+X) := by
    field_simp [hS0.ne',hz.ne']
    nlinarith [mul_pos hX (add_pos ha hX)]
  nlinarith [mul_nonneg (div_nonneg ha.le hS0.le) hε.le]

/-- An explicit uniform lower bound on the physical dispersion with
cutoff 1/R. The negative remainder is independent of R and the
coefficient of log R is sharp for the rank-r Dirac channel. -/
theorem parity_dispersion_log {b : ℝ → ℝ} (hb : Measurable b) {N : ℝ} (hN : ∀ v, |b v|≤N)
    {a X r R : ℝ} (ha : 0<a) (hX : 0<X) (hr : 0 ≤ r) (hR : a ≤ R)
    (hpos : ∀ S > 0, 0 ≤ parityPhaseCut b S)
    (hopt : ∀ S ≥ a, r*openingWeight (a/S) ≤ parityPhaseCut b S) :
    r*(Real.log (R/a)-((a+X)/a+1)) ≤ parityDispersionCutoff b R⁻¹ X := by
  let ε := R⁻¹
  have hR0 := ha.trans_le hR
  have hε : 0<ε := inv_pos.mpr hR0
  let f := fun S => parityPhaseCut b S*parityCutWeight ε X S
  have hν : IntegrableOn f (Ioi 0) := by
    have hi := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hε) 0).const_mul (N*X⁻¹)
    apply hi.mono' ((parity_phase_cut_measurable hb).mul (show Measurable (parityCutWeight ε X) by unfold parityCutWeight; fun_prop)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with S hS
    have hw := parity_cut_weight_le_exp hε.le hX hS.le
    rw [norm_mul,Real.norm_eq_abs,Real.norm_of_nonneg hw.1]
    exact (mul_le_mul (parity_phase_cut_bound hN S) hw.2 hw.1 ((abs_nonneg _).trans (hN 0))).trans_eq (by ring)
  have hsub : Ioc a R ⊆ Ioi (0:ℝ) := fun _ hs => ha.trans hs.1
  have hn : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with S hS
    exact mul_nonneg (hpos S hS) (parity_cut_weight_le_exp hε.le hX hS.le).1
  have hupper := setIntegral_mono_set hν hn (Eventually.of_forall hsub)
  change _ ≤ ∫ S in Ioi 0, f S
  apply le_trans _ hupper
  let g := fun S:ℝ => S⁻¹-((a+X)*(S^2)⁻¹+ε)
  have hp : ∀ x∈uIcc a R, x≠0 := fun x hx => (ha.trans_le ((uIcc_of_le hR) ▸ hx).1).ne'
  have h1 : ContinuousOn (fun S:ℝ => S⁻¹) (uIcc a R) := continuousOn_id.inv₀ hp
  have h2 : ContinuousOn (fun S:ℝ => (S^2)⁻¹) (uIcc a R) := (continuousOn_id.pow 2).inv₀ (fun S hS => pow_ne_zero _ (hp S hS))
  have hg : IntervalIntegrable g volume a R := (h1.sub ((continuousOn_const.mul h2).add continuousOn_const)).intervalIntegrable
  have hcmp : r*(∫ S in a..R, g S) ≤ ∫ S in Ioc a R, f S := by
    rw [←intervalIntegral.integral_const_mul,intervalIntegral.integral_of_le hR]
    apply setIntegral_mono_on ((hg.const_mul r).1) (hν.mono_set hsub) measurableSet_Ioc
    intro S hS
    have h := parity_log_pointwise ha hX hε hS.1.le
    exact (mul_le_mul_of_nonneg_left h hr).trans ((by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (hopt _ hS.1.le) (parity_cut_weight_le_exp hε.le hX (ha.trans hS.1).le).1) : r*(openingWeight (a/S)*parityCutWeight ε X S) ≤ _)
  apply le_trans _ hcmp
  apply mul_le_mul_of_nonneg_left _ hr
  have hInv2 : (∫ S in a..R, (S^2)⁻¹) = a⁻¹-R⁻¹ := by
    have hd (s) (hs:s∈uIcc a R) : HasDerivAt (fun x:ℝ => -x⁻¹) ((s^2)⁻¹) s := by
      convert ((hasDerivAt_inv (hp s hs)).neg) using 1
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd h2.intervalIntegrable]
    ring
  dsimp only [g]
  rw [intervalIntegral.integral_sub h1.intervalIntegrable ((continuousOn_const.mul h2).add continuousOn_const).intervalIntegrable,
    intervalIntegral.integral_add (continuousOn_const.mul h2).intervalIntegrable (continuous_const.intervalIntegrable ..),
    intervalIntegral.integral_const_mul,integral_inv_of_pos ha hR0,hInv2,intervalIntegral.integral_const,smul_eq_mul]
  dsimp only [ε]
  simp only [div_eq_mul_inv]
  nlinarith [inv_pos.mpr hR0,mul_inv_cancel₀ hR0.ne',mul_nonneg (add_nonneg ha.le hX.le) (inv_nonneg.mpr hR0.le),mul_nonneg ha.le (inv_nonneg.mpr hR0.le)]

/-- Rank-r optical lower bound under exactly the signed bounded phase
and inclusive channel inequalities in the proof. The regulator is the
actual lower endpoint ε of the proper-time integral. -/
theorem parity_proper_time_charge_log {b : ℝ → ℝ} (hb : Measurable b) {N : ℝ} (hN : ∀ v, |b v|≤N)
    {m X : ℝ} (hm : 0<m) (hX : 0<X) (r : ℕ) (hr : 1≤r)
    (hpos : ∀ S > 0, 0 ≤ parityPhaseCut b S)
    (hopt : ∀ S ≥ 4*m^2, (r:ℝ)*openingWeight (4*m^2/S)/(12*Real.pi^2) ≤ parityPhaseCut b S/(2*Real.pi^2)) :
    (∃ C:ℝ, ∀ R ≥ 4*m^2, r/(12*Real.pi^2)*Real.log (R/(4*m^2))-C ≤ parityProperCutoff b R⁻¹ X/(2*Real.pi^2)) ∧
    Tendsto (fun ε => parityProperCutoff b ε X/(2*Real.pi^2)) (𝓝[>] 0) atTop := by
  let a := 4*m^2
  have ha : 0<a := by dsimp [a]; positivity
  have hr' : 0<(r:ℝ) := by exact_mod_cast (by omega : 0<r)
  let c := (r:ℝ)/(12*Real.pi^2)
  let C := c*((a+X)/a+1)+N/(2*Real.pi^2)
  have hc : 0<c := by dsimp [c]; positivity
  have hlower (R) (hR:a≤R) : c*Real.log (R/a)-C ≤ parityProperCutoff b R⁻¹ X/(2*Real.pi^2) := by
    have hdsp := parity_dispersion_log hb hN ha hX (r := (r:ℝ)/6) (by positivity) hR hpos (fun S hS => ?_)
    · have hh := abs_le.mp (parity_phase_cutoff_comparison hb hN (inv_pos.mpr (ha.trans_le hR)) hX)
      dsimp only [C,c]
      have hp : 0 < 2*Real.pi^2 := by positivity
      apply (le_div_iff₀ hp).mpr
      have hc' : (r:ℝ)/(12*Real.pi^2)*(2*Real.pi^2)=(r:ℝ)/6 := by field_simp;ring
      have hN' : N/(2*Real.pi^2)*(2*Real.pi^2)=N := div_mul_cancel₀ _ hp.ne'
      nlinarith [congrArg (·*Real.log (R/a)) hc',congrArg (·*((a+X)/a+1)) hc']
    · have h := hopt S hS
      have h' := (div_le_div_iff₀ (by positivity) (by positivity)).mp h
      apply (le_of_mul_le_mul_right (a := 12*Real.pi^2) _ (by positivity))
      dsimp only [a]
      nlinarith only [h']
  constructor
  · exact ⟨C,hlower⟩
  · have hL : Tendsto (fun R:ℝ => Real.log (R/a)) atTop atTop := Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const ha)
    have hlarge := tendsto_atTop_add_const_right atTop (-C) (hL.const_mul_atTop hc)
    have hR : Tendsto (fun R:ℝ => parityProperCutoff b R⁻¹ X/(2*Real.pi^2)) atTop atTop := by
      apply tendsto_atTop_mono' atTop _ hlarge
      filter_upwards [eventually_ge_atTop a] with R hg
      simpa only [sub_eq_add_neg] using hlower R hg
    simpa only [Function.comp_def,inv_inv] using hR.comp tendsto_inv_nhdsGT_zero

end UV
