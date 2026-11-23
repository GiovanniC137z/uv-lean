import UV.ContinueFiveBallOpticalLog

/-! Fubini links the signed phase to the real proper-time density of
the parity-even determinant and its physical logarithmic obstruction. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology

namespace UV

def parityHeatPhase (b : ℝ → ℝ) (t : ℝ) := ∫ v in Ioi (0:ℝ), b v*Real.exp (-t*v)
def parityHeatPolarization (b : ℝ → ℝ) (X t : ℝ) :=
  (∫ u in Ioo 0 1, parityFeynman u*Real.exp (-t*(parityFeynman u*X))*(t*parityHeatPhase b t))/t

@[fun_prop] private theorem parity_heat_phase_measurable {b : ℝ → ℝ} (hb : Measurable b) : Measurable (parityHeatPhase b) := by
  have h : Measurable (fun z : ℝ×ℝ => b z.2*Real.exp (-z.1*z.2)) := by fun_prop
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem parity_laplace_resolvent_fibre {b : ℝ → ℝ} (hb : Measurable b) {N : ℝ} (hN : ∀ v, |b v|≤N)
    {ε a : ℝ} (hε : 0<ε) (ha : 0<a) :
    (∫ t in Ioi ε, Real.exp (-t*a)*parityHeatPhase b t) = ∫ v in Ioi 0, b v*parityCutWeight ε a v := by
  let τ := volume.restrict (Ioi ε)
  let ν := volume.restrict (Ioi (0:ℝ))
  let F := fun z:ℝ×ℝ => Real.exp (-z.1*a)*(b z.2*Real.exp (-z.1*z.2))
  have hm : Measurable F := by dsimp [F]; fun_prop
  have hd := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) ε).mul_prod ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hε) 0).const_mul N)
  have hi : Integrable F (τ.prod ν) := by
    apply hd.mono' hm.aestronglyMeasurable
    have hz : ∀ᵐ z ∂τ.prod ν, z ∈ Ioi ε ×ˢ Ioi 0 := by
      rw [ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioi.prod measurableSet_Ioi)]
      filter_upwards [ae_restrict_mem (μ := (volume:Measure ℝ)) measurableSet_Ioi] with t ht
      filter_upwards [ae_restrict_mem (μ := (volume:Measure ℝ)) measurableSet_Ioi] with v hv using ⟨ht,hv⟩
    filter_upwards [hz] with z hz
    have ht : ε ≤ z.1 := hz.1.le
    have hv0 : 0 ≤ z.2 := hz.2.le
    have hv : Real.exp (-z.1*z.2) ≤ Real.exp (-ε*z.2) := Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr ht) hv0])
    dsimp only [F]
    simp only [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_eq_abs,show -z.1*a= -a*z.1 by ring]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hN _) hv (Real.exp_pos _).le ((abs_nonneg (b 0)).trans (hN 0))) (Real.exp_pos _).le
  calc _ = ∫ t, ∫ v, F (t,v) ∂ν ∂τ := by simp only [τ,ν,F,parityHeatPhase,integral_const_mul]
       _ = ∫ v, ∫ t, F (t,v) ∂τ ∂ν := integral_integral_swap hi
       _ = _ := by
         apply integral_congr_ae
         filter_upwards [ae_restrict_mem (μ := (volume:Measure ℝ)) measurableSet_Ioi] with v hv
         have hf (t) : F (t,v) = b v*Real.exp (-(v+a)*t) := by
           dsimp only [F]
           rw [mul_left_comm,←Real.exp_add]
           congr 2;ring
         simp_rw [hf]
         dsimp only [τ]
         rw [integral_const_mul,integral_exp_mul_Ioi (neg_lt_zero.mpr (add_pos hv ha))]
         unfold parityCutWeight
         rw [neg_div_neg_eq,show -(v+a)*ε= -ε*(v+a) by ring]

/-- The positive spectral gap of the parity phase and its uniform
bound control all changes of integration order at the original endpoint. -/
theorem parity_heat_cutoff_eq {b : ℝ → ℝ} (hb : Measurable b) {N a ε X : ℝ} (hN : ∀ v, |b v|≤N)
    (ha : 0<a) (hgap : ∀ v∈Ioo 0 a, b v=0) (he : 0<ε) (hX : 0<X) :
    (∫ t in Ioi ε, parityHeatPolarization b X t) = parityProperCutoff b ε X := by
  let τ := volume.restrict (Ioi ε)
  let μ := volume.restrict (Ioo (0:ℝ) 1)
  let N' := N/(ε/2)
  have hC : 0 ≤ N := (abs_nonneg (b 0)).trans (hN 0)
  have hN' : 0 ≤ N' := div_nonneg hC (half_pos he).le
  have hpoint (t) (ht : ε<t) : ‖parityHeatPhase b t‖ ≤ N'*Real.exp (-(a/2)*t) := by
    let D := fun v:ℝ => (N*Real.exp (-(a/2)*t))*Real.exp (-(ε/2)*v)
    have hi := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (half_pos he)) 0).const_mul (N*Real.exp (-(a/2)*t))
    have hf : ∀ v∈Ioi (0:ℝ), ‖b v*Real.exp (-t*v)‖ ≤ D v := by
      intro v hv
      by_cases hv' : v<a
      · rw [hgap _ ⟨hv,hv'⟩,zero_mul,norm_zero]
        dsimp [D];positivity
      · have hpow : Real.exp (-t*v) ≤ Real.exp (-(a/2)*t)*Real.exp (-(ε/2)*v) := by
          rw [←Real.exp_add]
          apply Real.exp_le_exp.mpr
          nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_not_gt hv')) (he.trans ht).le, mul_nonneg (sub_nonneg.mpr ht.le) hv.le]
        rw [norm_mul,Real.norm_eq_abs,Real.norm_of_nonneg (Real.exp_pos _).le]
        exact (mul_le_mul (hN _) hpow (Real.exp_pos _).le hC).trans_eq (by dsimp [D]; ring)
    have hmeas : Measurable (fun v => b v*Real.exp (-t*v)) := hb.mul (by fun_prop)
    have hbI := hi.mono' hmeas.aestronglyMeasurable (ae_restrict_iff' measurableSet_Ioi |>.mpr (Eventually.of_forall hf))
    apply (norm_integral_le_integral_norm _).trans
    apply (integral_mono_ae hbI.norm hi (ae_restrict_iff' measurableSet_Ioi |>.mpr (Eventually.of_forall hf))).trans_eq
    rw [integral_const_mul,integral_exp_mul_Ioi (neg_lt_zero.mpr (half_pos he)),mul_zero,Real.exp_zero,neg_div_neg_eq]
    dsimp only [N'];ring
  let F := fun z:ℝ×ℝ => parityFeynman z.2*Real.exp (-z.1*(parityFeynman z.2*X))*parityHeatPhase b z.1
  have hμ : IsFiniteMeasure μ := by dsimp [μ];infer_instance
  letI := hμ
  have hmeas : Measurable F := by dsimp [F,parityFeynman];fun_prop (disch := exact parity_heat_phase_measurable hb)
  have hd := ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (half_pos ha)) ε).const_mul N').mul_prod (integrable_const (1:ℝ) (μ := μ))
  have hi : Integrable F (τ.prod μ) := by
    apply hd.mono' hmeas.aestronglyMeasurable
    have hz : ∀ᵐ z ∂τ.prod μ, z ∈ Ioi ε ×ˢ Ioo 0 1 := by
      rw [ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioi.prod measurableSet_Ioo)]
      filter_upwards [ae_restrict_mem (μ := (volume:Measure ℝ)) measurableSet_Ioi] with t ht
      filter_upwards [ae_restrict_mem (μ := (volume:Measure ℝ)) measurableSet_Ioo] with u hu using ⟨ht,hu⟩
    filter_upwards [hz] with z hz
    have hc := parity_feynman_bounds hz.2
    have hex : Real.exp (-z.1*(parityFeynman z.2*X)) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (he.trans hz.1).le) (mul_nonneg hc.1.le hX.le))
    dsimp only [F]
    simp only [norm_mul,Real.norm_of_nonneg hc.1.le,Real.norm_of_nonneg (Real.exp_pos _).le,mul_one]
    exact (mul_le_of_le_one_left (norm_nonneg _) (mul_le_one₀ hc.2 (Real.exp_pos _).le hex)).trans (hpoint _ hz.1)
  calc _ = ∫ t, ∫ u, F (t,u) ∂μ ∂τ := by
           apply integral_congr_ae
           filter_upwards [ae_restrict_mem (μ := (volume:Measure ℝ)) measurableSet_Ioi] with t ht
           have h (u) : parityFeynman u*Real.exp (-t*(parityFeynman u*X))*(t*parityHeatPhase b t) = t*F (t,u) := by dsimp [F];ring
           simp only [parityHeatPolarization,h,integral_const_mul,μ,mul_div_cancel_left₀ _ (he.trans ht).ne']
       _ = ∫ u, ∫ t, F (t,u) ∂τ ∂μ := integral_integral_swap hi
       _ = _ := by
           apply integral_congr_ae
           filter_upwards [ae_restrict_mem (μ := (volume:Measure ℝ)) measurableSet_Ioo] with u hu
           dsimp only [F,τ]
           simp_rw [mul_assoc (parityFeynman u),integral_const_mul]
           rw [parity_laplace_resolvent_fibre hb hN he (mul_pos (parity_feynman_bounds hu).1 hX)]

/-- Divergence of the cutoff integral of the actual signed heat
weight, with the manuscript's Fourier/spin normalization restored. -/
theorem parity_heat_optical_log {b : ℝ → ℝ} (hb : Measurable b) {N a m X : ℝ} (hN : ∀ v, |b v|≤N)
    (ha : 0<a) (hgap : ∀ v∈Ioo 0 a, b v=0) (hm : 0<m) (hX : 0<X) (r : ℕ) (hr : 1≤r)
    (hpos : ∀ S > 0, 0 ≤ parityPhaseCut b S)
    (hopt : ∀ S ≥ 4*m^2, (r:ℝ)*openingWeight (4*m^2/S)/(12*Real.pi^2) ≤ parityPhaseCut b S/(2*Real.pi^2)) :
    (∃ C:ℝ, ∀ R ≥ 4*m^2, r/(12*Real.pi^2)*Real.log (R/(4*m^2))-C ≤
      ∫ t in Ioi R⁻¹, parityHeatPolarization b X t/(2*Real.pi^2)) ∧
    Tendsto (fun ε => ∫ t in Ioi ε, parityHeatPolarization b X t/(2*Real.pi^2)) (𝓝[>] 0) atTop := by
  have h := parity_proper_time_charge_log hb hN hm hX r hr hpos hopt
  obtain ⟨C,hC⟩ := h.1
  have hh (ε) (he : 0<ε) : (∫ t in Ioi ε, parityHeatPolarization b X t/(2*Real.pi^2)) = parityProperCutoff b ε X/(2*Real.pi^2) := by
    rw [integral_div,parity_heat_cutoff_eq hb hN ha hgap he hX]
  constructor
  · exact ⟨C,fun R hR => (hC R hR).trans_eq (hh _ (inv_pos.mpr ((by positivity : 0<4*m^2).trans_le hR))).symm⟩
  · apply h.2.congr'
    filter_upwards [self_mem_nhdsWithin] with ε he using (hh ε he).symm

end UV
