import UV.ContinueHeatLinkBranches

/-! The nonreal poles cannot be removed by local polynomial contacts.
The comparison Cauchy transform of the squared-mass law is holomorphic
throughout the slit plane under the single Euclidean integrability condition. -/

noncomputable section

namespace UV.HeatMaxwell

open Set Real MeasureTheory Filter
open scoped Topology

private theorem heat_upper_im_strictMono {A : ℝ} (hA : 0 < A) :
    StrictMono (fun n => (heatLambertUpper n A).im) := by
  intro n m h
  have hnm : (n:ℝ)+1 ≤ (m:ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
  exact ((heatLambertUpper_spec n hA).2.2.trans_le
    (mul_le_mul_of_nonneg_right (by linarith only [hnm] : 2*(n:ℝ)+2 ≤ 2*(m:ℝ)+1) pi_pos.le)).trans
      (heatLambertUpper_spec m hA).2.1

theorem heatFreeVector_infinitely_many_nonreal_poles {m a : ℝ} (hm : 0 < m) (ha : 0 < a) :
    {z : ℂ | z.im ≠ 0 ∧ heatVectorDenominator m a z = 0 ∧
      UV.simplePoleResidue (heatFreeVector m a) z ≠ 0}.Infinite := by
  let A := 2*a^2*m^2
  have hA : 0 < A := by dsimp [A]; positivity
  let b := 2*a^2
  have hb : 0 < b := by dsimp [b]; positivity
  have hbc : (b:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  let f := fun n => -heatLambertUpper n A/(b:ℂ)
  have hinj : Function.Injective f := by
    intro n m h
    have h1 := (div_left_inj' hbc).mp h
    exact (heat_upper_im_strictMono hA).injective (congrArg Complex.im (neg_injective h1))
  apply (infinite_range_of_injective hinj).mono
  rintro _ ⟨n,rfl⟩
  have hz : heatVectorDenominator m a (f n) = 0 := by
    apply (heatFreeVector_full_pole_locus hm ha _).mpr
    exact ⟨.ofNat (n+1),by simp [f,b,A,heatLambertBranch]⟩
  have him : 0 < (heatLambertUpper n A).im := (show 0 < (2*(n:ℝ)+1)*π by positivity).trans
    (heatLambertUpper_spec n hA).2.1
  refine ⟨?_,hz,heatFreeVector_residue_ne_zero hm ha hz⟩
  simpa only [f,Complex.div_ofReal_im,Complex.neg_im] using (div_neg_of_neg_of_pos (neg_lt_zero.mpr him) hb).ne

def heatVectorStieltjes (ρ : Measure ℝ) (z : ℂ) : ℂ := ∫ s, (z+(s:ℂ))⁻¹ ∂ρ

private theorem slit_separation {p : ℂ} (hp : p.im ≠ 0 ∨ 0 < p.re) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 ≤ s → 2*δ ≤ ‖p+(s:ℂ)‖ := by
  rcases hp with hi | hr
  · refine ⟨|p.im|/2,by positivity,fun s _ => ?_⟩
    simpa only [Complex.add_im,Complex.ofReal_im,add_zero,mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] using
      Complex.abs_im_le_norm (p+(s:ℂ))
  · refine ⟨p.re/2,by positivity,fun s hs => ?_⟩
    have h : p.re ≤ (p+(s:ℂ)).re := by simp [hs]
    linarith only [h,(le_abs_self _).trans (Complex.abs_re_le_norm (p+(s:ℂ)))]

private theorem heat_stieltjes_local_bound {p z : ℂ} {δ s : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s)
    (hsep : 2*δ ≤ ‖p+(s:ℂ)‖) (hz : z ∈ Metric.ball p δ) :
    δ ≤ ‖z+(s:ℂ)‖ ∧ ‖(z+(s:ℂ))⁻¹‖ ≤ (1+(1+‖p‖+δ)/δ)*(1+s)⁻¹ := by
  have hn : ‖z-p‖ < δ := by simpa only [Metric.mem_ball,dist_eq_norm] using hz
  have htri := norm_le_norm_sub_add (p+(s:ℂ)) (z+(s:ℂ))
  rw [add_sub_add_right_eq_sub,norm_sub_rev] at htri
  have hl : δ ≤ ‖z+(s:ℂ)‖ := by linarith only [hn,hsep,htri]
  have hsz : 1+s ≤ ‖z+(s:ℂ)‖ + (1+‖p‖+δ) := by
    have hs' := norm_le_norm_sub_add (s:ℂ) (z+(s:ℂ))
    rw [show (s:ℂ)-(z+(s:ℂ)) = -z by ring, norm_neg,Complex.norm_real,Real.norm_of_nonneg hs] at hs'
    linarith only [hs',norm_le_norm_sub_add z p,hn]
  refine ⟨hl,?_⟩
  rw [norm_inv,← div_eq_mul_inv,inv_eq_one_div,div_le_div_iff₀ (hδ.trans_le hl) (by positivity : 0 < 1+s)]
  have hb : 0 ≤ (1+‖p‖+δ)/δ := by positivity
  have h := mul_le_mul_of_nonneg_left hl hb
  rw [div_mul_cancel₀ _ hδ.ne'] at h
  nlinarith only [h,hsz]

theorem heatVectorStieltjes_hasDerivAt (ρ : Measure ℝ) (hs : ∀ᵐ s ∂ρ, 0 ≤ s)
    (hi : Integrable (fun s : ℝ => (1+s)⁻¹) ρ) {p : ℂ} (hp : p.im ≠ 0 ∨ 0 < p.re) :
    HasDerivAt (heatVectorStieltjes ρ) (∫ s, -((p+(s:ℂ))⁻¹)^2 ∂ρ) p := by
  obtain ⟨δ,hδ,sep⟩ := slit_separation hp
  let C := 1+(1+‖p‖+δ)/δ
  let F := fun (z : ℂ) (s : ℝ) => (z+(s:ℂ))⁻¹
  let dF := fun (z : ℂ) (s : ℝ) => -((z+(s:ℂ))⁻¹)^2
  have hmeas (z : ℂ) : AEStronglyMeasurable (F z) ρ :=
    (measurable_const.add Complex.continuous_ofReal.measurable).inv.aestronglyMeasurable
  have hbound (s : ℝ) (hs' : 0 ≤ s) (z : ℂ) (hz : z ∈ Metric.ball p δ) :=
    heat_stieltjes_local_bound hδ hs' (sep s hs') hz
  have hI : Integrable (F p) ρ := (hi.const_mul C).mono' (hmeas p)
    (hs.mono fun s h => (hbound s h p (Metric.mem_ball_self hδ)).2)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := dF) hδ
    (Eventually.of_forall hmeas) hI ((hmeas p).pow 2).neg
    (bound := fun s : ℝ => (C*(1+s)⁻¹)*δ⁻¹) ?_ ((hi.const_mul C).mul_const _) ?_).2
  · filter_upwards [hs] with s hs' z hz
    obtain ⟨hl,hu⟩ := hbound s hs' z hz
    have htop : ‖(z+(s:ℂ))⁻¹‖ ≤ δ⁻¹ := by rw [norm_inv]; exact inv_anti₀ hδ hl
    change ‖-((z+(s:ℂ))⁻¹)^2‖ ≤ _
    rw [norm_neg,norm_pow,pow_two]
    exact mul_le_mul hu htop (norm_nonneg _) ((norm_nonneg _).trans hu)
  · filter_upwards [hs] with s hs' z hz
    have hn : z+(s:ℂ) ≠ 0 := norm_pos_iff.mp (hδ.trans_le (hbound s hs' z hz).1)
    simpa only [F,dF,id_eq,neg_div,one_div,inv_pow] using ((hasDerivAt_id z).add_const (s:ℂ)).inv hn

/-- A positive spectral coefficient with any local polynomial contact
cannot agree in a punctured neighborhood of a nonreal heat-link pole. -/
theorem heatFreeVector_no_local_spectral_contact {m a : ℝ} (hm : 0 < m) (ha : 0 < a)
    (ρ : Measure ℝ) (hs : ∀ᵐ s ∂ρ, 0 ≤ s) (hi : Integrable (fun s : ℝ => (1+s)⁻¹) ρ)
    (P : Polynomial ℂ) {p : ℂ} (hp : p.im ≠ 0) (hz : heatVectorDenominator m a p = 0) :
    ¬ heatFreeVector m a =ᶠ[𝓝[≠] p] fun z => P.eval z + heatVectorStieltjes ρ z := by
  intro he
  have hc := (P.continuousAt (a := p)).add (heatVectorStieltjes_hasDerivAt ρ hs hi (Or.inl hp)).continuousAt
  have hzero : Tendsto (fun z : ℂ => z-p) (𝓝[≠] p) (𝓝 0) := by
    simpa only [sub_self] using ((tendsto_id (x := 𝓝 p)).sub_const p).mono_left
      (nhdsWithin_le_nhds (s := {p}ᶜ))
  have h := (hzero.mul (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {p}ᶜ)))).congr'
    (he.symm.mono fun z h => congrArg ((z-p)*·) h)
  rw [zero_mul] at h
  exact (div_ne_zero (Complex.exp_ne_zero _) (heatVector_zero_simple hm ha hz))
    (tendsto_nhds_unique (heatFreeVector_residue_limit hm ha hz) h)

end UV.HeatMaxwell
