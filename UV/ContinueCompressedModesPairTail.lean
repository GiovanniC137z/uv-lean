import UV.ContinueCompressedModesPairSewing
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The actual invariant-mass integral of the Maxwell-sewn pair line.
Both linear failure in the original action and inverse-linear decay in
the magnetically completed action have nonzero limiting constants. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology

namespace UV.PairCurvature

@[fun_prop] theorem measurable_massDensity (m ℓ : ℝ) : Measurable (massDensity m ℓ) := by
  unfold massDensity openingWeight
  exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const

theorem massDensity_pos {m s : ℝ} (hm : 0<m) (hs : 4*m^2<s) (ℓ : ℝ) :
    0<massDensity m ℓ s := by
  have hs0 : 0<s := (show 0<4*m^2 by positivity).trans hs
  rw [massDensity,if_pos hs.le,openingWeight_eq_of_nonneg (by positivity)]
  exact mul_pos (div_pos (mul_pos (Real.sqrt_pos.mpr (sub_pos.mpr ((div_lt_one hs0).mpr hs))) (by positivity)) (by positivity)) (Real.exp_pos _)

private def ratio (p s : ℝ) := p / pairEnergy p s

private theorem ratio_bounds {p s : ℝ} (hp : 0<p) (hs : 0<s) :
    0≤ratio p s ∧ ratio p s≤1 := by
  have hD : 0<pairEnergy p s := Real.sqrt_pos.mpr (by positivity)
  have he : (pairEnergy p s)^2=p^2+s := Real.sq_sqrt (by positivity)
  exact ⟨div_nonneg hp.le hD.le,(div_le_one hD).mpr (by nlinarith)⟩

private theorem ratio_tendsto {s : ℝ} (hs : 0<s) :
    Tendsto (fun p : ℝ => ratio p s) atTop (𝓝 1) := by
  have h := ((tendsto_const_nhds (x := (1:ℝ))).add (((tendsto_inv_atTop_zero (𝕜 := ℝ)).pow 2).const_mul s)).sqrt
  have hh : Tendsto (fun p:ℝ => (Real.sqrt (1+s*p⁻¹^2))⁻¹) atTop (𝓝 1) := by
    simpa using h.inv₀ (by norm_num)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with p hp
  have hD : 0<pairEnergy p s := Real.sqrt_pos.mpr (by positivity)
  have he : (pairEnergy p s)^2=p^2+s := Real.sq_sqrt (by positivity)
  have hsqrt : Real.sqrt (1+s*p⁻¹^2) = pairEnergy p s/p := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg hD.le hp.le)).mpr
    field_simp
    nlinarith
  rw [hsqrt,inv_div,ratio]

private def scaledWeight (complete : Bool) (e p s : ℝ) :=
  let z := ratio p s
  if complete then e^2/4*z*(3-2*z/(1+z)) else e^2/4*(3*z*p⁻¹^2-2/s)

private theorem scaledWeight_eq (complete : Bool) (e : ℝ) {p s : ℝ}
    (hp : 0<p) (hs : 0<s) :
    scaledWeight complete e p s = (if complete then p else p⁻¹)*sewnWeight complete e p s := by
  have hd : 0<pairEnergy p s := Real.sqrt_pos.mpr (by positivity)
  have hz := (ratio_bounds hp hs).1
  cases complete
  · rw [(sewn_weight e hp hs).1]
    simp only [scaledWeight,Bool.false_eq_true,if_false,ratio]
    field_simp [hp.ne',hd.ne',hs.ne']
  · rw [(sewn_weight e hp hs).2]
    simp only [scaledWeight,if_true,ratio]
    field_simp [hd.ne',hp.ne',(add_pos hd hp).ne']

private theorem scaledWeight_limit (complete : Bool) (e : ℝ) {s : ℝ} (hs : 0<s) :
    Tendsto (fun p => scaledWeight complete e p s) atTop (𝓝 (if complete then e^2/2 else -e^2/(2*s))) := by
  have hz := ratio_tendsto hs
  cases complete
  · have h := (((hz.const_mul 3).mul (tendsto_inv_atTop_zero.pow 2)).sub_const (2/s)).const_mul (e^2/4)
    simp only [scaledWeight,Bool.false_eq_true,if_false]
    convert h using 1
    congr 1
    ring
  · have h := ((hz.const_mul (e^2/4)).mul ((tendsto_const_nhds (x := (3:ℝ))).sub
      ((hz.const_mul 2).div (hz.const_add 1) (by norm_num))))
    simp only [scaledWeight,if_true]
    convert h using 1
    congr 1
    ring

private theorem scaledWeight_bound (complete : Bool) (e : ℝ) {p s d : ℝ}
    (hp : 1<p) (hd : 0<d) (hs : d<s) :
    |scaledWeight complete e p s| ≤ e^2/4*(3+2/d) := by
  obtain ⟨hz,hz1⟩ := ratio_bounds (by linarith : 0<p) (hd.trans hs)
  have hpi : p⁻¹≤1 := (inv_le_one₀ (by linarith)).mpr hp.le
  have hpi0 : 0 ≤ p⁻¹ := inv_nonneg.mpr (by linarith)
  have hi := (sq_le_sq₀ hpi0 zero_le_one).mpr hpi
  have hs' : 2/s≤2/d := div_le_div_of_nonneg_left (by norm_num) hd hs.le
  have hs0 : 0<s := hd.trans hs
  have H : 0≤2/s := by positivity
  cases complete
  · simp only [scaledWeight,Bool.false_eq_true,if_false,abs_mul,abs_of_nonneg (show 0≤e^2/4 by positivity)]
    gcongr
    apply abs_le.mpr
    constructor
    · nlinarith [mul_nonneg hz (sq_nonneg p⁻¹)]
    · nlinarith [mul_le_mul hz1 (show p⁻¹^2≤1 by nlinarith) (sq_nonneg _) zero_le_one]
  · have H1 : 0≤2*ratio p s/(1+ratio p s) := div_nonneg (by linarith) (by linarith)
    have H2 : 2*ratio p s/(1+ratio p s)≤1 := (div_le_one (by linarith)).mpr (by linarith)
    simp only [scaledWeight,if_true,abs_mul,abs_of_nonneg (show 0≤e^2/4 by positivity),abs_of_nonneg hz,abs_of_nonneg (show 0 ≤ 3-2*ratio p s/(1+ratio p s) by linarith)]
    rw [mul_assoc]
    gcongr
    nlinarith [mul_le_mul hz1 (show 3-2*ratio p s/(1+ratio p s)≤3 by linarith) (by linarith) zero_le_one]

def massResponse (complete : Bool) (e m ℓ p : ℝ) :=
  ∫ s in Ioi (4*m^2), sewnWeight complete e p s * massDensity m ℓ s

theorem massResponse_limit (complete : Bool) {m ℓ : ℝ} (hm : 0<m) (hℓ : 0<ℓ) (e : ℝ) :
    Tendsto (fun p => (if complete then p else p⁻¹)*massResponse complete e m ℓ p) atTop
      (𝓝 (∫ s in Ioi (4*m^2), (if complete then e^2/2 else -e^2/(2*s))*massDensity m ℓ s)) := by
  let d := 4*m^2
  have hd : 0<d := by dsimp [d]; positivity
  let f := fun (p s : ℝ) => scaledWeight complete e p s*massDensity m ℓ s
  have h := tendsto_integral_filter_of_dominated_convergence (l := (atTop : Filter ℝ)) (μ := volume.restrict (Ioi d))
    (F := f) (f := fun s => (if complete then e^2/2 else -e^2/(2*s))*massDensity m ℓ s)
    (fun s => (e^2/4*(3+2/d))*massDensity m ℓ s)
  apply Tendsto.congr' _ (h ?_ ?_ ?_ ?_)
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with p hp
    rw [massResponse,←integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    dsimp only [f]
    rw [scaledWeight_eq complete e hp (hd.trans hs),mul_assoc]
  · exact Eventually.of_forall fun p => by
      dsimp [f,scaledWeight,ratio,pairEnergy]; cases complete <;> simp <;> fun_prop
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with p hp
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    dsimp only [f]
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (massDensity_nonneg ..)]
    exact mul_le_mul_of_nonneg_right (scaledWeight_bound complete e hp hd hs) (massDensity_nonneg ..)
  · exact ((massDensity_integrable m hℓ).const_mul _).integrableOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (scaledWeight_limit complete e (hd.trans hs)).mul_const _

private def limitMagnitude (complete : Bool) (e m ℓ : ℝ) :=
  ∫ s in Ioi (4*m^2), (if complete then e^2/2 else e^2/(2*s))*massDensity m ℓ s

private theorem limitMagnitude_pos (complete : Bool) {e m ℓ : ℝ}
    (he : e≠0) (hm : 0<m) (hℓ : 0<ℓ) : 0<limitMagnitude complete e m ℓ := by
  let d := 4*m^2
  have hd : 0<d := by dsimp [d]; positivity
  let f := fun s : ℝ => (if complete then e^2/2 else e^2/(2*s))*massDensity m ℓ s
  have hpos (s : ℝ) (hs : s∈Ioi d) : 0<f s := by
    have hs' : 0<s := hd.trans hs
    have hρ := massDensity_pos hm hs ℓ
    dsimp [f]
    cases complete <;> simp <;> positivity
  have hI : IntegrableOn f (Ioi d) := by
    apply (((massDensity_integrable m hℓ).const_mul (e^2/2+e^2/(2*d))).integrableOn).mono'
    · dsimp [f]; cases complete <;> simp <;> fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      rw [Real.norm_of_nonneg (hpos s hs).le]
      dsimp [f]
      refine mul_le_mul_of_nonneg_right ?_ (massDensity_nonneg ..)
      cases complete
      · simp only [Bool.false_eq_true,if_false]
        have h := div_le_div_of_nonneg_left (sq_nonneg e) (show 0<2*d by positivity)
          (show 2*d ≤ 2*s by linarith [show d<s from hs])
        linarith [sq_nonneg e]
      · simp; positivity
  apply (setIntegral_pos_iff_support_of_nonneg_ae (Eventually.mono (ae_restrict_mem measurableSet_Ioi)
    (fun s hs => (hpos s hs).le)) hI).mpr
  apply lt_of_lt_of_le (show 0<volume (Ioo d (d+1)) by simp [Real.volume_Ioo])
  exact measure_mono (fun s hs => ⟨(hpos s hs.1).ne',hs.1⟩)

/-- The radial spatial measure costs p². Its absolute density is eventually
bounded below by a positive multiple of p³ (bare) or p (completed). -/
theorem radial_power_obstruction (complete : Bool) {e m ℓ : ℝ} (he : e≠0)
    (hm : 0<m) (hℓ : 0<ℓ) : ∃ c:ℝ, 0<c ∧
    ∀ᶠ p:ℝ in atTop, c*(if complete then p else p^3) ≤ p^2*|massResponse complete e m ℓ p| := by
  let C := limitMagnitude complete e m ℓ
  have hC : 0<C := limitMagnitude_pos complete he hm hℓ
  have h := (massResponse_limit complete hm hℓ e).abs
  have heq : |∫ s in Ioi (4*m^2), (if complete then e^2/2 else -e^2/(2*s))*massDensity m ℓ s| = C := by
    cases complete
    · simp only [Bool.false_eq_true,if_false,neg_div,neg_mul,integral_neg,abs_neg]
      exact abs_of_pos hC
    · exact abs_of_pos hC
  rw [heq] at h
  refine ⟨C/2,by positivity,?_⟩
  filter_upwards [h.eventually_const_lt (show C/2<C by linarith), eventually_gt_atTop (1:ℝ)] with p h hp
  have hp0 : 0<p := by linarith
  rw [abs_mul] at h
  cases complete
  · simp only [Bool.false_eq_true,if_false,abs_inv,abs_of_pos hp0] at h ⊢
    have hh := mul_le_mul_of_nonneg_right h.le (show 0≤p^3 by positivity)
    convert hh using 1
    field_simp
  · simp only [if_true,abs_of_pos hp0] at h ⊢
    nlinarith [mul_le_mul_of_nonneg_right h.le hp0.le]

theorem vacuum_radial_not_integrable (complete : Bool) {e m ℓ : ℝ}
    (he : e≠0) (hm : 0<m) (hℓ : 0<ℓ) (R : ℝ) :
    ¬IntegrableOn (fun p:ℝ => p^2*massResponse complete e m ℓ p) (Ioi R) := by
  obtain ⟨c,hc,h⟩ := radial_power_obstruction complete he hm hℓ
  obtain ⟨b,hb⟩ := eventually_atTop.1 h
  let T := max (max b R) 1
  have hbT : b≤T := (le_max_left b R).trans (le_max_left ..)
  have hRT : R≤T := (le_max_right b R).trans (le_max_left ..)
  intro hInt
  have hconst : IntegrableOn (fun _ : ℝ => c) (Ioi T) := by
    apply (hInt.mono_set (Ioi_subset_Ioi hRT)).norm.mono' aestronglyMeasurable_const
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    have hT : T<p := hp
    have hp1 : 1≤p := (le_max_right _ _).trans hT.le
    have hpow : 1≤(if complete then p else p^3) := by
      cases complete
      · exact one_le_pow₀ hp1
      · exact hp1
    rw [Real.norm_eq_abs,abs_of_pos hc]
    calc c ≤ c*(if complete then p else p^3) := le_mul_of_one_le_right hc.le hpow
      _ ≤ p^2*|massResponse complete e m ℓ p| := hb p (hbT.trans hT.le)
      _ = ‖p^2*massResponse complete e m ℓ p‖ := by rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg p)]
  simp [integrableOn_const_iff,Real.volume_Ioi,hc.ne'] at hconst

end UV.PairCurvature
