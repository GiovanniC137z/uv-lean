import UV.ContinueFiveBallPortalAction

/-! The optical charge logarithm with an arbitrary signed phase density.
The two cutoffs below are the actual proper-time endpoint and the cutoff
on the nonnegative physical cut, in the same locked Euclidean chart. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology

namespace UV

def parityFeynman (u : ℝ) := u*(1-u)
def parityCutWeight (a X S : ℝ) := Real.exp (-a*(S+X))/(S+X)
def parityPhaseCut (b : ℝ → ℝ) (S : ℝ) :=
  ∫ u in Ioo 0 1, parityFeynman u * b (parityFeynman u*S)

def parityProperCutoff (b : ℝ → ℝ) (ε X : ℝ) :=
  ∫ u in Ioo 0 1, parityFeynman u *
    ∫ v in Ioi 0, b v * parityCutWeight ε (parityFeynman u*X) v

def parityDispersionCutoff (b : ℝ → ℝ) (ε X : ℝ) :=
  ∫ S in Ioi 0, parityPhaseCut b S * parityCutWeight ε X S

theorem parity_feynman_bounds {u : ℝ} (hu : u ∈ Ioo 0 1) :
    0 < parityFeynman u ∧ parityFeynman u ≤ 1 := by
  dsimp [parityFeynman]
  constructor
  · exact mul_pos hu.1 (sub_pos.mpr hu.2)
  · nlinarith [sq_nonneg u,hu.2]

theorem parity_cut_weight_le_exp {a X S : ℝ} (ha : 0 ≤ a) (hX : 0<X) (hS : 0 ≤ S) :
    0 ≤ parityCutWeight a X S ∧ parityCutWeight a X S ≤ X⁻¹*Real.exp (-a*S) := by
  have hs : 0 < S+X := by linarith
  constructor
  · dsimp [parityCutWeight]; positivity
  · rw [parityCutWeight,div_eq_mul_inv,mul_comm X⁻¹]
    apply mul_le_mul (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg ha hX.le])) (inv_anti₀ hX (by linarith)) (inv_nonneg.mpr hs.le) (Real.exp_pos _).le

theorem parity_cut_weight_difference {ε X h S : ℝ} (he : 0<ε) (hX : 0<X) (hh : 0<h) (hh1 : h≤1) (hS : 0 ≤ S) :
    0 ≤ parityCutWeight (ε*h) X S - parityCutWeight ε X S ∧
    parityCutWeight (ε*h) X S - parityCutWeight ε X S ≤ ε*Real.exp (-(ε*h)*S) := by
  let z := S+X
  have hz : 0 < z := by dsimp [z]; linarith
  have hsplit : Real.exp (-(ε*h)*z)-Real.exp (-ε*z) =
      Real.exp (-(ε*h)*z)*(1-Real.exp (-(ε*(1-h)*z))) := by rw [mul_sub,mul_one,←Real.exp_add]; congr 2;ring
  change 0 ≤ Real.exp (-(ε*h)*z)/z-Real.exp (-ε*z)/z ∧ _
  simp only [parityCutWeight]
  change _ ∧ Real.exp (-(ε*h)*z)/z-Real.exp (-ε*z)/z ≤ _
  rw [←sub_div,hsplit]
  have h1 : 0 ≤ ε*(1-h)*z := mul_nonneg (mul_nonneg he.le (sub_nonneg.mpr hh1)) hz.le
  constructor
  · exact div_nonneg (mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr h1)))) hz.le
  · apply (div_le_iff₀ hz).mpr
    have hw := Real.add_one_le_exp (-(ε*(1-h)*z))
    have ha : Real.exp (-(ε*h)*z) ≤ Real.exp (-(ε*h)*S) := Real.exp_le_exp.mpr (by dsimp [z]; nlinarith [mul_nonneg (mul_nonneg he.le hh.le) hX.le])
    have hx : 1-Real.exp (-(ε*(1-h)*z)) ≤ ε*z := by nlinarith [mul_nonneg (mul_nonneg he.le hh.le) hz.le]
    exact (mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le).trans ((mul_le_mul_of_nonneg_right ha (mul_nonneg he.le hz.le)).trans_eq (by ring))

private theorem parity_weighted_integrable {b : ℝ → ℝ} (hb : Measurable b) {N : ℝ} (hN : ∀ v, |b v|≤N)
    {a X h : ℝ} (ha : 0<a) (hX : 0<X) :
    IntegrableOn (fun S => b (h*S)*parityCutWeight a X S) (Ioi 0) := by
  have hi := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0).const_mul (N*X⁻¹)
  apply hi.mono' (by dsimp only [parityCutWeight]; exact ((hb.comp (measurable_const.mul measurable_id)).mul (by fun_prop)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with S hS
  have hw := parity_cut_weight_le_exp ha.le hX hS.le
  rw [norm_mul,Real.norm_eq_abs,Real.norm_of_nonneg hw.1]
  exact (mul_le_mul (hN _) hw.2 hw.1 ((abs_nonneg (b 0)).trans (hN 0))).trans_eq (by ring)

theorem parity_phase_fibre_cutoff {b : ℝ → ℝ} (hb : Measurable b) {N : ℝ} (hN : ∀ v, |b v|≤N)
    {ε X h : ℝ} (he : 0<ε) (hX : 0<X) (hh : 0<h) (hh1 : h≤1) :
    |h*(∫ v in Ioi 0, b v*parityCutWeight ε (h*X) v) -
      h*(∫ S in Ioi 0, b (h*S)*parityCutWeight ε X S)| ≤ N := by
  let f := fun v => b v*parityCutWeight ε (h*X) v
  have hchange := integral_comp_mul_left_Ioi f 0 hh
  simp only [mul_zero,smul_eq_mul] at hchange
  have heq : (∫ v in Ioi 0, f v) = ∫ S in Ioi 0, b (h*S)*parityCutWeight (ε*h) X S := by
    rw [←show h*(∫ S in Ioi 0, f (h*S)) = ∫ v in Ioi 0, f v by rw [hchange,←mul_assoc,mul_inv_cancel₀ hh.ne',one_mul],←integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun S => ?_)
    dsimp only [f,parityCutWeight]
    rw [show h*S+h*X=h*(S+X) by ring,←mul_assoc (-ε) h (S+X),neg_mul]
    field_simp [hh.ne']
  change |h*(∫ v in Ioi 0, f v)-_| ≤ _
  rw [heq,←mul_sub,abs_mul,abs_of_pos hh,←integral_sub (parity_weighted_integrable hb hN (mul_pos he hh) hX)
    (parity_weighted_integrable hb hN he hX)]
  have hpos := (abs_nonneg (b 0)).trans (hN 0)
  have hdom := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (mul_pos he hh)) 0).const_mul (N*ε)
  have hle : |∫ S in Ioi 0, (b (h*S)*parityCutWeight (ε*h) X S-b (h*S)*parityCutWeight ε X S)| ≤
      ∫ S in Ioi 0, N*ε*Real.exp (-(ε*h)*S) := by
    rw [←Real.norm_eq_abs]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono_ae ((parity_weighted_integrable hb hN (mul_pos he hh) hX).sub (parity_weighted_integrable hb hN he hX)).norm hdom
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with S hS
    have hw := parity_cut_weight_difference he hX hh hh1 hS.le
    dsimp only [Pi.sub_apply]
    rw [←mul_sub,Real.norm_eq_abs,abs_mul,abs_of_nonneg hw.1]
    exact (mul_le_mul (hN _) hw.2 hw.1 hpos).trans_eq (by ring)
  apply (mul_le_mul_of_nonneg_left hle hh.le).trans_eq
  rw [integral_const_mul,integral_exp_mul_Ioi (neg_lt_zero.mpr (mul_pos he hh)),mul_zero,Real.exp_zero]
  field_simp

/-- Proper-time and physical-energy cutoffs differ by a uniformly
bounded amount, even when b changes sign arbitrarily often. The
normalization 1/(2π²) multiplies both sides in the physical source. -/
theorem parity_phase_cutoff_comparison {b : ℝ → ℝ} (hb : Measurable b) {N : ℝ} (hN : ∀ v, |b v|≤N)
    {ε X : ℝ} (he : 0<ε) (hX : 0<X) :
    |parityProperCutoff b ε X-parityDispersionCutoff b ε X| ≤ N := by
  let μ := volume.restrict (Ioo (0:ℝ) 1)
  let ν := volume.restrict (Ioi (0:ℝ))
  let Z := fun z:ℝ×ℝ => parityFeynman z.1*(b (parityFeynman z.1*z.2)*parityCutWeight ε X z.2)
  have N0 := (abs_nonneg (b 0)).trans (hN 0)
  have hm : Measurable Z := by dsimp [Z,parityFeynman,parityCutWeight]; fun_prop
  have hμ : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  letI := hμ
  have hd := (integrable_const (1:ℝ) (μ := μ)).mul_prod ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr he) 0).const_mul (N*X⁻¹))
  have hi : Integrable Z (μ.prod ν) := by
    apply hd.mono' hm.aestronglyMeasurable
    have had : ∀ᵐ z ∂μ.prod ν, z ∈ (Ioo (0:ℝ) 1) ×ˢ (Ioi 0) := by
      rw [ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioo.prod measurableSet_Ioi)]
      filter_upwards [ae_restrict_mem (μ := (volume:Measure ℝ)) measurableSet_Ioo] with u hu
      filter_upwards [ae_restrict_mem (μ := (volume:Measure ℝ)) measurableSet_Ioi] with S hS using ⟨hu,hS⟩
    filter_upwards [had] with z hz
    have hf := parity_feynman_bounds hz.1
    have hw := parity_cut_weight_le_exp he.le hX hz.2.le
    dsimp only [Z]
    rw [norm_mul,norm_mul,Real.norm_of_nonneg hf.1.le,Real.norm_eq_abs,Real.norm_of_nonneg hw.1,one_mul]
    exact (mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) hw.1) hf.2).trans ((mul_le_mul (hN _) hw.2 hw.1 N0).trans_eq (by ring))
  let A := fun u => parityFeynman u * ∫ v in Ioi 0, b v*parityCutWeight ε (parityFeynman u*X) v
  let D := fun u => ∫ S, Z (u,S) ∂ν
  have hid : Integrable D μ := hi.integral_prod_left
  have hA : Measurable A := by
    have h : Measurable (fun z:ℝ×ℝ => b z.2*parityCutWeight ε (parityFeynman z.1*X) z.2) := by
      dsimp [parityFeynman,parityCutWeight]; fun_prop
    exact (show Measurable (fun z:ℝ => z*(1-z)) by fun_prop).mul h.stronglyMeasurable.integral_prod_right'.measurable
  have hdiff : ∀ᵐ u ∂μ, |A u-D u| ≤ N := by
    filter_upwards [ae_restrict_mem (μ := (volume:Measure ℝ)) measurableSet_Ioo] with u hu
    have hf := parity_feynman_bounds hu
    simpa only [A,D,Z,ν,integral_const_mul] using parity_phase_fibre_cutoff hb hN he hX hf.1 hf.2
  have hiΔ : Integrable (fun u => A u-D u) μ := (integrable_const (μ := μ) N).mono' (hA.aestronglyMeasurable.sub hid.aestronglyMeasurable) hdiff
  have hiA : Integrable A μ := (hiΔ.add hid).congr (Eventually.of_forall fun u => sub_add_cancel (A u) (D u))
  have hdint : (∫ u, D u ∂μ) = parityDispersionCutoff b ε X := by
    unfold parityDispersionCutoff D
    rw [integral_integral_swap (f := fun u S => Z (u,S)) hi]
    apply integral_congr_ae (Eventually.of_forall fun S => ?_)
    simp only [Z,μ,parityPhaseCut,←mul_assoc,integral_mul_const]
  change |(∫ u, A u ∂μ)-_| ≤ _
  rw [←hdint,←integral_sub hiA hid,←Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono_ae hiΔ.norm (integrable_const (μ :=μ) N) hdiff).trans_eq
  simp [μ,Real.volume_real_Ioo]

end UV
