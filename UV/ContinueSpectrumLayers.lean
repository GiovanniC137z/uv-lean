import UV.ContinueSpectrumOscillatory
import UV.ResumeSpectrumMeasure

/-! The atom and oscillatory continuum represent the literal positive
boundary--layer Green block. No Stieltjes representation is assumed. -/

noncomputable section
open MeasureTheory Real Filter Set
open scoped Topology

namespace UV.RevisionSpectrum

def continueBoundaryLayerDensity (β b M₂ r s : ℝ) : ℝ :=
  bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s) *
    normalMode β (Real.sqrt (s-M₂)) (b-s) r

theorem continue_normalMode_bound {β k r : ℝ} (hβ : 0<β) (hk : 0<k) (hr : 0≤r) (t : ℝ) :
    |normalMode β k t r| ≤ 1+|t| *r/β := by
  unfold normalMode
  calc
    _ ≤ |Real.cos (k*r)|+|t/(β*k)*Real.sin (k*r)| := abs_add_le _ _
    _ = |Real.cos (k*r)|+(|t|/(β*k))*|Real.sin (k*r)| := by
      rw [abs_mul,abs_div,abs_of_pos (mul_pos hβ hk)]
    _ ≤ 1+(|t|/(β*k))*(k*r) := by
      apply add_le_add (Real.abs_cos_le_one _)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [abs_of_nonneg (mul_nonneg hk.le hr)] using Real.abs_sin_le_abs (x:=k*r)
    _ = _ := by field_simp

theorem continue_boundary_layer_integrable {β b M₂ x r : ℝ}
    (hβ : 0<β) (hb₀ : 0<b) (hb : b<M₂) (hx : 0<x) (hr : 0≤r) :
    IntegrableOn (fun s => continueBoundaryLayerDensity β b M₂ r s/(x+s)) (Ioi M₂) := by
  apply ((bulkBoundary_mass hβ hb).1.mul_const (1/x+r/β)).mono'
  · exact (by unfold continueBoundaryLayerDensity bulkBoundaryDensity normalMode; fun_prop :
      Measurable (fun s => continueBoundaryLayerDensity β b M₂ r s/(x+s))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hsM : M₂<s := hs
    have hs₀ : 0<s := hb₀.trans (hb.trans hsM)
    have hk : 0<Real.sqrt (s-M₂) := Real.sqrt_pos.mpr (sub_pos.mpr hsM)
    have hρ : 0≤bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s) := by unfold bulkBoundaryDensity; positivity
    rw [Real.norm_eq_abs,continueBoundaryLayerDensity,abs_div,abs_mul,abs_of_nonneg hρ,
      abs_of_pos (add_pos hx hs₀)]
    have hm := continue_normalMode_bound hβ hk hr (b-s)
    rw [abs_of_neg (by linarith : b-s<0),neg_sub] at hm
    have hratio : |normalMode β (Real.sqrt (s-M₂)) (b-s) r|/(x+s)≤1/x+r/β := by
      calc
        _ ≤ (1+(s-b)*r/β)/(x+s) := div_le_div_of_nonneg_right hm (by positivity)
        _ = (x+s)⁻¹+((s-b)/(x+s))*(r/β) := by ring
        _ ≤ x⁻¹+1*(r/β) := by
          apply add_le_add (inv_anti₀ hx (by linarith))
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact (div_le_one (by positivity : 0<x+s)).mpr (by linarith)
        _ = _ := by ring
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hratio hρ

/-- The exact normal-momentum partial fractions, kept as four integrable
oscillatory pairs so no conditionally integrable summand is introduced. -/
theorem continue_boundary_layer_normal_identity {β b M₂ x : ℝ}
    (hβ : 0<β) (hb₀ : 0<b) (hb : b<M₂) (hx : 0<x) (r : ℝ) {k : ℝ} (hk : 0<k) :
    let u := bulkKappa β b M₂
    let v := u+β
    let w := Real.sqrt (x+M₂)
    (2*k)*(continueBoundaryLayerDensity β b M₂ r (k^2+M₂)/(x+(k^2+M₂))) =
      (2/(Real.pi*(u+v))) *
        (v^2*(Real.cos (r*k)*((k^2+v^2)⁻¹*(k^2+w^2)⁻¹)) -
          u^2*(Real.cos (r*k)*((k^2+u^2)⁻¹*(k^2+w^2)⁻¹)) -
          u*(k*Real.sin (r*k)*((k^2+u^2)⁻¹*(k^2+w^2)⁻¹)) -
          v*(k*Real.sin (r*k)*((k^2+v^2)⁻¹*(k^2+w^2)⁻¹))) := by
  dsimp only
  let u := bulkKappa β b M₂
  let v := u+β
  let w := Real.sqrt (x+M₂)
  have hu : 0<u := bulkKappa_pos hβ hb
  have hv : 0<v := by dsimp [v]; positivity
  have hw : 0<w := Real.sqrt_pos.mpr (by have := hb₀.trans hb; positivity)
  have hq : u*v=M₂-b := by dsimp [u,v]; nlinarith [bulkKappa_sq_add (β:=β) hb]
  have ht : b-(k^2+M₂)=-(k^2+u*v) := by linarith
  have hw2 : w^2=x+M₂ := Real.sq_sqrt (by have := hb₀.trans hb; positivity)
  have hsplit : (b-(k^2+M₂))^2+(β*k)^2=(k^2+u^2)*(k^2+v^2) := by
    rw [ht]
    dsimp [v]
    ring
  change (2*k)*(continueBoundaryLayerDensity β b M₂ r (k^2+M₂)/(x+(k^2+M₂))) =
    (2/(Real.pi*(u+v))) * _
  unfold continueBoundaryLayerDensity
  rw [show k^2+M₂-M₂=k^2 by ring,Real.sqrt_sq hk.le]
  unfold bulkBoundaryDensity normalMode
  rw [hsplit,ht,show x+(k^2+M₂)=k^2+w^2 by linarith,mul_comm k r]
  have h₁ : k^2+u^2≠0 := by positivity
  have h₂ : k^2+v^2≠0 := by positivity
  have h₃ : k^2+w^2≠0 := by positivity
  have h₄ : u+v≠0 := by positivity
  field_simp
  dsimp [v]
  ring

theorem continue_boundary_layer_noncoincident {β b M₂ x r : ℝ}
    (hβ : 0<β) (hb₀ : 0<b) (hb : b<M₂) (hx : 0<x) (hr : 0<r)
    (hvw : bulkKappa β b M₂+β≠Real.sqrt (x+M₂)) :
    bulkResidue β b M₂*Real.exp (-r*bulkKappa β b M₂)/(x+bulkPole β b M₂) +
      (∫ s : ℝ in Ioi M₂,continueBoundaryLayerDensity β b M₂ r s/(x+s)) =
      Real.exp (-r*Real.sqrt (x+M₂))/(x+b+β*Real.sqrt (x+M₂)) := by
  let u := bulkKappa β b M₂
  let v := u+β
  let w := Real.sqrt (x+M₂)
  have hu : 0<u := bulkKappa_pos hβ hb
  have hv : 0<v := by dsimp [v]; positivity
  have hM : 0<M₂ := hb₀.trans hb
  have hw : 0<w := Real.sqrt_pos.mpr (by positivity)
  have hw2 : w^2=x+M₂ := Real.sq_sqrt (by positivity)
  have hq : u^2+β*u=M₂-b := bulkKappa_sq_add hb
  have hup : u<w := by
    have hp := (bulkPole_unique hβ hb).1
    unfold bulkPole at hp
    change b<M₂-u^2 at hp
    nlinarith
  have huw : u≠w := hup.ne
  have hvw' : v≠w := hvw
  have hcv := continuePairCos_integrable hv hw r
  have hcu := continuePairCos_integrable hu hw r
  have hsu := continuePairSin_integrable hu hw r
  have hsv := continuePairSin_integrable hv hw r
  have hI : (∫ s : ℝ in Ioi M₂,continueBoundaryLayerDensity β b M₂ r s/(x+s)) =
      (2/(Real.pi*(u+v))) *
        (v^2*continuePairCos v w r-u^2*continuePairCos u w r-
          u*(∫ k : ℝ in Ioi 0,k*Real.sin (r*k)*((k^2+u^2)⁻¹*(k^2+w^2)⁻¹))-
          v*(∫ k : ℝ in Ioi 0,k*Real.sin (r*k)*((k^2+v^2)⁻¹*(k^2+w^2)⁻¹))) := by
    rw [resume_bulk_spectral_substitution]
    have he := setIntegral_congr_fun (μ:=volume) measurableSet_Ioi
      (fun k hk => continue_boundary_layer_normal_identity hβ hb₀ hb hx r (mem_Ioi.mp hk))
    rw [he,integral_const_mul]
    change (2/(Real.pi*(u+v)))*(∫ k : ℝ in Ioi 0,
      v^2*(Real.cos (r*k)*((k^2+v^2)⁻¹*(k^2+w^2)⁻¹)) -
      u^2*(Real.cos (r*k)*((k^2+u^2)⁻¹*(k^2+w^2)⁻¹)) -
      u*(k*Real.sin (r*k)*((k^2+u^2)⁻¹*(k^2+w^2)⁻¹)) -
      v*(k*Real.sin (r*k)*((k^2+v^2)⁻¹*(k^2+w^2)⁻¹))) = _
    congr 1
    have h12 : IntegrableOn (fun k : ℝ =>
      v^2*(Real.cos (r*k)*((k^2+v^2)⁻¹*(k^2+w^2)⁻¹)) -
      u^2*(Real.cos (r*k)*((k^2+u^2)⁻¹*(k^2+w^2)⁻¹))) (Ioi 0) :=
      (hcv.const_mul (v^2)).sub (hcu.const_mul (u^2))
    have h123 : IntegrableOn (fun k : ℝ =>
      v^2*(Real.cos (r*k)*((k^2+v^2)⁻¹*(k^2+w^2)⁻¹)) -
      u^2*(Real.cos (r*k)*((k^2+u^2)⁻¹*(k^2+w^2)⁻¹)) -
      u*(k*Real.sin (r*k)*((k^2+u^2)⁻¹*(k^2+w^2)⁻¹))) (Ioi 0) := h12.sub (hsu.const_mul u)
    rw [integral_sub h123 (hsv.const_mul v),integral_sub h12 (hsu.const_mul u),
      integral_sub (hcv.const_mul (v^2)) (hcu.const_mul (u^2))]
    simp only [integral_const_mul,continuePairCos]
  have hZ : bulkResidue β b M₂=2*u/(u+v) := by
    unfold bulkResidue
    change (1+β/(2*u))⁻¹=2*u/(u+v)
    have hd : 1+β/(2*u)≠0 := by positivity
    dsimp [v]
    field_simp
    ring
  have hpole : x+bulkPole β b M₂=(w-u)*(w+u) := by unfold bulkPole; change x+(M₂-u^2)=_; nlinarith
  have hden : x+b+β*w=(w-u)*(w+v) := by dsimp [v]; nlinarith
  rw [hI,continuePairCos_formula hv hw hvw' r,continuePairCos_formula hu hw huw r,
    continuePairSin_formula hu hw huw hr,continuePairSin_formula hv hw hvw' hr,
    abs_of_pos hr,hZ,hpole]
  change (2*u/(u+v))*Real.exp (-r*u)/((w-u)*(w+u)) + _ = Real.exp (-r*w)/(x+b+β*w)
  rw [hden]
  have hd₁ : w^2-u^2≠0 := by nlinarith [sq_nonneg (w+u)]
  have hd₂ : w^2-v^2≠0 := by intro hz; exact hvw' ((sq_eq_sq₀ hw.le hv.le).mp (sub_eq_zero.mp hz)).symm
  have hd₃ : w-u≠0 := sub_ne_zero.mpr hup.ne'
  have hd₄ : w+u≠0 := by positivity
  have hd₅ : w+v≠0 := by positivity
  have hd₆ : u+v≠0 := by positivity
  field_simp
  simp_rw [mul_comm _ r]
  ring

theorem continue_boundary_layer_shift_limit {β b M₂ x r : ℝ}
    (hβ : 0<β) (hb₀ : 0<b) (hb : b<M₂) (hx : 0<x) (hr : 0≤r) :
    Tendsto (fun n : ℕ => ∫ s : ℝ in Ioi M₂,
      continueBoundaryLayerDensity β b M₂ r s/(x+1/((n:ℝ)+1)+s)) atTop
      (𝓝 (∫ s : ℝ in Ioi M₂,continueBoundaryLayerDensity β b M₂ r s/(x+s))) := by
  have hi := continue_boundary_layer_integrable hβ hb₀ hb hx hr
  apply tendsto_integral_of_dominated_convergence (μ:=volume.restrict (Ioi M₂))
    (fun s => ‖continueBoundaryLayerDensity β b M₂ r s/(x+s)‖)
  · intro n
    exact (by unfold continueBoundaryLayerDensity bulkBoundaryDensity normalMode; fun_prop :
      Measurable (fun s => continueBoundaryLayerDensity β b M₂ r s/(x+1/((n:ℝ)+1)+s))).aestronglyMeasurable
  · exact hi.norm
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0<s := hb₀.trans (hb.trans hs)
    simp only [Real.norm_eq_abs,abs_div,abs_of_pos (by positivity : 0<x+1/((n:ℝ)+1)+s),
      abs_of_pos (add_pos hx hs₀)]
    apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
    have hh : 0≤1/((n:ℝ)+1) := by positivity
    linarith
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0<s := hb₀.trans (hb.trans hs)
    have ht : Tendsto (fun n : ℕ => x+1/((n:ℝ)+1)+s) atTop (𝓝 (x+s)) := by
      simpa using (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).add_const s
    exact tendsto_const_nhds.div ht (by positivity)

/-- Exact boundary--layer Stieltjes identity for every nonnegative sampled
depth, including the coincident rational factor by an actual dominated limit. -/
theorem continue_boundary_layer_stieltjes {β b M₂ x r : ℝ}
    (hβ : 0<β) (hb₀ : 0<b) (hb : b<M₂) (hx : 0<x) (hr : 0≤r) :
    IntegrableOn (fun s => continueBoundaryLayerDensity β b M₂ r s/(x+s)) (Ioi M₂) ∧
    bulkResidue β b M₂*Real.exp (-r*bulkKappa β b M₂)/(x+bulkPole β b M₂) +
      (∫ s : ℝ in Ioi M₂,continueBoundaryLayerDensity β b M₂ r s/(x+s)) =
      Real.exp (-r*Real.sqrt (x+M₂))/(x+b+β*Real.sqrt (x+M₂)) := by
  refine ⟨continue_boundary_layer_integrable hβ hb₀ hb hx hr,?_⟩
  by_cases hr0 : r=0
  · subst r
    simpa only [continueBoundaryLayerDensity,normalMode,mul_zero,Real.cos_zero,Real.sin_zero,
      add_zero,mul_one,zero_mul,neg_zero,Real.exp_zero,one_div] using
      (resume_bulk_boundary_stieltjes hβ hb₀ hb hx).2
  have hrp : 0<r := lt_of_le_of_ne hr (Ne.symm hr0)
  by_cases hco : bulkKappa β b M₂+β=Real.sqrt (x+M₂)
  · let xn := fun n : ℕ => x+1/((n:ℝ)+1)
    have hxn : Tendsto xn atTop (𝓝 x) := by
      simpa [xn] using tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    have hxp (n : ℕ) : 0<xn n := by dsimp [xn]; positivity
    have hM : 0<M₂ := hb₀.trans hb
    have hne (n : ℕ) : bulkKappa β b M₂+β≠Real.sqrt (xn n+M₂) := by
      intro heq
      have hs := Real.sq_sqrt (show 0≤xn n+M₂ by positivity)
      have hs' := Real.sq_sqrt (show 0≤x+M₂ by positivity)
      rw [← heq] at hs
      rw [← hco] at hs'
      have he : xn n=x := by linarith
      have hh : 0<1/((n:ℝ)+1) := by positivity
      dsimp [xn] at he
      linarith
    have hZ : Tendsto (fun _ : ℕ => bulkResidue β b M₂*Real.exp (-r*bulkKappa β b M₂))
        atTop (𝓝 (bulkResidue β b M₂*Real.exp (-r*bulkKappa β b M₂))) := tendsto_const_nhds
    have hL := (hZ.div (hxn.add_const (bulkPole β b M₂))
      (show x+bulkPole β b M₂≠0 by exact (add_pos hx (hb₀.trans (bulkPole_unique hβ hb).1)).ne')).add
        (continue_boundary_layer_shift_limit hβ hb₀ hb hx hr)
    have hS := Real.continuous_sqrt.continuousAt.tendsto.comp (hxn.add_const M₂)
    have hR : Tendsto (fun n => Real.exp (-r*Real.sqrt (xn n+M₂))/
        (xn n+b+β*Real.sqrt (xn n+M₂))) atTop
        (𝓝 (Real.exp (-r*Real.sqrt (x+M₂))/(x+b+β*Real.sqrt (x+M₂)))) := by
      exact ((Real.continuous_exp.continuousAt.tendsto).comp (hS.const_mul (-r))).div
        ((hxn.add_const b).add (tendsto_const_nhds.mul hS))
        (show x+b+β*Real.sqrt (x+M₂)≠0 by positivity)
    apply tendsto_nhds_unique hL
    apply hR.congr'
    exact Eventually.of_forall fun n =>
      (continue_boundary_layer_noncoincident hβ hb₀ hb (hxp n) hrp (hne n)).symm
  · exact continue_boundary_layer_noncoincident hβ hb₀ hb hx hrp hco

end UV.RevisionSpectrum
