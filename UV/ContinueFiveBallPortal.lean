import UV.RevisionOpening
import UV.ExtendOpticalSpectralMatch
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! The two-connection portal on a fixed sector-plane. Positive squared
Euclidean transfer and the crossed-pair invariant appear in different
multipliers. Electric coefficients here have their common e² removed. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology

namespace UV

def portalEuclidean (b X : ℝ) := b/(X+b)

def portalPairCut (m b s : ℝ) := if 4*m^2 ≤ s then
  (b^2/(s-b)^2)*openingWeight (4*m^2/s)/(12*Real.pi^2) else 0

theorem portal_source_square {b X : ℝ} (hb : 0 < b) (hX : 0 < X) (A B : ℝ) :
    X*B^2+b*(B-A)^2 = (X+b)*(B-portalEuclidean b X*A)^2+X*portalEuclidean b X*A^2 := by
  unfold portalEuclidean
  field_simp [show X+b≠0 by positivity]
  ring

theorem portal_laplace {b X : ℝ} (hb : 0 < b) (hX : 0 ≤ X) :
    (∫ u in Ioi (0:ℝ), b*Real.exp (-b*u)*Real.exp (-u*X)) = portalEuclidean b X := by
  have h (u:ℝ) : b*Real.exp (-b*u)*Real.exp (-u*X) = b*Real.exp ((-(X+b))*u) := by
    rw [mul_assoc,←Real.exp_add]
    congr 2
    ring
  simp_rw [h]
  rw [integral_const_mul,integral_exp_mul_Ioi (by linarith),mul_zero,Real.exp_zero,portalEuclidean]
  rw [neg_div_neg_eq,one_div,div_eq_mul_inv]

/-- The measured one-pair density vanishes below threshold and its
unsubtracted dispersion integral converges with the below-threshold
portal pole kept at its actual mass. -/
theorem portal_cut_integrable {m b : ℝ} (hm : 0 < m) (hb : 0 < b) (ht : b < 4*m^2) :
    (∀ s < 4*m^2, portalPairCut m b s=0) ∧
    IntegrableOn (fun s => portalPairCut m b s/s) (Ioi (4*m^2)) := by
  refine ⟨fun s hs => if_neg (not_le.mpr hs),?_⟩
  let d := 4*m^2
  let c := 1-b/d
  have hd : 0 < d := by dsimp [d]; positivity
  have hc : 0 < c := by dsimp [c]; rw [sub_pos,div_lt_one hd]; exact ht
  have hmz : Measurable (fun s => portalPairCut m b s/s) := by
    unfold portalPairCut openingWeight
    exact (Measurable.ite measurableSet_Ici (by fun_prop) measurable_const).div measurable_id
  let C := b^2*(3/2)/(12*Real.pi^2*c^2)
  have hI : IntegrableOn (fun s:ℝ => C*(s^3)⁻¹) (Ioi d) := by
    have h := (integrableOn_Ioi_rpow_iff hd).mpr (show (-3:ℝ)< -1 by norm_num)
    apply (h.const_mul C).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [show (-3:ℝ) = -(3:ℕ) by norm_num,Real.rpow_neg (hd.trans hs).le,Real.rpow_natCast]
  apply hI.mono' hmz.aestronglyMeasurable
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun s hs => ?_
  have hs0 : 0 < s := hd.trans hs
  have hs1 : 0 < s-b := by linarith [show d < s from hs,show b<d from ht]
  have hden : c*s ≤ s-b := by
    dsimp only [c]
    have h := mul_le_mul_of_nonneg_right hs.le (div_nonneg hb.le hd.le)
    rw [mul_comm d _,div_mul_cancel₀ _ hd.ne'] at h
    linarith
  have ho := openingWeight_nonneg (4*m^2/s)
  rw [portalPairCut,if_pos hs.le,Real.norm_of_nonneg (by positivity)]
  change _ ≤ C*(s^3)⁻¹
  dsimp only [C]
  have hπ : 0 < 12*Real.pi^2 := by positivity
  calc _ ≤ (b^2/(s-b)^2)*(3/2)/(12*Real.pi^2)/s := by
             gcongr
             exact openingWeight_le _
       _ ≤ _ := by
             rw [←div_eq_mul_inv]
             field_simp [hπ.ne',hs0.ne',hc.ne',hs1.ne']
             have hsq := pow_le_pow_left₀ (mul_nonneg hc.le hs0.le) hden 2
             nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg b)]

def portalMark (z : ℝ) := ∫ v in (0:ℝ)..1, v*(1-v)*Real.exp (-z*(v*(1-v)))

def portalSpinMark (z : ℝ) := ∫ v in (0:ℝ)..1, Real.exp (-z*(v*(1-v)))

theorem portal_mark_zero : portalMark 0=1/6 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1) (f := fun v:ℝ => v^2/2-v^3/3)
    (f' := fun v:ℝ => v*(1-v)) (fun v _ => by
      convert (((hasDerivAt_id v).pow 2).div_const 2).sub (((hasDerivAt_id v).pow 3).div_const 3) using 1
      dsimp
      ring)
    (by apply Continuous.intervalIntegrable; fun_prop)
  norm_num [portalMark] at h ⊢
  linarith

@[fun_prop] theorem portal_mark_continuous : Continuous portalMark := by
  unfold portalMark
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  dsimp only [Function.uncurry]
  fun_prop

/-- Spin, orbital and direct-contact contributions on the common
positive proper-time slice. -/
theorem portal_mark_contact {z : ℝ} (hz : z≠0) :
    portalSpinMark z + 2*(portalSpinMark z-1)/z = 4*portalMark z := by
  let F := fun v:ℝ => Real.exp (-z*(v*(1-v)))
  let G := fun v:ℝ => (1-2*v)*F v
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hD (v:ℝ) : HasDerivAt G ((-2-z)*F v+4*z*(v*(1-v)*F v)) v := by
    dsimp [G,F]
    convert (((hasDerivAt_const v (1:ℝ)).sub ((hasDerivAt_id v).const_mul 2)).mul
      ((((hasDerivAt_id v).mul ((hasDerivAt_const v (1:ℝ)).sub (hasDerivAt_id v))).const_mul (-z)).exp)) using 1
    dsimp
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1) (fun v _ => hD v)
    (by apply Continuous.intervalIntegrable; fun_prop)
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at h
  change (-2-z)*portalSpinMark z+4*z*portalMark z = G 1-G 0 at h
  norm_num [G,F] at h
  field_simp
  linarith

def portalBare (m b X t : ℝ) := (portalEuclidean b X)^2 / (2*Real.pi^2) *
  Real.exp (-t*m^2) * portalMark (t*X) / t

theorem portal_bare_log_coefficient (m b X : ℝ) :
    Tendsto (fun t => t*portalBare m b X t) (𝓝[>] 0) (𝓝 ((portalEuclidean b X)^2/(12*Real.pi^2))) := by
  have h : Continuous (fun t:ℝ => (portalEuclidean b X)^2/(2*Real.pi^2)*Real.exp (-t*m^2)*portalMark (t*X)) := by
    fun_prop (disch := exact portal_mark_continuous)
  have hh := (h.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simp only [neg_zero,zero_mul,Real.exp_zero,mul_one,portal_mark_zero] at hh
  convert hh.congr' (f₂ := fun t => t*portalBare m b X t) ?_ using 2
  · ring
  · filter_upwards [self_mem_nhdsWithin] with t ht
    dsimp only [portalBare]
    field_simp [show t≠0 from ne_of_gt ht]

/-- Contraction of the centered fluctuation is independent of the
external source. Subtracting the free vacuum leaves precisely two
powers of the same Euclidean transfer on each transverse mode. -/
theorem portal_quadratic_contraction {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : Ω → ℝ) (hz : Integrable z μ) (hz2 : Integrable (fun ω => z ω^2) μ) (hmean : ∫ ω, z ω ∂μ=0)
    (A b X : ℝ) :
    (∫ ω, (portalEuclidean b X*A+z ω)^2 ∂μ) - (∫ ω, z ω^2 ∂μ) = (portalEuclidean b X)^2*A^2 := by
  let a := portalEuclidean b X*A
  have hh (ω) : (a+z ω)^2 = (a^2+(2*a)*z ω)+z ω^2 := by ring
  change (∫ ω, (a+z ω)^2 ∂μ)-_=_
  simp_rw [hh]
  have h₁ : Integrable (fun ω => 2*a*z ω) μ := hz.const_mul _
  have h₂ : Integrable (fun ω => a^2+2*a*z ω) μ := (integrable_const _).add h₁
  rw [integral_add h₂ hz2,integral_add (integrable_const _) h₁,
    integral_const_mul,hmean,mul_zero,add_zero,add_sub_cancel_right,integral_const,measureReal_univ_eq_one,one_smul]
  exact mul_pow _ _ _

/-- At each nonzero Euclidean momentum the full coefficient diverges
logarithmically even on an arbitrarily short proper-time interval.
No energy-shell singularity is involved in this divergence. -/
theorem portal_bare_nonintegrable (m : ℝ) {b X δ : ℝ} (hb : 0 < b) (hX : 0 < X) (hδ : 0 < δ) :
    ¬ IntegrableOn (portalBare m b X) (Ioo 0 δ) := by
  let c := (portalEuclidean b X)^2/(12*Real.pi^2)
  have hc : 0 < c := by dsimp [c,portalEuclidean]; positivity
  have hl := (portal_bare_log_coefficient m b X).eventually (lt_mem_nhds (half_lt_self hc))
  obtain ⟨d,hd,hnear⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hl.and (Ioo_mem_nhdsGT hδ))
  have hd' : 0 < d := hd
  intro h
  have h' := h.mono_set (s := Ioo 0 d) (fun s hs => (hnear hs).2)
  have hI : IntegrableOn (fun t:ℝ => t⁻¹) (Ioo 0 d) := by
    apply (h'.norm.const_mul (2/c)).mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht' : 0 < t := ht.1
    have hk := (hnear ht).1
    have hD : 0 < portalBare m b X t := by
      apply pos_of_mul_pos_right (lt_trans (half_pos hc) hk) ht'.le
    rw [Real.norm_of_nonneg (inv_nonneg.mpr ht'.le),Real.norm_of_nonneg hD.le]
    rw [←one_div,div_le_iff₀ ht']
    calc (1:ℝ) = (2/c)*(c/2) := by field_simp
         _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hk.le (show 0 ≤ 2/c by positivity)]
  have hP : IntegrableOn (fun t:ℝ => t^(-1:ℝ)) (Ioo 0 d) := by simpa only [Real.rpow_neg_one] using hI
  exact (lt_irrefl (-1:ℝ)) ((intervalIntegral.integrableOn_Ioo_rpow_iff hd').mp hP)

/-- The finite cut and divergent complete proper response are simultaneous
properties of a single mediator below the ordinary Dirac pair threshold. -/
theorem portal_pair_and_full_response {m b X : ℝ} (hm : 0 < m) (hb : 0 < b) (ht : b<4*m^2) (hX : 0 < X) :
    (∀ s < 4*m^2, portalPairCut m b s=0) ∧
    IntegrableOn (fun s => portalPairCut m b s/s) (Ioi (4*m^2)) ∧
    ∀ δ > 0, ¬ IntegrableOn (portalBare m b X) (Ioo 0 δ) :=
  ⟨(portal_cut_integrable hm hb ht).1,(portal_cut_integrable hm hb ht).2,fun _ => portal_bare_nonintegrable m hb hX⟩

/-- On the selected spatial chart the energy of an on-shell pair is
inside the forward cone at every relative momentum. -/
theorem portal_pair_forward_cone (m : ℝ) (k P : ChargeSpatialMomentum) :
    ‖P‖ ≤ FurtherOptical.energy m (k+P)+FurtherOptical.energy m (-k) := by
  have h (q : ChargeSpatialMomentum) : ‖q‖ ≤ FurtherOptical.energy m q := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity : 0 ≤ m^2+‖q‖^2)]
    linarith [sq_nonneg m]
  calc ‖P‖ = ‖(k+P)+(-k)‖ := by rw [add_right_comm,add_neg_cancel,zero_add]
       _ ≤ ‖k+P‖+‖-k‖ := norm_add_le _ _
       _ ≤ _ := add_le_add (h _) (h _)

/-- The two-point spectral kernel contains a simple and a double
mediator pole in addition to the measured charged-pair continuum. -/
theorem portal_spectral_partial_fractions {b X s : ℝ} (hX : X+b ≠ 0) (hs : X+s ≠ 0) (hg : s-b ≠ 0) :
    b^2/((X+b)^2*(X+s)) = b^2/(s-b)^2*(1/(X+s)-1/(X+b)) + b^2/(s-b)*(1/(X+b)^2) := by
  field_simp
  ring

end UV
