import UV.ContinueNormalConstrainedTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Pi

/-! Frequency-domain sewing for the spatially constant Maxwell mode
on the finite slab. The endpoint of the holonomy Brownian lift is free.
The modulus bound at frequency zero is the length of the marked interval. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped FourierTransform Topology

namespace UV

def omegaRotorMark (t ν : ℝ) := ∫ u in (0:ℝ)..t, normalAngularPhase ν u

theorem omega_rotor_mark_continuous (t : ℝ) : Continuous (omegaRotorMark t) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  change Continuous (fun z : ℝ × ℝ => Complex.exp (-Complex.I*(z.1:ℂ)*(z.2:ℂ)))
  fun_prop

theorem omega_rotor_mark_bounds {t : ℝ} (ht : 0 ≤ t) (ν : ℝ) :
    ‖omegaRotorMark t ν‖ ≤ t ∧ (ν ≠ 0 → ‖omegaRotorMark t ν‖ ≤ 2/|ν|) := by
  constructor
  · simpa [omegaRotorMark,abs_of_nonneg ht] using intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := t) (f := normalAngularPhase ν) (C := 1) (fun u _ => (normal_angular_phase_norm ν u).le)
  · intro hν
    let c := -Complex.I*(ν:ℂ)
    have hc : c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr hν)
    change ‖∫ u in (0:ℝ)..t, Complex.exp (c*(u:ℂ))‖ ≤ _
    rw [integral_exp_mul_complex hc,norm_div]
    have hn : ‖c‖ = |ν| := by simp [c]
    rw [hn]; apply div_le_div_of_nonneg_right _ (abs_nonneg ν)
    exact (norm_sub_le _ _).trans_eq (by norm_num [c,Complex.norm_exp,Complex.mul_re])

theorem omega_rotor_pair_integrable {s t T : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hsT : s ≤ T) (htT : t ≤ T) :
    let f := fun ν => omegaRotorMark s (-ν)*omegaRotorMark t ν
    Integrable f ∧ ∀ ν, ‖f ν‖ ≤ (2*T^2+8)*(1+ν^2)⁻¹ := by
  let f := fun ν => omegaRotorMark s (-ν)*omegaRotorMark t ν
  have hc : Continuous f := ((omega_rotor_mark_continuous s).comp continuous_neg).mul (omega_rotor_mark_continuous t)
  have hb (ν) : ‖f ν‖ ≤ (2*T^2+8)*(1+ν^2)⁻¹ := by
    rw [←div_eq_mul_inv,le_div_iff₀ (by positivity)]
    change ‖omegaRotorMark s (-ν)*omegaRotorMark t ν‖ * _ ≤ _
    rw [norm_mul]
    have hs' := omega_rotor_mark_bounds hs (-ν)
    have ht' := omega_rotor_mark_bounds ht ν
    by_cases hz : |ν| ≤ 1
    · have h := mul_le_mul (hs'.1.trans hsT) (ht'.1.trans htT) (norm_nonneg _) (ht.trans htT)
      have hν : 1+ν^2 ≤ 2 := by nlinarith [sq_abs ν,abs_nonneg ν]
      nlinarith [mul_le_mul h hν (by positivity : 0 ≤ 1+ν^2) (mul_self_nonneg T)]
    · have hp : 0 < |ν| := by linarith [lt_of_not_ge hz]
      have hn := (abs_pos.mp hp)
      have h := mul_le_mul (by simpa only [abs_neg] using hs'.2 (neg_ne_zero.mpr hn)) (ht'.2 hn) (norm_nonneg _) (by positivity)
      have hν : 1+ν^2 ≤ 2*|ν|^2 := by nlinarith [lt_of_not_ge hz,sq_abs ν]
      have hle := mul_le_mul h hν (by positivity : 0 ≤ 1+ν^2) (by positivity)
      have hcan : 2/|ν| * (2/|ν|)*(2*|ν|^2) = 8 := by field_simp; ring
      nlinarith [hcan,sq_nonneg T]
  exact ⟨(integrable_inv_one_add_sq.const_mul _).mono' hc.aestronglyMeasurable (Eventually.of_forall hb),hb⟩

def omegaRotorOverlap (s t x : ℝ) : ℝ := max (min s (t-x)-max 0 (-x)) 0

private def omegaIntervalPulse (t : ℝ) := (Ioc (0:ℝ) t).indicator (fun _ => (1:ℂ))

private theorem omega_overlap_slice (s t x : ℝ) :
    (∫ u in Ioc 0 s, omegaIntervalPulse t (x+u)) = (omegaRotorOverlap s t x:ℂ) := by
  have he : (fun u => omegaIntervalPulse t (x+u)) = (Ioc (-x) (t-x)).indicator (fun _ => (1:ℂ)) := by
    funext u
    have hh : x+u ∈ Ioc 0 t ↔ u ∈ Ioc (-x) (t-x) := by simp only [mem_Ioc]; constructor <;> rintro ⟨h,k⟩ <;> constructor <;> linarith
    simp only [omegaIntervalPulse,indicator_apply,hh]
  rw [he,setIntegral_indicator measurableSet_Ioc,Ioc_inter_Ioc,setIntegral_const,Real.volume_real_Ioc]
  simp [omegaRotorOverlap,Complex.real_smul]

private theorem omega_overlap_integrable (s t : ℝ) : Integrable (fun x => (omegaRotorOverlap s t x:ℂ)) := by
  have hc : Continuous (fun x => (omegaRotorOverlap s t x:ℂ)) := by unfold omegaRotorOverlap; fun_prop
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Icc (-s) t) isCompact_Icc
  intro x hx
  have h : min s (t-x)-max 0 (-x) ≤ 0 := by
    by_cases hh : x < -s
    · linarith [min_le_left s (t-x),le_max_right 0 (-x)]
    · have h' : t < x := lt_of_not_ge (fun k => hx ⟨le_of_not_gt hh,k⟩)
      linarith [min_le_right s (t-x),le_max_left 0 (-x)]
  simp [omegaRotorOverlap,max_eq_right h]

private theorem omega_overlap_transform {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (ν : ℝ) :
    (∫ x, normalAngularPhase ν x * (omegaRotorOverlap s t x:ℂ)) =
      omegaRotorMark s (-ν)*omegaRotorMark t ν := by
  let μ := (volume : Measure ℝ).restrict (Ioc 0 s)
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  let f := omegaIntervalPulse t
  let F := fun x u => normalAngularPhase ν x * f (x+u)
  have hf : Integrable f := (integrableOn_const (C := (1:ℂ)) (hs := measure_Ioc_lt_top.ne)).integrable_indicator measurableSet_Ioc
  have hfm : Measurable f := measurable_const.indicator measurableSet_Ioc
  have hw : Continuous (normalAngularPhase ν) := by unfold normalAngularPhase; fun_prop
  have hNorm (x u) : ‖F x u‖ = ‖f (x+u)‖ := by simp only [F,norm_mul,normal_angular_phase_norm,one_mul]
  have hInt : Integrable (Function.uncurry F) (volume.prod μ) := by
    apply (integrable_prod_iff' ((hw.measurable.comp measurable_fst).mul (hfm.comp (measurable_fst.add measurable_snd))).aestronglyMeasurable).mpr
    constructor
    · refine Eventually.of_forall fun u => ?_
      apply ((measurePreserving_add_right volume u).integrable_comp_of_integrable hf).norm.mono'
        ((hw.measurable.mul (hfm.comp (measurable_id.add_const u))).aestronglyMeasurable)
      exact Eventually.of_forall fun x => (hNorm x u).le
    · have he (u : ℝ) : (∫ x, ‖F x u‖) = ∫ x, ‖f x‖ := by
        simp_rw [hNorm]; exact (measurePreserving_add_right volume u).integral_comp (Homeomorph.addRight u).measurableEmbedding (fun x => ‖f x‖)
      change Integrable (fun u => ∫ x, ‖F x u‖) μ
      simp_rw [he]; exact integrable_const _
  have hin (u : ℝ) : (∫ x, F x u) = normalAngularPhase (-ν) u * omegaRotorMark t ν := by
    let g := fun z => normalAngularPhase ν z * f z
    have he (x) : F x u = normalAngularPhase (-ν) u * g (x+u) := by
      have hphase : normalAngularPhase ν x = normalAngularPhase (-ν) u * normalAngularPhase ν (x+u) := by
        unfold normalAngularPhase
        rw [←Complex.exp_add]
        congr 1; push_cast; ring
      dsimp only [F,g]
      rw [←mul_assoc,←hphase]
    simp_rw [he]
    rw [integral_const_mul,(measurePreserving_add_right volume u).integral_comp (Homeomorph.addRight u).measurableEmbedding]
    congr 1
    have hG : g = (Ioc 0 t).indicator (normalAngularPhase ν) := by
      funext x; by_cases hx : x ∈ Ioc 0 t <;> simp [g,f,omegaIntervalPulse,hx]
    rw [hG,integral_indicator measurableSet_Ioc,omegaRotorMark,intervalIntegral.integral_of_le ht]
  simp_rw [←omega_overlap_slice s t,←integral_const_mul]
  change (∫ x, ∫ u, F x u ∂μ) = _
  rw [integral_integral_swap hInt]
  simp_rw [hin]
  rw [integral_mul_const]
  congr 1
  exact (intervalIntegral.integral_of_le hs).symm

/-- The exact Fourier normalization of the covariance of one pair of
harmonic Wilson marks at arbitrary slab times. -/
theorem omega_rotor_pair_covariance {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ((2*Real.pi:ℝ):ℂ)⁻¹ * (∫ ν, omegaRotorMark s (-ν)*omegaRotorMark t ν) = (min s t : ℝ) := by
  let g := fun x => (omegaRotorOverlap s t x:ℂ)
  let f := fun ν => omegaRotorMark s (-ν)*omegaRotorMark t ν
  have hc : Continuous g := by dsimp [g,omegaRotorOverlap]; fun_prop
  have hhat (η : ℝ) : 𝓕 g η = f (2*Real.pi*η) := by
    rw [Real.fourierIntegral_eq']
    have he (x : ℝ) : Complex.exp ((↑(-2*Real.pi*inner ℝ x η):ℂ)*Complex.I) = normalAngularPhase (2*Real.pi*η) x := by
      unfold normalAngularPhase
      simp only [RCLike.inner_apply,conj_trivial]
      push_cast; congr 1; ring
    simp_rw [he]
    exact omega_overlap_transform hs ht _
  have ha : 0 < 2*Real.pi := by positivity
  have hi : Integrable (𝓕 g) := by
    simp_rw [show 𝓕 g = fun η => f (2*Real.pi*η) from funext hhat]
    exact (omega_rotor_pair_integrable hs ht (le_max_left s t) (le_max_right s t)).1.comp_mul_left' ha.ne'
  have hg : Integrable g := omega_overlap_integrable s t
  have h := hg.fourier_inversion hi (hc.continuousAt (x := 0))
  rw [Real.fourierIntegralInv_eq'] at h
  simp only [inner_zero_right,mul_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_smul] at h
  change (∫ η, 𝓕 g η) = g 0 at h
  simp_rw [hhat] at h
  rw [Measure.integral_comp_mul_left,abs_of_pos (inv_pos.mpr ha),Complex.real_smul] at h
  simpa only [Complex.ofReal_inv,g,omegaRotorOverlap,sub_zero,neg_zero,max_self,max_eq_left (le_min hs ht)] using h

@[simp] theorem omega_rotor_mark_zero (t : ℝ) : omegaRotorMark t 0 = (t : ℂ) := by
  simp [omegaRotorMark,normalAngularPhase]

/-- Each Wick line carries its own frequency. Its endpoints may coincide
with one another or with arbitrary split charged endpoint times. -/
def omegaRotorLine {ι : Type*} [DecidableEq ι] (i j : ι) (V s t ν : ℝ) : ℂ :=
  (if i = j then (V:ℂ)⁻¹ else 0) * (((2*Real.pi:ℝ):ℂ)⁻¹ *
    (omegaRotorMark s (-ν)*omegaRotorMark t ν))

theorem omega_rotor_line_integrable (i j : Fin 3) {V s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Integrable (omegaRotorLine i j V s t) := by
  have hi := (omega_rotor_pair_integrable hs ht (le_max_left _ _) (le_max_right _ _)).1
  exact (hi.const_mul _).const_mul _

theorem omega_rotor_line_covariance (i j : Fin 3) {V s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (∫ ν, omegaRotorLine i j V s t ν) =
      (if i = j then (min s t / V : ℝ) else 0) := by
  simp only [omegaRotorLine,integral_const_mul,omega_rotor_pair_covariance hs ht]
  split_ifs <;> simp [div_eq_inv_mul]

/-- Absolute integrability and the exact value of every fixed finite
Cartesian Wick pairing, including the product over zero lines. The
momentum carried by the harmonic mode is spatially zero in each line. -/
theorem omega_rotor_finite_sewing {n : ℕ} (i j : Fin n → Fin 3)
    {V : ℝ} (_hV : 0 < V) (s t : Fin n → ℝ) (hs : ∀ k, 0 ≤ s k) (ht : ∀ k, 0 ≤ t k) :
    let F := fun (ν : Fin n → ℝ) => ∏ k, omegaRotorLine (i k) (j k) V (s k) (t k) (ν k)
    Integrable F ∧ (∫ ν, F ν) =
      ∏ k, (if i k = j k then ((min (s k) (t k) / V : ℝ) : ℂ) else 0) := by
  constructor
  · exact Integrable.fintype_prod (fun k => omega_rotor_line_integrable (i k) (j k) (hs k) (ht k))
  · dsimp only
    rw [integral_fintype_prod_volume_eq_prod (fun k => omegaRotorLine (i k) (j k) V (s k) (t k))]
    apply Finset.prod_congr rfl
    intro k _
    rw [omega_rotor_line_covariance _ _ (hs k) (ht k)]
    split_ifs <;> rfl

/-- An integrable hard-momentum/radial majorant remains integrable after
adding every line of a fixed finite harmonic sewing with independent
frequency. No independence between marks in the hard integrand is needed
when the selected times are dominated uniformly on the slab. -/
theorem omega_rotor_joint_majorant {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [SigmaFinite μ] {n : ℕ} {H : X → ℝ} (hH : Integrable H μ)
    (T : ℝ) : Integrable (fun x : X × (Fin n → ℝ) =>
      H x.1 * ∏ k, ((2*T^2+8)*(1+(x.2 k)^2)⁻¹)) (μ.prod volume) := by
  have hline : Integrable (fun ν : ℝ => (2*T^2+8)*(1+ν^2)⁻¹) := by
    exact integrable_inv_one_add_sq.const_mul (2*T^2+8)
  exact hH.mul_prod (Integrable.fintype_prod (fun _ => hline))

/-- The split times may themselves be functions of all the other integration
variables. Uniform line estimates give joint absolute convergence even
when the radial and hard modes vary with the endpoints. -/
theorem omega_rotor_joint_sewing {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [SigmaFinite μ] {n : ℕ} {T : ℝ} {H : X → ℝ} (hH : Integrable H μ)
    (hH₀ : ∀ x, 0 ≤ H x) (s t : Fin n → X → ℝ)
    (hs : ∀ k x, s k x ∈ Icc 0 T) (ht : ∀ k x, t k x ∈ Icc 0 T)
    (G : X × (Fin n → ℝ) → ℂ) (hG : AEStronglyMeasurable G (μ.prod volume))
    (hdom : ∀ᵐ x ∂μ.prod volume, ‖G x‖ ≤ H x.1 * ∏ k,
      ‖omegaRotorMark (s k x.1) (-(x.2 k))*omegaRotorMark (t k x.1) (x.2 k)‖) :
    Integrable G (μ.prod volume) := by
  apply (omega_rotor_joint_majorant μ hH T).mono' hG
  filter_upwards [hdom] with x hx
  refine hx.trans (mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun k _ => norm_nonneg _) ?_) (hH₀ _))
  intro k _
  exact (omega_rotor_pair_integrable (hs k x.1).1 (ht k x.1).1 (hs k x.1).2 (ht k x.1).2).2 _

end UV
