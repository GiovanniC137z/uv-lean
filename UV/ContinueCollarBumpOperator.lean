import UV.ContinueCollarBumpEnergy
import UV.ContinueCollarBumpSpectral
import UV.ContinueCollarHSIdentity
import UV.ResumeCollarLower

/-! The lower-order test on the genuine weighted heat operator takes
the actual normalized compactly supported radial bump as its input. -/

noncomputable section

open MeasureTheory Set Real
open UV.AdvanceCollarResonanceBump UV.ContinueCollarHSIdentity
open scoped InnerProductSpace Topology

namespace UV.CollarEigenmode

private theorem bumpMem (h : ℝ) : MemLp (fun r => (resonanceBump h r : ℂ)) 2 radialMeasure := by
  have hC := Complex.continuous_ofReal.comp (resonance_bump_smooth h).continuous
  exact (memLp_two_iff_integrable_sq_norm hC.aestronglyMeasurable).mpr ((hC.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)

def radialBump (h : ℝ) : RadialL2 := (bumpMem h).toLp _

theorem radialBump_coe (h : ℝ) :
    ∀ᵐ r ∂radialMeasure,radialBump h r = (resonanceBump h r:ℂ) := (bumpMem h).coeFn_toLp

theorem radialBump_norm {h : ℝ} (hh : 0<h) (h₂ : 2*h≤1) : ‖radialBump h‖=1 := by
  have hi := L2.integrable_inner (𝕜 := ℂ) (radialBump h) (radialBump h)
  have he := congrArg RCLike.re (L2.inner_def (𝕜 := ℂ) (radialBump h) (radialBump h))
  rw [← integral_re hi] at he
  simp only [← norm_sq_eq_re_inner] at he
  have ham : (∫ r,‖radialBump h r‖^2 ∂radialMeasure) = ∫ r in Ioc (0:ℝ) 1,resonanceBump h r^2 := by
    apply integral_congr_ae
    filter_upwards [radialBump_coe h] with r hr
    simp [hr,Real.norm_eq_abs]
  have hdis (r : ℝ) (hr : r ∉ Ioc 0 1) : resonanceBump h r^2=0 := by
    have hsr : r ∉ Ioo h (2*h) := fun hrr => hr ⟨hh.trans hrr.1,(le_of_lt hrr.2).trans h₂⟩
    simp [resonance_bump_zero_off_support hh hsr]
  have hS (r : ℝ) (hr : r ∉ Icc h (2*h)) : resonanceBump h r^2=0 := by
    simp [resonance_bump_zero_off_support hh (fun hs => hr (Ioo_subset_Icc_self hs))]
  have hmass := (setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) hdis).trans (setIntegral_eq_integral_of_forall_compl_eq_zero hS).symm
  rw [ham,hmass,resonance_bump_norm hh] at he
  nlinarith [norm_nonneg (radialBump h)]

private theorem local_pairing {X : Type*} [MeasurableSpace X] {μ : Measure X} {S : Set X}
    (hS : MeasurableSet S) (v w y : Lp ℂ 2 μ) {z : ℝ}
    (hsup : ∀ᵐ r ∂μ,r ∉ S → v r = 0)
    (hweight : ∀ᵐ r ∂μ,r ∈ S → sqrt z*‖w r‖ ≤ ‖y r‖) :
    sqrt z*(⟪v,w⟫_ℂ).re ≤ ‖v‖*‖y‖ := by
  let hw := (Lp.memLp w).indicator hS
  let vcut := hw.toLp _
  have hcut : ∀ᵐ r ∂μ,vcut r=S.indicator (fun x => w x) r := hw.coeFn_toLp
  have hpair : ⟪v,w⟫_ℂ = ⟪v,vcut⟫_ℂ := by
    rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hcut,hsup] with r hr hv
    by_cases h : r ∈ S
    · rw [hr,indicator_of_mem h]
    · rw [hv h]; simp
  let x := (sqrt z:ℂ) • vcut
  have hnorm : ‖x‖ ≤ (1:ℝ)*‖y‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_smul (sqrt z:ℂ) vcut,hcut,hweight] with r hx hc hf
    change ‖((sqrt z : ℂ) • vcut : Lp ℂ 2 μ) r‖ ≤ _
    rw [hx,Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg (sqrt_nonneg _),hc,one_mul]
    by_cases h : r ∈ S
    · simpa only [indicator_of_mem h] using hf h
    · simp [indicator_of_notMem h]
  change ‖(sqrt z:ℂ) • vcut‖ ≤ _ at hnorm
  rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (sqrt_nonneg _),one_mul] at hnorm
  have hinner := (Complex.re_le_norm ⟪v,vcut⟫_ℂ).trans (norm_inner_le_norm v vcut)
  rw [hpair]
  calc
    _ ≤ sqrt z*(‖v‖*‖vcut‖) := mul_le_mul_of_nonneg_left hinner (sqrt_nonneg _)
    _ = ‖v‖*(sqrt z*‖vcut‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (norm_nonneg v)

/-- Sharp lower scale of the weighted collar. The spectral form identity
is needed only on the explicit smooth unit bump. The input of the tested
heat operator can be complex, with no pointwise sign restriction. -/
theorem weighted_heat_operator_lower {ι : Type*} (b : HilbertBasis ι ℂ RadialL2)
    (T A : ℝ → RadialL2 →L[ℂ] RadialL2) (E : ι → ℝ) (j : ℝ) (Z : ℝ → ℝ)
    {a : ℝ} (ha : 0<a) (hE : ∀ i,0 ≤ E i)
    (hZ : ∀ r ∈ Ioc 0 1, exp (a/r^2*ResumeCollarSpectral.durationLog r^3) ≤ Z r)
    (hact : ∀ t,0<t → ∀ x i,b.repr (T t x) i = (exp (-t*E i):ℂ)*b.repr x i)
    (hweight : ∀ t,0<t → ∀ x,∀ᵐ r ∂radialMeasure,A t x r = (sqrt (Z r):ℂ)*T t x r)
    (hform : ∀ h,0<h → 2*h≤1 → HasSum (fun i => E i*‖b.repr (radialBump h) i‖^2) (dirichletEnergy j (resonanceBump h))) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ t in 𝓝[>] (0:ℝ),0 < ‖A t‖^2 ∧ c*ResumeCollarSpectral.collarScale t ≤ log (‖A t‖^2) := by
  obtain ⟨C,hC,hb⟩ := dirichlet_bump_energy j
  apply ResumeCollarLower.collar_lower_from_bump_test ha hC Z (fun h => dirichletEnergy j (resonanceBump h)) _ hZ (fun h hh h₂ => (hb h hh h₂).2)
  intro t h ht hh h₂ z hreg
  by_cases hz : 0 ≤ z
  · let v := radialBump h
    have hv : ‖v‖=1 := radialBump_norm hh h₂
    have hspec := mode_heat_jensen b (T t) E ht.le hE v hv (hact t ht v) (hform h hh h₂).summable
    rw [(hform h hh h₂).tsum_eq] at hspec
    have hlocal := local_pairing (S := Icc h (2*h)) measurableSet_Icc v (T t v) (A t v) (z := z)
      (by filter_upwards [radialBump_coe h] with r hr; intro hs
          rw [show v r=(resonanceBump h r:ℂ) from hr,resonance_bump_zero_off_support hh (fun hs' => hs (Ioo_subset_Icc_self hs'))]; simp)
      (by filter_upwards [hweight t ht v] with r hr; intro hs
          rw [hr,norm_mul,Complex.norm_real,Real.norm_of_nonneg (sqrt_nonneg _)]
          exact mul_le_mul_of_nonneg_right (sqrt_le_sqrt (hreg r hs)) (norm_nonneg _))
    rw [hv,one_mul] at hlocal
    have hl := (mul_le_mul_of_nonneg_left hspec (sqrt_nonneg _)).trans (hlocal.trans (show ‖A t v‖ ≤ ‖A t‖ by simpa [hv] using (A t).le_opNorm v))
    have hpow := pow_le_pow_left₀ (mul_nonneg (sqrt_nonneg _) (exp_nonneg _)) hl 2
    rw [mul_pow,sq_sqrt hz,← exp_nat_mul] at hpow
    convert hpow using 1
    push_cast
    ring_nf
  · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hz) (exp_nonneg _)).trans (sq_nonneg _)

end UV.CollarEigenmode
