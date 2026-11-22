import UV.RevisionBoundaryDensity
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! A normal spectral law cannot distinguish the relative sign of two
disjoint bands. This is the actual Fourier transform, in the unitary
convention with (2π) in the exponential. -/

noncomputable section

open MeasureTheory Set Real Filter
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate InnerProductSpace

namespace UV.RevisionBoundary

private theorem fourier_even_of_even {f : ℝ → ℂ} (hf : (∀ x, f (-x) = f x)) :
    ∀ x, 𝓕 f (-x) = 𝓕 f x := by
  intro x
  rw [← Real.fourierIntegralInv_eq_fourierIntegral_neg,
    Real.fourierIntegralInv_eq_fourierIntegral_comp_neg,
    show (fun t => f (-t)) = f from funext hf]

private theorem fourier_real_of_real_even {f : ℝ → ℂ} (hf : (∀ x, f (-x) = f x))
    (hreal : ∀ x, (f x).im = 0) (x : ℝ) : (𝓕 f x).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  conv_rhs => rw [← fourier_even_of_even hf x]
  rw [← Real.fourierIntegralInv_eq_fourierIntegral_neg, Real.fourierIntegral_eq',
    Real.fourierIntegralInv_eq', ← integral_conj]
  congr 1
  funext t
  rw [smul_eq_mul, smul_eq_mul, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, Complex.conj_eq_iff_im.mpr (hreal t), mul_neg, ← neg_mul, ← Complex.ofReal_neg]
  congr 4
  ring

private theorem fourier_zero (f : ℝ → ℂ) : 𝓕 f 0 = ∫ x, f x := by
  simp [Real.fourierIntegral_eq]

private theorem square_integral_even_fourier (f : 𝓢(ℝ, ℂ))
    (he : ∀ x, f (-x) = f x) (hr : ∀ x, (f x).im = 0) :
    ∫ x : ℝ, ‖𝓕 f x‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  let F := SchwartzMap.fourierTransformCLE ℂ f
  have hfint : Integrable (f : ℝ → ℂ) := f.integrable
  have hFint : Integrable (𝓕 f) := F.integrable
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact real_inner_comm x y
  have h :=
    VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner hfint hFint
  rw [hflip] at h
  change (∫ x, 𝓕 f x * 𝓕 f x) = ∫ x, f x * 𝓕 (𝓕 f) x at h
  have hff : (𝓕 (𝓕 f) : ℝ → ℂ) = f := by
    have heF := fourier_even_of_even he
    have hinv : (𝓕⁻ (𝓕 f) : ℝ → ℂ) = f :=
      f.continuous.fourier_inversion f.integrable hFint
    calc
      _ = (𝓕⁻ (𝓕 f) : ℝ → ℂ) := by
        funext x
        rw [Real.fourierIntegralInv_eq_fourierIntegral_neg, fourier_even_of_even heF x]
      _ = _ := hinv
  rw [hff] at h
  have heq (z : ℂ) (hz : z.im = 0) : z * z = (‖z‖ ^ 2 : ℝ) := by
    calc
      z * z = conj z * z := congrArg (· * z) (Complex.conj_eq_iff_im.mpr hz).symm
      _ = _ := by rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hL : (fun x : ℝ => 𝓕 f x * 𝓕 f x) = fun x => ((‖𝓕 f x‖ ^ 2 : ℝ) : ℂ) := by
    funext x
    exact heq _ (fourier_real_of_real_even he hr x)
  have hR : (fun x : ℝ => f x * f x) = fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
    funext x
    exact heq _ (hr x)
  rw [hL, hR, integral_complex_ofReal, integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

private theorem zero_node_schwartz_finite (f : 𝓢(ℝ, ℂ)) (hz : f 0 = 0) {T : ℝ}
    (hT : 0 < T) : densityReturn T (bornDensity f) ≠ ∞ := by
  let g := SchwartzMap.derivCLM ℂ f
  have hg : MemLp g 2 volume := g.memLp 2
  have hprim (x : ℝ) : f x = ∫ t in (0 : ℝ)..x, g t := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f' := (g : ℝ → ℂ))
      (fun t _ => f.hasDerivAt t) g.integrable.intervalIntegrable]
    rw [hz, sub_zero]
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (((memLp_two_iff_integrable_sq_norm hg.1).mp hg).hasFiniteIntegral
      |> fun h => by
        rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => sq_nonneg _)] at h
        exact h.ne)) (nodal_state_return_bound hT f.continuous hg hprim)

set_option maxHeartbeats 600000 in
private theorem exists_even_bands :
    ∃ u v : 𝓢(ℝ, ℂ),
      (∀ x, u (-x) = u x) ∧ (∀ x, v (-x) = v x) ∧
      (∀ x, (u x).im = 0) ∧ (∀ x, (v x).im = 0) ∧
      (∀ x, u x = 0 ∨ v x = 0) ∧
      (∫ x, u x) = 1 ∧ (∫ x, v x) = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1/2, 1, by norm_num, by norm_num⟩
  let u : ℝ → ℝ := b.normed volume
  let vp : ℝ → ℝ := fun x => u (x + 3)
  let vm : ℝ → ℝ := fun x => u (x - 3)
  let v : ℝ → ℝ := fun x => (vp x + vm x) / 2
  have hu := b.hasCompactSupport_normed (μ := volume)
  have hvp : HasCompactSupport vp := hu.comp_homeomorph (Homeomorph.addRight (3 : ℝ))
  have hvm : HasCompactSupport vm := by
    simpa only [sub_eq_add_neg] using hu.comp_homeomorph (Homeomorph.addRight (-3 : ℝ))
  have hv : HasCompactSupport v :=
    ((hvp.add hvm).comp_left (g := (· / 2)) (by norm_num))
  have hus : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u := b.contDiff_normed
  have hvp' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) vp := hus.comp (contDiff_id.add contDiff_const)
  have hvm' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) vm := hus.comp (contDiff_id.sub contDiff_const)
  have hvs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v := (hvp'.add hvm').div_const _
  let U : 𝓢(ℝ, ℂ) := (hu.comp_left (g := Complex.ofReal) Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hus)
  let V : 𝓢(ℝ, ℂ) := (hv.comp_left (g := Complex.ofReal) Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hvs)
  have hintu : (∫ x, u x) = 1 := b.integral_normed
  have hintv : (∫ x, v x) = 1 := by
    unfold v
    rw [integral_div, integral_add (hvp'.continuous.integrable_of_hasCompactSupport hvp)
      (hvm'.continuous.integrable_of_hasCompactSupport hvm)]
    change ((∫ x, u (x + 3)) + (∫ x, u (x - 3))) / 2 = 1
    rw [integral_add_right_eq_self, integral_sub_right_eq_self, hintu]
    norm_num
  have hzero (x : ℝ) (hx : 1 ≤ |x|) : u x = 0 := by
    by_contra h
    have hxmem : x ∈ Function.support u := h
    change x ∈ Function.support (b.normed volume) at hxmem
    rw [b.support_normed_eq] at hxmem
    have : |x| < 1 := by simpa [b, Metric.mem_ball, Real.dist_eq] using hxmem
    linarith
  refine ⟨U, V, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change (u (-x) : ℂ) = (u x : ℂ)
    exact congrArg Complex.ofReal (b.normed_neg (μ := volume) x)
  · intro x
    change (v (-x) : ℂ) = (v x : ℂ)
    congr 1
    unfold v vp vm
    have hn (t : ℝ) : u (-t) = u t := b.normed_neg t
    rw [show -x + 3 = -(x - 3) by ring, show -x - 3 = -(x + 3) by ring, hn, hn, add_comm]
  · intro x
    exact Complex.ofReal_im (u x)
  · intro x
    exact Complex.ofReal_im (v x)
  · intro x
    by_cases hx : 1 ≤ |x|
    · exact Or.inl (by change (u x : ℂ) = 0; rw [hzero x hx, Complex.ofReal_zero])
    · have hlt : -1 < x ∧ x < 1 := abs_lt.mp (not_le.mp hx)
      have hp : 1 ≤ |x + 3| := (by linarith : 1 ≤ x + 3).trans (le_abs_self _)
      have hm : 1 ≤ |x - 3| := (by linarith : 1 ≤ -(x - 3)).trans (neg_le_abs _)
      exact Or.inr (by change (v x : ℂ) = 0; simp [v, vp, vm, hzero _ hp, hzero _ hm])
  · change (∫ x, (u x : ℂ)) = 1
    rw [integral_complex_ofReal, hintu, Complex.ofReal_one]
  · change (∫ x, (v x : ℂ)) = 1
    rw [integral_complex_ofReal, hintv, Complex.ofReal_one]

private theorem conj_real_wave_norm (f : 𝓢(ℝ, ℂ)) (c : ℝ) :
    ∫ x : ℝ, ‖((c : ℂ) • f) x‖ ^ 2 = c ^ 2 * ∫ x : ℝ, ‖f x‖ ^ 2 := by
  simp_rw [SchwartzMap.smul_apply, smul_eq_mul, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]
  exact integral_const_mul _ _

/-- Proposition `prop:g5I-isospectral`: exact equal Fourier multiplier laws
for normalized even real Schwartz preparations with opposite UV outcomes. -/
theorem isospectral_normal_preparations {T : ℝ} (hT : 0 < T) :
    ∃ φminus φplus : 𝓢(ℝ, ℂ),
      (∫ x : ℝ, ‖φminus x‖ ^ 2) = 1 ∧ (∫ x : ℝ, ‖φplus x‖ ^ 2) = 1 ∧
      (∀ x, φminus (-x) = φminus x) ∧ (∀ x, φplus (-x) = φplus x) ∧
      (∀ x, (φminus x).im = 0) ∧ (∀ x, (φplus x).im = 0) ∧
      MemLp (deriv (φminus : ℝ → ℂ)) 2 volume ∧
      MemLp (deriv (φplus : ℝ → ℂ)) 2 volume ∧
      (∀ m : ℝ → ℂ, (∫ ξ, m ξ * (‖𝓕 φminus ξ‖ ^ 2 : ℝ)) =
        ∫ ξ, m ξ * (‖𝓕 φplus ξ‖ ^ 2 : ℝ)) ∧
      densityReturn T (bornDensity φminus) ≠ ∞ ∧ densityReturn T (bornDensity φplus) = ∞ := by
  rcases exists_even_bands with ⟨u, v, hue, hve, hur, hvr, hz, hui, hvi⟩
  let amin := u - v
  let aplus := u + v
  have hame (x : ℝ) : amin (-x) = amin x := by simp [amin, hue, hve]
  have hape (x : ℝ) : aplus (-x) = aplus x := by simp [aplus, hue, hve]
  have hamr (x : ℝ) : (amin x).im = 0 := by simp [amin, hur, hvr]
  have hapr (x : ℝ) : (aplus x).im = 0 := by simp [aplus, hur, hvr]
  have ham : (∫ x, amin x) = 0 := by
    simp only [amin, SchwartzMap.sub_apply]
    rw [integral_sub u.integrable v.integrable, hui, hvi, sub_self]
  have hap : (∫ x, aplus x) = 2 := by
    simp only [aplus, SchwartzMap.add_apply]
    rw [integral_add u.integrable v.integrable, hui, hvi]
    norm_num
  have hnorm (x : ℝ) : ‖amin x‖ = ‖aplus x‖ := by
    rcases hz x with h | h <;> simp [amin, aplus, h]
  let Z := ∫ x : ℝ, ‖aplus x‖ ^ 2
  have hZ : 0 < Z := by
    obtain ⟨x, hx⟩ : ∃ x, aplus x ≠ 0 := by
      by_contra! h
      simp [h] at hap
    have hL2 : MemLp (aplus : ℝ → ℂ) 2 volume := aplus.memLp 2
    apply integral_pos_of_integrable_nonneg_nonzero (aplus.continuous.norm.pow 2)
      ((memLp_two_iff_integrable_sq_norm hL2.1).mp hL2)
      (fun _ => sq_nonneg _) (x := x)
    exact (sq_pos_of_pos (norm_pos_iff.mpr hx)).ne'
  let c := (Real.sqrt Z)⁻¹
  let L := SchwartzMap.fourierTransformCLE ℂ (V := ℝ) (E := ℂ)
  let φm := (c : ℂ) • L.symm amin
  let φp := (c : ℂ) • L.symm aplus
  have hsymm {a : 𝓢(ℝ, ℂ)} (he : ∀ x, a (-x) = a x) (x : ℝ) : L.symm a x = 𝓕 a x := by
    change (SchwartzMap.fourierTransformCLE ℂ).symm a x = _
    rw [SchwartzMap.fourierTransformCLE_symm_apply, Real.fourierIntegralInv_eq_fourierIntegral_neg,
      fourier_even_of_even he x]
  have hm (x : ℝ) : φm x = (c : ℂ) * 𝓕 amin x := by
    rw [show φm x = (c : ℂ) • L.symm amin x from SchwartzMap.smul_apply, smul_eq_mul, hsymm hame]
  have hp (x : ℝ) : φp x = (c : ℂ) * 𝓕 aplus x := by
    rw [show φp x = (c : ℂ) • L.symm aplus x from SchwartzMap.smul_apply, smul_eq_mul, hsymm hape]
  have hcZ : c ^ 2 * Z = 1 := by
    unfold c
    rw [inv_pow, Real.sq_sqrt hZ.le, inv_mul_cancel₀ hZ.ne']
  have hφm : (∫ x : ℝ, ‖φm x‖ ^ 2) = 1 := by
    rw [conj_real_wave_norm]
    simp_rw [hsymm hame]
    rw [square_integral_even_fourier amin hame hamr]
    simp_rw [hnorm]
    exact hcZ
  have hφp : (∫ x : ℝ, ‖φp x‖ ^ 2) = 1 := by
    rw [conj_real_wave_norm]
    simp_rw [hsymm hape]
    rw [square_integral_even_fourier aplus hape hapr]
    exact hcZ
  have hφm0 : φm 0 = 0 := by rw [hm, fourier_zero, ham, mul_zero]
  have hφp0 : φp 0 ≠ 0 := by
    rw [hp, fourier_zero, hap]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.2 hZ).ne'))
      (by norm_num)
  refine ⟨φm, φp, hφm, hφp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, zero_node_schwartz_finite φm hφm0 hT,
    nonnodal_state_return_diverges hT φp.continuous hφp0⟩
  · intro x
    rw [hm, hm, fourier_even_of_even hame]
  · intro x
    rw [hp, hp, fourier_even_of_even hape]
  · intro x
    rw [hm, Complex.mul_im, fourier_real_of_real_even hame hamr]
    simp
  · intro x
    rw [hp, Complex.mul_im, fourier_real_of_real_even hape hapr]
    simp
  · exact (SchwartzMap.derivCLM ℂ φm).memLp 2
  · exact (SchwartzMap.derivCLM ℂ φp).memLp 2
  · intro m
    have hLm : L φm = (c : ℂ) • amin := by
      change L ((c : ℂ) • L.symm amin) = _
      rw [map_smul, L.apply_symm_apply]
    have hLp : L φp = (c : ℂ) • aplus := by
      change L ((c : ℂ) • L.symm aplus) = _
      rw [map_smul, L.apply_symm_apply]
    change (∫ x, m x * (‖L φm x‖ ^ 2 : ℝ)) = ∫ x, m x * (‖L φp x‖ ^ 2 : ℝ)
    simp_rw [hLm, hLp, SchwartzMap.smul_apply, smul_eq_mul, norm_mul, hnorm]


end UV.RevisionBoundary
