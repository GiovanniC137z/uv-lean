import UV.VerifySpectrumComplexStieltjes
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The vertical boundary approach extracts the actual Dirac atom of an
ordinary reference-weighted Stieltjes measure. -/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology

namespace UV.RevisionSpectrum

def verifyStieltjesVertical (p h : ℝ) : ℂ := -(p:ℂ)+(h:ℂ)*Complex.I

def verifyAtomicIntegrand (p h s : ℝ) : ℂ :=
  ((h:ℂ)*Complex.I) * verifyStieltjesIntegrand (verifyStieltjesVertical p h) s

theorem verify_stieltjes_vertical_mem {p h : ℝ} (hh : 0<h) :
    verifyStieltjesVertical p h ∈ verifyUpperStieltjesDomain := by
  right
  simpa [verifyStieltjesVertical,Complex.mul_im] using hh

private theorem verify_atom_den_real (p h s : ℝ) :
    (verifyStieltjesVertical p h+(s:ℂ)).re = s-p := by
  simp [verifyStieltjesVertical, Complex.mul_re,sub_eq_add_neg,add_comm]

private theorem verify_atom_den_imag (p h s : ℝ) :
    (verifyStieltjesVertical p h+(s:ℂ)).im = h := by
  simp [verifyStieltjesVertical, Complex.mul_im]

private theorem verify_atom_dominating {p h s y : ℝ} (hp : 0≤p) (hh : 0<h)
    (hh' : h≤1) (hy : 0<y) (hs : 0≤s) :
    ‖verifyAtomicIntegrand p h s‖ ≤ (1+y+p)*stieltjesWeight y s := by
  let D := ‖verifyStieltjesVertical p h+(s:ℂ)‖
  have hD : h≤D := by
    have h := Complex.abs_im_le_norm (verifyStieltjesVertical p h+(s:ℂ))
    rwa [verify_atom_den_imag, abs_of_pos hh] at h
  have hpD : s≤p+D := by
    have h := Complex.re_le_norm (verifyStieltjesVertical p h+(s:ℂ))
    rw [verify_atom_den_real] at h
    dsimp [D]
    linarith
  have hpos : 0<D := hh.trans_le hD
  have he : ‖verifyAtomicIntegrand p h s‖ = h*D⁻¹ := by
    simp only [verifyAtomicIntegrand, verifyStieltjesIntegrand, D, norm_mul, norm_inv, Complex.norm_I,
      mul_one, Complex.norm_real, Real.norm_of_nonneg hh.le]
  rw [he,stieltjesWeight,← div_eq_mul_inv,← div_eq_mul_inv]
  apply (div_le_div_iff₀ hpos (by positivity)).2
  calc
    h*(y+s) ≤ h*(y+(p+D)) := mul_le_mul_of_nonneg_left (by linarith [hpD]) hh.le
    _ = h*(y+p)+h*D := by ring
    _ ≤ D*(y+p)+1*D := add_le_add
      (mul_le_mul_of_nonneg_right hD (by positivity)) (mul_le_mul_of_nonneg_right hh' hpos.le)
    _ = (1+y+p)*D := by ring

private theorem verify_atomic_integrand_tendsto (p s : ℝ) :
    Tendsto (fun h : ℝ => verifyAtomicIntegrand p h s) (𝓝[>] (0:ℝ))
      (𝓝 (({p}:Set ℝ).indicator (fun _ => (1:ℂ)) s)) := by
  classical
  by_cases hp : s=p
  · subst s
    rw [indicator_of_mem (mem_singleton p)]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : (h:ℂ)*Complex.I ≠ 0 := mul_ne_zero
       (Complex.ofReal_ne_zero.mpr (mem_Ioi.mp hh).ne') Complex.I_ne_zero
    have he : verifyStieltjesVertical p h +(p:ℂ) = (h:ℂ)*Complex.I := by
      unfold verifyStieltjesVertical
      ring
    rw [verifyAtomicIntegrand, verifyStieltjesIntegrand, he, mul_inv_cancel₀ hh']
  · rw [indicator_of_notMem (show s∉({p}:Set ℝ) from hp)]
    have h0 : verifyStieltjesVertical p 0+(s:ℂ) ≠ 0 := by
      intro hn
      apply hp
      have he := congrArg Complex.re hn
      rw [verify_atom_den_real, Complex.zero_re] at he
      exact sub_eq_zero.mp he
    have hv : Continuous (fun h : ℝ => verifyStieltjesVertical p h +(s:ℂ)) := by
      unfold verifyStieltjesVertical
      fun_prop
    have hi : ContinuousAt (fun h : ℝ => verifyStieltjesIntegrand (verifyStieltjesVertical p h) s)
        0 := hv.continuousAt.inv₀ h0
    have hm : Continuous (fun h : ℝ => (h:ℂ)*Complex.I) := by fun_prop
    have ht := (hm.continuousAt.mul hi).tendsto
    simpa only [verifyAtomicIntegrand, Complex.ofReal_zero, zero_mul] using
      ht.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)

theorem verify_stieltjes_extracts_real_atom {ν : Measure ℝ} {p y : ℝ}
    (hp : 0≤p) (hy : 0<y) (hν : ∀ᵐ s ∂ν,0≤s) (hi : Integrable (stieltjesWeight y) ν) :
    Tendsto (fun h : ℝ => ((h:ℂ)*Complex.I) *
      verifyComplexStieltjes ν (verifyStieltjesVertical p h))
      (𝓝[>] (0:ℝ)) (𝓝 (ν.real ({p}:Set ℝ) : ℂ)) := by
  classical
  have H := tendsto_integral_filter_of_dominated_convergence (μ := ν)
    (F := verifyAtomicIntegrand p) (f := ({p}:Set ℝ).indicator (fun _ => (1:ℂ)))
    (l := 𝓝[>] (0:ℝ)) (fun s => (1+y+p)*stieltjesWeight y s)
    ?_ ?_ (hi.const_mul _) ?_
  · have he : (∫ s, ({p}:Set ℝ).indicator (fun _ => (1:ℂ)) s ∂ν) =
        (ν.real ({p}:Set ℝ) : ℂ) := by
      rw [integral_indicator (measurableSet_singleton p), integral_const]
      simp [measureReal_def]
    rw [he] at H
    simpa only [verifyComplexStieltjes, verifyAtomicIntegrand, integral_const_mul] using H
  · exact Eventually.of_forall fun h =>
      (by unfold verifyAtomicIntegrand verifyStieltjesIntegrand; fun_prop :
        Measurable (verifyAtomicIntegrand p h)).aestronglyMeasurable
  · have hlt : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ), h<1 :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)
    filter_upwards [hlt, self_mem_nhdsWithin] with h hh' hh
    exact hν.mono fun s hs => verify_atom_dominating hp hh hh'.le hy hs
  · exact Eventually.of_forall (verify_atomic_integrand_tendsto p)

end UV.RevisionSpectrum
