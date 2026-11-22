import UV.AdvanceSpectrumCompletion
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex

/-! Analyticity of an ordinary Stieltjes transform on the upper slit
continuation domain using the reference-weighted spectral mass. -/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology

namespace UV.RevisionSpectrum

def verifyUpperStieltjesDomain : Set ℂ := {z | 0 < z.re ∨ 0 < z.im}

theorem verify_upper_stieltjes_open : IsOpen verifyUpperStieltjesDomain := by
  change IsOpen ({z : ℂ | 0<z.re} ∪ {z : ℂ | 0<z.im})
  exact (isOpen_lt continuous_const Complex.continuous_re).union
    (isOpen_lt continuous_const Complex.continuous_im)

theorem verify_upper_stieltjes_preconnected : IsPreconnected verifyUpperStieltjesDomain := by
  change IsPreconnected ({z : ℂ | 0<z.re} ∪ {z : ℂ | 0<z.im})
  have hre : Convex ℝ {z : ℂ | 0<z.re} :=
    convex_halfSpace_gt (IsLinearMap.mk Complex.add_re Complex.smul_re) _
  have him : Convex ℝ {z : ℂ | 0<z.im} :=
    convex_halfSpace_gt (IsLinearMap.mk Complex.add_im Complex.smul_im) _
  exact IsPreconnected.union (1+Complex.I) (by simp) (by simp)
    hre.isPreconnected him.isPreconnected

theorem verify_upper_stieltjes_add_nonnegative {z : ℂ} (hz : z ∈ verifyUpperStieltjesDomain)
    {s : ℝ} (hs : 0≤s) : z + (s:ℂ) ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  rcases hz with h | h
  · left
    simpa only [Complex.add_re, Complex.ofReal_re] using add_pos_of_pos_of_nonneg h hs
  · right
    simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using (show z.im≠0 by linarith)

def verifyStieltjesIntegrand (z : ℂ) (s : ℝ) : ℂ := (z+(s:ℂ))⁻¹

def verifyComplexStieltjes (ν : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ s, verifyStieltjesIntegrand z s ∂ν

private theorem verify_stieltjes_local_denominator {z : ℂ} (hz : z∈verifyUpperStieltjesDomain) :
    ∃ ε > 0, ∀ w ∈ ball z ε, ∀ s : ℝ, 0≤s → ε ≤ ‖w+(s:ℂ)‖ := by
  rcases hz with hz | hz
  · refine ⟨z.re/2, by positivity, ?_⟩
    intro w hw s hs
    rw [mem_ball, dist_eq_norm] at hw
    have hre := (Complex.abs_re_le_norm (w-z)).trans_lt hw
    rw [Complex.sub_re] at hre
    have hp : z.re/2 ≤ (w+(s:ℂ)).re := by
      rw [Complex.add_re, Complex.ofReal_re]
      linarith [(abs_lt.mp hre).1]
    exact hp.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  · refine ⟨z.im/2, by positivity, ?_⟩
    intro w hw s _
    rw [mem_ball, dist_eq_norm] at hw
    have him := (Complex.abs_im_le_norm (w-z)).trans_lt hw
    rw [Complex.sub_im] at him
    have hp : z.im/2 ≤ (w+(s:ℂ)).im := by
      rw [Complex.add_im, Complex.ofReal_im, add_zero]
      linarith [(abs_lt.mp him).1]
    exact hp.trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))

private theorem verify_stieltjes_weight_control {z w : ℂ} {ε y s : ℝ}
    (hε : 0<ε) (hy : 0<y) (hs : 0≤s) (hw : w ∈ ball z ε)
    (hden : ε ≤ ‖w+(s:ℂ)‖) :
    ‖verifyStieltjesIntegrand w s‖ ≤ (1+(y+‖z‖+ε)/ε)*stieltjesWeight y s := by
  have hwz : ‖w-z‖<ε := by rwa [mem_ball,dist_eq_norm] at hw
  have hwt : ‖w‖ ≤ ‖z‖+ε := by
    have ht := norm_add_le (w-z) z
    rw [sub_add_cancel] at ht
    linarith
  have ht := norm_sub_le (w+(s:ℂ)) w
  rw [add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hs] at ht
  have hd : 0<‖w+(s:ℂ)‖ := hε.trans_le hden
  have hh : y+‖z‖+ε ≤ ((y+‖z‖+ε)/ε)*‖w+(s:ℂ)‖ := by
    calc
      _ = ((y+‖z‖+ε)/ε)*ε := (div_mul_cancel₀ _ hε.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)
  rw [verifyStieltjesIntegrand, norm_inv, stieltjesWeight, ← one_div,
    ← div_eq_mul_inv, div_le_div_iff₀ hd (by positivity)]
  nlinarith

theorem verify_complex_stieltjes_differentiableOn {ν : Measure ℝ} {y : ℝ} (hy : 0<y)
    (hs : ∀ᵐ s ∂ν, 0≤s) (hi : Integrable (stieltjesWeight y) ν) :
    DifferentiableOn ℂ (verifyComplexStieltjes ν) verifyUpperStieltjesDomain := by
  intro z hz
  obtain ⟨ε,hε,hden⟩ := verify_stieltjes_local_denominator hz
  let A := 1+(y+‖z‖+ε)/ε
  let F' : ℂ → ℝ → ℂ := fun w s => -((w+(s:ℂ))^2)⁻¹
  have hA : 0<A := by dsimp [A]; positivity
  have hn (w : ℂ) (hw : w∈ball z ε) (s : ℝ) (hs' : 0≤s) : w+(s:ℂ) ≠ 0 :=
    norm_ne_zero_iff.mp ((hε.trans_le (hden w hw s hs')).ne')
  have hmeas (w : ℂ) : Measurable (verifyStieltjesIntegrand w) := by
    unfold verifyStieltjesIntegrand
    exact (measurable_const.add Complex.continuous_ofReal.measurable).inv
  have hzi : Integrable (verifyStieltjesIntegrand z) ν := by
    apply (hi.const_mul A).mono' (hmeas z).aestronglyMeasurable
    filter_upwards [hs] with s hs'
    exact verify_stieltjes_weight_control hε hy hs' (mem_ball_self hε)
      (hden z (mem_ball_self hε) s hs')
  have hdmeas : Measurable (F' z) := by
    unfold F'
    exact (((measurable_const.add Complex.continuous_ofReal.measurable).pow_const 2).inv).neg
  have hb : Integrable (fun s => (A/ε)*stieltjesWeight y s) ν := hi.const_mul _
  have hdb : ∀ᵐ s ∂ν, ∀ w ∈ ball z ε, ‖F' w s‖ ≤ (A/ε)*stieltjesWeight y s := by
    filter_upwards [hs] with s hs' w hw
    have hl := verify_stieltjes_weight_control hε hy hs' hw (hden w hw s hs')
    change ‖verifyStieltjesIntegrand w s‖ ≤ A * stieltjesWeight y s at hl
    have hiε : ‖w+(s:ℂ)‖⁻¹ ≤ ε⁻¹ := inv_anti₀ hε (hden w hw s hs')
    have he : ‖F' w s‖ = ‖verifyStieltjesIntegrand w s‖*‖w+(s:ℂ)‖⁻¹ := by
      simp only [F', verifyStieltjesIntegrand, norm_neg, norm_inv, pow_two, mul_inv, norm_mul]
    rw [he, div_eq_mul_inv]
    exact (mul_le_mul hl hiε (by positivity)
      (mul_nonneg hA.le (stieltjesWeight_pos hy hs').le)).trans_eq (by ring)
  have hD : ∀ᵐ s ∂ν, ∀ w ∈ ball z ε,
      HasDerivAt (fun u : ℂ => verifyStieltjesIntegrand u s) (F' w s) w := by
    filter_upwards [hs] with s hs' w hw
    have h := ((hasDerivAt_id w).add_const (s:ℂ)).inv (hn w hw s hs')
    simpa only [verifyStieltjesIntegrand,F',id_eq,neg_div,one_div] using h
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := verifyStieltjesIntegrand) (F' := F') hε
    (Eventually.of_forall fun w => (hmeas w).aestronglyMeasurable)
    hzi hdmeas.aestronglyMeasurable hdb hb hD).2.differentiableAt.differentiableWithinAt

theorem verify_complex_stieltjes_analyticOnNhd {ν : Measure ℝ} {y : ℝ} (hy : 0<y)
    (hs : ∀ᵐ s ∂ν, 0≤s) (hi : Integrable (stieltjesWeight y) ν) :
    AnalyticOnNhd ℂ (verifyComplexStieltjes ν) verifyUpperStieltjesDomain :=
  (verify_complex_stieltjes_differentiableOn hy hs hi).analyticOnNhd verify_upper_stieltjes_open

theorem verify_complex_stieltjes_ofReal (ν : Measure ℝ) (x : ℝ) :
    verifyComplexStieltjes ν (x:ℂ) = (diagonalStieltjes ν x : ℂ) := by
  unfold verifyComplexStieltjes diagonalStieltjes verifyStieltjesIntegrand stieltjesWeight
  simp_rw [← Complex.ofReal_add, ← Complex.ofReal_inv, integral_complex_ofReal]

end UV.RevisionSpectrum
