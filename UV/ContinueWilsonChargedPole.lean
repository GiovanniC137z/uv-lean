import UV.ContinueWilsonRestRoots

/-! The complex time-spin endpoint, its positive energy poles, and the
coefficient of `1 / (M - z)` in the manuscript's spectral convention. -/

noncomputable section

open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology

namespace UV

def WilsonRestLaw.complexMoment {L : ℝ} (D : WilsonRestLaw L) (n : ℕ) (z : ℂ) : ℂ :=
  ∫ s, (s : ℂ)^n * Complex.exp (z*(s : ℂ)) ∂D.law

def WilsonRestLaw.complexBlock {L : ℝ} (D : WilsonRestLaw L) (σ : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  D.complexMoment n z + ((σ/(2*L) : ℝ) : ℂ) * D.complexMoment (n+1) z

theorem WilsonRestLaw.complex_moment_derivative {L : ℝ} (D : WilsonRestLaw L) (n : ℕ) (z : ℂ) :
    HasDerivAt (D.complexMoment n) (D.complexMoment (n+1) z) z :=
  hasDerivAt_integral_pow_mul_exp (D.exp_domain z.re) n

theorem WilsonRestLaw.complex_moment_real {L : ℝ} (D : WilsonRestLaw L) (n : ℕ) (x : ℝ) :
    D.complexMoment n (x : ℂ) = (D.moment n x : ℂ) := by
  unfold WilsonRestLaw.complexMoment WilsonRestLaw.moment
  rw [← integral_complex_ofReal]
  norm_cast

theorem WilsonRestLaw.complex_block_real {L : ℝ} (D : WilsonRestLaw L) (σ : ℝ) (n : ℕ) (x : ℝ) :
    D.complexBlock σ n (x : ℂ) = (D.block σ n x : ℂ) := by
  simp [WilsonRestLaw.complexBlock, D.complex_moment_real, D.block_moments]

theorem WilsonRestLaw.complex_block_derivative {L : ℝ} (D : WilsonRestLaw L) (σ : ℝ) (n : ℕ) (z : ℂ) :
    HasDerivAt (D.complexBlock σ n) (D.complexBlock σ (n+1) z) z :=
  (D.complex_moment_derivative n z).add ((D.complex_moment_derivative (n+1) z).const_mul _)

theorem WilsonRestLaw.complex_block_integral {L : ℝ} (D : WilsonRestLaw L) (σ : ℝ) (z : ℂ) :
    D.complexBlock σ 0 z = ∫ s, (wilsonTimeWeight L σ s : ℂ)*Complex.exp (z*(s:ℂ)) ∂D.law := by
  have hi (n : ℕ) : Integrable (fun s : ℝ => (s:ℂ)^n * Complex.exp (z*(s:ℂ))) D.law :=
    integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet (D.exp_domain z.re) n
  unfold WilsonRestLaw.complexBlock WilsonRestLaw.complexMoment
  rw [← integral_const_mul, ← integral_add (hi 0) ((hi 1).const_mul _)]
  congr 1
  funext s
  simp [wilsonTimeWeight]
  ring

def WilsonRestLaw.restDenominator {L : ℝ} (D : WilsonRestLaw L) (lam σ : ℝ) (z : ℂ) : ℂ :=
  1 - (lam:ℂ) * D.complexBlock σ 0 z

def WilsonRestLaw.restEndpoint {L : ℝ} (D : WilsonRestLaw L) (lam σ : ℝ) (z : ℂ) : ℂ :=
  ((σ*L : ℝ):ℂ) / D.restDenominator lam σ z

theorem WilsonRestLaw.rest_denominator_derivative {L : ℝ} (D : WilsonRestLaw L) (lam σ : ℝ) (z : ℂ) :
    HasDerivAt (D.restDenominator lam σ) (-((lam:ℂ) * D.complexBlock σ 1 z)) z := by
  simpa only [zero_sub] using (hasDerivAt_const z (1:ℂ)).sub ((D.complex_block_derivative σ 0 z).const_mul (lam:ℂ))

theorem WilsonRestLaw.rest_denominator_real_zero {L : ℝ} (D : WilsonRestLaw L) {lam : ℝ}
    (hlam : 0 < lam) (σ M : ℝ) : D.restDenominator lam σ (M : ℂ) = 0 ↔ D.block σ 0 M = lam⁻¹ := by
  rw [WilsonRestLaw.restDenominator, D.complex_block_real, ← Complex.ofReal_mul,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_eq_zero]
  constructor
  · intro h
    apply (mul_right_inj' hlam.ne').mp
    rw [mul_inv_cancel₀ hlam.ne']
    linarith
  · intro h
    rw [h, mul_inv_cancel₀ hlam.ne', sub_self]

theorem WilsonRestLaw.rest_weight_limit {L lam σ M : ℝ} (D : WilsonRestLaw L)
    (hlam : 0 < lam) (hM : D.block σ 0 M = lam⁻¹) (hd : 0 < D.block σ 1 M) :
    Tendsto (fun z : ℂ => ((M:ℂ)-z)*D.restEndpoint lam σ z) (𝓝[≠] (M:ℂ))
      (𝓝 ((σ*L/(lam*D.block σ 1 M) : ℝ):ℂ)) := by
  have hz := (D.rest_denominator_real_zero hlam σ M).mpr hM
  have h := D.rest_denominator_derivative lam σ (M:ℂ)
  rw [D.complex_block_real] at h
  have hd' : -((lam:ℂ)*(D.block σ 1 M:ℂ)) ≠ 0 := neg_ne_zero.mpr
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr hlam.ne') (Complex.ofReal_ne_zero.mpr hd.ne'))
  have hs := hasDerivAt_iff_tendsto_slope.mp h
  have ht := (tendsto_const_nhds (x := -((σ*L:ℝ):ℂ)) (f := 𝓝[≠] (M:ℂ))).div hs hd'
  have he : -((σ*L:ℝ):ℂ) / -((lam:ℂ)*(D.block σ 1 M:ℂ)) = ((σ*L/(lam*D.block σ 1 M):ℝ):ℂ) := by push_cast; ring
  rw [← he]
  apply ht.congr'
  filter_upwards with z
  change -((σ*L:ℝ):ℂ) / slope (D.restDenominator lam σ) (M:ℂ) z = _
  rw [slope_def_field,hz,sub_zero,div_div_eq_mul_div]
  unfold WilsonRestLaw.restEndpoint
  ring

/-- The two signs are spectral weights of the same charged endpoint.
The numerator is nonzero in either time-spin block. -/
theorem WilsonRestLaw.rest_poles_opposite_weights {L lam : ℝ} (D : WilsonRestLaw L)
    (hlam : 0 < lam) (hl : lam < 1) :
    ∃ Mplus Mminus Zplus Zminus : ℝ, 0 < Mplus ∧ Mplus < Mminus ∧ 0 < Zplus ∧ Zminus < 0 ∧
      (∀ x : ℝ, D.restDenominator lam 1 (x:ℂ) = 0 ↔ x = Mplus ∨ x = -Mminus) ∧
      (∀ x : ℝ, D.restDenominator lam (-1) (x:ℂ) = 0 ↔ x = Mminus ∨ x = -Mplus) ∧
      Tendsto (fun z : ℂ => ((Mplus:ℂ)-z)*D.restEndpoint lam 1 z) (𝓝[≠] (Mplus:ℂ)) (𝓝 (Zplus:ℂ)) ∧
      Tendsto (fun z : ℂ => ((Mminus:ℂ)-z)*D.restEndpoint lam (-1) z) (𝓝[≠] (Mminus:ℂ)) (𝓝 (Zminus:ℂ)) := by
  obtain ⟨p,q,hp,hpq,hpr,hqr,hpd,hqd⟩ := D.two_rest_masses hlam hl
  have hL := D.length_pos
  refine ⟨p,q,1*L/(lam*D.block 1 1 p),(-1)*L/(lam*D.block (-1) 1 q),hp,hpq,
    div_pos (by simpa only [one_mul] using hL) (mul_pos hlam hpd),
    div_neg_of_neg_of_pos (by linarith) (mul_pos hlam hqd),
    fun x => (D.rest_denominator_real_zero hlam 1 x).trans (hpr x),
    fun x => (D.rest_denominator_real_zero hlam (-1) x).trans (hqr x),
    D.rest_weight_limit hlam ((hpr p).mpr (Or.inl rfl)) hpd,
    D.rest_weight_limit hlam ((hqr q).mpr (Or.inl rfl)) hqd⟩

end UV
