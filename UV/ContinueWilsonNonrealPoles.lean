import UV.ContinueEntireFrequencyZeros
import UV.ContinueWilsonRestTransform

/-! Infinitely many genuine nonreal poles on each time-spin block, in
addition to the two real denominator zeros. -/

noncomputable section

open Set Filter MeasureTheory Complex
open scoped Topology

namespace UV

theorem WilsonRestLaw.rest_denominator_not_zero {L lam : ℝ} (D : WilsonRestLaw L)
    (hl : lam < 1) (σ : ℝ) : D.restDenominator lam σ 0 ≠ 0 := by
  have he := D.complex_block_real σ 0 0
  simp only [Complex.ofReal_zero,D.block_at_zero,Complex.ofReal_one] at he
  rw [WilsonRestLaw.restDenominator,he,mul_one,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.ofReal_ne_zero]
  linarith

/-- Each root produces unbounded norm on the punctured energy plane.
This includes roots of any finite multiplicity. -/
theorem WilsonRestLaw.endpoint_at_zero_unbounded {L lam σ : ℝ} (D : WilsonRestLaw L)
    (hl : lam < 1) (hσ : σ ≠ 0) {p : ℂ} (hz : D.restDenominator lam σ p = 0) :
    Tendsto (D.restEndpoint lam σ) (𝓝[≠] p) (Bornology.cobounded ℂ) := by
  let f := D.restDenominator lam σ
  have hf : Differentiable ℂ f := fun z => (D.rest_denominator_derivative lam σ z).differentiableAt
  have hA := hf.differentiableOn.analyticOnNhd (s := univ) isOpen_univ
  have hn := (hA p (mem_univ p)).eventually_eq_zero_or_eventually_ne_zero.resolve_left (fun he =>
    D.rest_denominator_not_zero hl σ (hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ p) he (mem_univ 0)))
  have hlim : Tendsto f (𝓝[≠] p) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hz ▸ (hf.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds),hn⟩
  have hc : ((σ*L:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mul_ne_zero hσ D.length_pos.ne')
  simpa only [WilsonRestLaw.restEndpoint,div_eq_mul_inv,Function.comp_def,f] using
    (tendsto_mul_left_cobounded hc).comp (tendsto_inv₀_nhdsWithin_ne_zero.comp hlim)

/-- The manuscript's signed time-spin endpoint has infinitely many distinct
nonreal, nonremovable poles for either spin. Absolute continuity supplies the
Fourier limit. The argument derives the finite-zero obstruction at this pin. -/
theorem WilsonRestLaw.infinitely_many_nonreal_poles {L lam σ : ℝ} (D : WilsonRestLaw L)
    (hlam : 0 < lam) (hl : lam < 1) (hσ : σ = 1 ∨ σ = -1) (hac : D.law ≪ volume) :
    {z : ℂ | z.im ≠ 0 ∧ D.restDenominator lam σ z = 0 ∧
      Tendsto (D.restEndpoint lam σ) (𝓝[≠] z) (Bornology.cobounded ℂ)}.Infinite := by
  have hs : |σ| ≤ 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hs0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hb : 1 < lam⁻¹ := (one_lt_inv₀ hlam).mpr hl
  obtain ⟨p,⟨_,hp⟩,_⟩ := D.positive_root_unique hs hb
  let f := D.restDenominator lam σ
  have hf : Differentiable ℂ f := fun z => (D.rest_denominator_derivative lam σ z).differentiableAt
  have hall := exponential_type_infinite_zeros_of_frequency_limit hf
    ⟨0,D.rest_denominator_not_zero hl σ⟩ ⟨(p:ℂ),(D.rest_denominator_real_zero hlam σ p).mpr hp⟩
    (show 0 ≤ 2*L from mul_nonneg (by norm_num) D.length_pos.le)
    (D.rest_denominator_growth lam hs) (D.rest_denominator_imaginary_limits lam σ hac)
  obtain ⟨P,Q,_,_,hP,hQ,_,_⟩ := D.two_rest_masses hlam hl
  let S : Set ℂ := {(P:ℂ),(Q:ℂ),(-P:ℂ),(-Q:ℂ)}
  have hfin : S.Finite := Set.toFinite _
  have hreal (z : ℂ) (hz : f z = 0) (hi : z.im = 0) : z ∈ S := by
    have he : (z.re:ℂ) = z := Complex.ext rfl (by simpa using hi.symm)
    have h := (D.rest_denominator_real_zero hlam σ z.re).mp (he.symm ▸ hz)
    rw [← he]
    rcases hσ with rfl | rfl
    · rcases (hP z.re).mp h with h | h <;> simp [S,h]
    · rcases (hQ z.re).mp h with h | h <;> simp [S,h]
  apply (hall.diff hfin).mono
  rintro z ⟨hz,hn⟩
  exact ⟨fun hi => hn (hreal z hz hi),hz,D.endpoint_at_zero_unbounded hl hs0 hz⟩

end UV
