import UV.ContinueEntireRootDivision
import UV.ContinueExponentialType

/-! An entire function of finite exponential type with a zero and a
finite common limit at the two imaginary ends has infinitely many zeros,
provided it is not identically zero. -/

noncomputable section

open Set Filter Complex
open scoped Topology

namespace UV

private theorem affine_exponential_cannot_decay (a b : ℂ)
    (ht : Tendsto (fun t : ℝ => Complex.exp (a*((t:ℂ)*Complex.I)+b)) (cocompact ℝ) (𝓝 0)) : False := by
  have hp := ht.mono_left atTop_le_cocompact
  have hm := ht.comp (tendsto_neg_atTop_atBot.mono_right atBot_le_cocompact)
  have he (t : ℝ) : Complex.exp (a*((t:ℂ)*Complex.I)+b) * Complex.exp (a*(((-t:ℝ):ℂ)*Complex.I)+b) = Complex.exp (b+b) := by
    rw [← Complex.exp_add,Complex.ofReal_neg]
    congr 1
    ring
  have hlim := (hp.mul hm).congr he
  rw [zero_mul] at hlim
  exact Complex.exp_ne_zero (b+b) (tendsto_nhds_unique tendsto_const_nhds hlim)

private theorem finite_zeros_exclude_two_sided_decay (s : Finset ℂ) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hn : ∃ z, f z ≠ 0)
    (hb : ∃ A B : ℝ, 0 ≤ B ∧ ∀ z, ‖f z‖ ≤ Real.exp (A+B*‖z‖))
    (hs : ∀ z, f z = 0 → z ∈ s)
    (ht : Tendsto (fun t : ℝ => f ((t:ℂ)*Complex.I)) (cocompact ℝ) (𝓝 0)) : False := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty =>
    obtain ⟨A,B,hB,hbound⟩ := hb
    have hnz (z : ℂ) : f z ≠ 0 := fun hz => Finset.notMem_empty z (hs z hz)
    obtain ⟨a,b,he⟩ := zero_free_exponential_type hf hnz hB hbound
    exact affine_exponential_cannot_decay a b (ht.congr (fun t => he _))
  | @insert a s ha ih =>
    by_cases hfa : f a = 0
    · obtain ⟨n,hnpos,g,hg,hga,he⟩ := entire_divide_isolated_zero hf hn hfa
      obtain ⟨A,B,hB,hbound⟩ := hb
      obtain ⟨C,hC⟩ := entire_quotient_growth hg he hB hbound
      apply ih hg ⟨a,hga⟩ ⟨C,B,hB,hC⟩ _ (entire_quotient_imaginary_decay hnpos he ht)
      intro z hz
      have hfz : f z = 0 := by rw [he,hz,mul_zero]
      exact (Finset.mem_insert.mp (hs z hfz)).resolve_left (fun h => hga (h ▸ hz))
    · apply ih hf hn hb _ ht
      intro z hz
      exact (Finset.mem_insert.mp (hs z hz)).resolve_left (fun h => hfa (h ▸ hz))

/-- Removing one zero forces two-sided decay of the quotient. Iterating
over any proposed finite zero set would leave a nonvanishing entire
exponential whose evaluations at opposite imaginary energies have a
constant nonzero product. -/
theorem exponential_type_infinite_zeros_of_frequency_limit {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hn : ∃ z, f z ≠ 0) (hz : ∃ z, f z = 0) {A B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ z, ‖f z‖ ≤ Real.exp (A+B*‖z‖)) {c : ℂ}
    (ht : Tendsto (fun t : ℝ => f ((t:ℂ)*Complex.I)) (cocompact ℝ) (𝓝 c)) :
    {z : ℂ | f z = 0}.Infinite := by
  classical
  intro hfin
  obtain ⟨a,ha⟩ := hz
  obtain ⟨n,hnpos,g,hg,hga,he⟩ := entire_divide_isolated_zero hf hn ha
  obtain ⟨C,hC⟩ := entire_quotient_growth hg he hB hb
  apply finite_zeros_exclude_two_sided_decay hfin.toFinset hg ⟨a,hga⟩ ⟨C,B,hB,hC⟩ _
    (entire_quotient_imaginary_decay hnpos he ht)
  intro z hz
  apply hfin.mem_toFinset.mpr
  change f z = 0
  rw [he,hz,mul_zero]

end UV
